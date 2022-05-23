/*******************************************************************\

Module: Verifier Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Verifier Interface

#include "goto_synthesizer_verifier.h"

#include <util/c_types.h>
#include <util/config.h>
#include <util/exit_codes.h>
#include <util/range.h>
#include <util/string_constant.h>
#include <util/unicode.h>
#include <util/version.h>

#include <ansi-c/cprover_library.h>
#include <cpp/cprover_library.h>
#include <langapi/language_util.h>

#include <fstream>
#include <iostream>
#include <memory>

#ifdef _MSC_VER
#endif

#include <goto-programs/goto_function.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/goto_trace.cpp>
#include <goto-programs/goto_trace.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>

#include <ansi-c/ansi_c_language.h>
#include <cbmc/cbmc_parse_options.h>
#include <cpp/cpp_language.h>
#include <goto-checker/all_properties_verifier.h>
#include <goto-checker/all_properties_verifier_with_fault_localization.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/bmc_util.h>
#include <goto-checker/cover_goals_verifier_with_trace_storage.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <goto-checker/multi_path_symex_only_checker.h>
#include <goto-checker/properties.h>
#include <goto-checker/report_util.cpp>
#include <goto-checker/single_loop_incremental_symex_checker.h>
#include <goto-checker/single_path_symex_checker.h>
#include <goto-checker/single_path_symex_only_checker.h>
#include <goto-checker/stop_on_fail_verifier.h>
#include <goto-checker/stop_on_fail_verifier_with_fault_localization.h>
#include <goto-instrument/contracts/contracts.h>
#include <goto-instrument/loop_utils.h>
#include <langapi/mode.h>

cext simple_verifiert::get_cex(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  const source_locationt &loop_entry_loc,
  cex_typet type)
{
  std::map<exprt, std::string> lhs_eval;
  std::map<std::string, std::string> object_sizes;
  std::map<std::string, std::string> pointer_offsets;
  std::map<std::string, std::string> loop_entry_eval;
  std::map<std::string, std::string> loop_entry_offsets;
  std::set<exprt> live_lhs;

  optionst options;
  trace_optionst trace_options(options);

  std::string next_object_size = "";
  bool have_seen_entry = false; // false if haven't touched the loop head
  bool after_entry =
    false; // true if have touched the first lone of the loop body

  // for tmp_post case, the checked pointer is the late seen alive variable
  exprt last_lhs;

  for(const auto &step : goto_trace.steps)
  {
    // stop record after the entry of the loop
    if(!step.pc->source_location().is_nil())
    {
      const auto &source_location = step.pc->source_location();
      if(
        source_location.get_file() == loop_entry_loc.get_file() &&
        source_location.get_function() == loop_entry_loc.get_function() &&
        source_location.get_line() == loop_entry_loc.get_line())
      {
        have_seen_entry = true;
      }
      else
      {
        if(have_seen_entry && !step.hidden)
          after_entry = true;
      }
    }

    switch(step.type)
    {
    case goto_trace_stept::typet::ASSERT:
      break;

    case goto_trace_stept::typet::DECL:
    case goto_trace_stept::typet::ASSIGNMENT:
    {
      irep_idt identifier;
      if(step.get_lhs_object().has_value())
        identifier = step.get_lhs_object()->get_identifier();

      if(step.full_lhs_value.is_nil())
        std::cout << "(assignment removed)";
      else
      {
        std::string lhs = from_expr(ns, identifier, step.full_lhs);
        std::string rhs = from_expr(ns, identifier, step.full_lhs_value);

        // make the rhs pure number
        if(
          rhs.length() > 2 && rhs.find("ul") == rhs.length() - 2 &&
          isdigit(rhs.at(rhs.length() - 3)))
          rhs = rhs.substr(0, rhs.length() - 2);
        if(
          rhs.length() > 1 && rhs.find("u") == rhs.length() - 1 &&
          isdigit(rhs.at(rhs.length() - 2)))
          rhs = rhs.substr(0, rhs.length() - 1);

        // update the alive varaibles
        // std::cout << lhs << " = " << rhs << " | " << after_entry << " | " << step.hidden << " @ " << step.pc->source_location().pretty() << "\n";
        if(
          step.pc->source_location().get_function() ==
            loop_entry_loc.get_function() &&
          !after_entry && !step.hidden &&
          (step.full_lhs.type().id() == ID_unsignedbv ||
           step.full_lhs.type().id() == ID_pointer) &&
          (lhs.find("(") == std::string::npos))
        {
          // for tmp_post
          last_lhs = step.full_lhs;
          if(lhs != "a" && lhs != "b" && lhs != "c")
            live_lhs.insert(step.full_lhs);
        }

        // if an existing object is assigned to a pointer
        if(rhs.find("dynamic_object") != std::string::npos)
        {
          // get the binary representation of object_id :: pointer_offset
          const irep_idt value =
            to_constant_expr(step.full_lhs_value).get_value();
          const typet &type = to_constant_expr(step.full_lhs_value).type();
          const auto width = to_pointer_type(type).get_width();
          mp_integer int_value = bvrep2integer(value, width, false);

          // mask out object id
          mp_integer mask = string2integer("72057594037927935");

          pointer_offsets[lhs] = integer2string(bitwise_and(mask, int_value));

          // get the object_size
          size_t left = rhs.find("dynamic_object") + 14;
          size_t right = left;
          while(rhs[right] != ' ')
          {
            right++;
          }
          object_sizes[lhs] = object_sizes[rhs.substr(left, right - left)];
        }

        // record the evaluation and the loop_entry value
        if(have_seen_entry && !after_entry)
        {
          lhs_eval[step.full_lhs] = rhs;
        }

        if(!have_seen_entry)
        {
          loop_entry_eval[lhs] = rhs;
          if(step.full_lhs.type().id() == ID_pointer)
          {
            loop_entry_offsets[lhs] = pointer_offsets[lhs];
          }
        }

        // needed when we check tmp_post
        if(!step.hidden)
        {
          last_lhs = step.full_lhs;
        }

        // store the object_size of dynamic_object by its index
        // Example:
        //    object_sizes[5] is the size of dynamic_object5
        if(
          rhs.find("dynamic_object") != std::string::npos &&
          next_object_size != "")
        {
          size_t left = rhs.find("dynamic_object") + 14;
          size_t right = left;
          while(rhs[right] != ' ')
          {
            right++;
          }
          object_sizes[rhs.substr(left, right - left)] = next_object_size;
          next_object_size = "";
        }
        if(lhs.find("malloc_size") != std::string::npos)
        {
          next_object_size = rhs;
        }
      }
      break;
    }

    case goto_trace_stept::typet::FUNCTION_CALL:
      break;

    case goto_trace_stept::typet::FUNCTION_RETURN:
      break;

    case goto_trace_stept::typet::ASSUME:
    case goto_trace_stept::typet::LOCATION:
    case goto_trace_stept::typet::GOTO:
    case goto_trace_stept::typet::OUTPUT:
    case goto_trace_stept::typet::INPUT:
    case goto_trace_stept::typet::SPAWN:
    case goto_trace_stept::typet::MEMORY_BARRIER:
    case goto_trace_stept::typet::ATOMIC_BEGIN:
    case goto_trace_stept::typet::ATOMIC_END:
    case goto_trace_stept::typet::DEAD:
    case goto_trace_stept::typet::CONSTRAINT:
    case goto_trace_stept::typet::SHARED_READ:
    case goto_trace_stept::typet::SHARED_WRITE:
      break;

    case goto_trace_stept::typet::NONE:
      UNREACHABLE;
    }
  }
  // for tmp_post
  if(live_lhs.find(checked_pointer) == live_lhs.end())
    checked_pointer = last_lhs;

  return cext(
    lhs_eval,
    object_sizes,
    pointer_offsets,
    loop_entry_eval,
    loop_entry_offsets,
    live_lhs,
    type);
}

exprt get_object(exprt range_predicate)
{
  return range_predicate.operands()[1].operands()[0];
}

exprt get_index(exprt range_predicate)
{
  return range_predicate.operands()[0].operands()[0];
}

exprt get_checked_pointer(exprt range_predicate)
{
  return range_predicate.operands()[0].operands()[0].operands()[0];
}

optionst get_options()
{
  optionst options;
  // Default true
  options.set_option("built-in-assertions", true);
  options.set_option("pretty-names", true);
  options.set_option("propagation", true);
  options.set_option("sat-preprocessor", true);
  options.set_option("simple-slice", true);
  options.set_option("simplify", true);
  options.set_option("simplify-if", true);
  options.set_option("show-goto-symex-steps", false);
  options.set_option("show-points-to-sets", false);
  options.set_option("show-array-constraints", false);
  options.set_option("assertions", true);
  options.set_option("assumptions", true);
  options.set_option("trace", true);
  //options.set_option("pointer-check", true);

  // Other default
  options.set_option("arrays-uf", "auto");
  options.set_option("depth", UINT32_MAX);
  // Options for process_goto_program
  options.set_option(
    "rewrite-union", true); // transform self loops to assumptions
  options.set_option("self-loops-to-assumptions", true);
  return options;
}

bool simple_verifiert::verify()
{
  null_message_handlert null_message_handler;
  ui_message_handlert ui_null_message_handler(null_message_handler);
  messaget null_log(ui_null_message_handler);

  // store the original functions
  // and then annoate the invariants
  goto_functionst::function_mapt &function_map =
    parse_option.goto_model.goto_functions.function_map;
  for(const auto &invariant_map_entry : parse_option.invariant_map)
  {
    irep_idt fun_name = invariant_map_entry.first.func_name;
    original_functions[fun_name].copy_from(function_map[fun_name].body);
    exprt guard =
      parse_option.get_loop_head(invariant_map_entry.first)->condition();
    goto_programt::targett loop_end =
      parse_option.get_loop_end(invariant_map_entry.first);
    exprt condition = loop_end->get_condition();
    condition.add(ID_C_spec_loop_invariant) =
      and_exprt(or_exprt(guard, invariant_map_entry.second), true_exprt());
    loop_end->set_condition(condition);
  }

  code_contractst cont(parse_option.goto_model, null_log);
  cont.apply_loop_contracts();

  optionst options = get_options();

  link_to_library(
    parse_option.goto_model, ui_message_handler, cprover_cpp_library_factory);
  link_to_library(
    parse_option.goto_model, ui_message_handler, cprover_c_library_factory);
  process_goto_program(parse_option.goto_model, options, null_log);
  remove_skip(parse_option.goto_model);
  label_properties(parse_option.goto_model);

  std::unique_ptr<
    all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>
    verifier = util_make_unique<
      all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
      options, ui_message_handler, parse_option.goto_model);

  const resultt result = (*verifier)();
  verifier->report();

  // restore the unnotated loops
  for(const auto &invariant_map_entry : parse_option.invariant_map)
  {
    irep_idt fun_name = invariant_map_entry.first.func_name;
    parse_option.goto_model.goto_functions.function_map[fun_name].body.swap(
      original_functions[fun_name]);
  }

  if(result != resultt::PASS)
  {
    const auto sorted_properties =
      get_sorted_properties(verifier->get_properties());
    const auto &property_it = sorted_properties.front();
    if(property_it->second.status == property_statust::FAIL)
    {
      cex_typet cex_type;
      if((property_it->second.description.find(
            "pointer outside object bounds") != std::string::npos))
      {
        //offset = get_index(property_it->second.pc->condition());
        offset = property_it->second.pc->condition();
        dereferenced_object = get_object(property_it->second.pc->condition());
        cex_type = cex_oob;
      }

      if(
        property_it->second.description.find("pointer NULL") !=
        std::string::npos)
      {
        cex_type = cex_null_pointer;
        checked_pointer =
          get_checked_pointer(property_it->second.pc->condition());
      }

      if(property_it->second.description.find("preserved") != std::string::npos)
      {
        cex_type = cex_not_preserved;
      }

      return_cex = get_cex(
        verifier->get_traces().get_namespace(),
        verifier->get_traces()[property_it->first],
        target_loop_head->source_location(),
        cex_type);
      return_cex.checked_pointer = checked_pointer;
      return_cex.dereferenced_object = dereferenced_object;
      return_cex.offset = offset;
      // std::cout << "failure type : " << (int)property_it->second.status << "\n";

      return false;
    }
  }

  return (result == resultt::PASS);
}

bool simple_verifiert::verify(const exprt &expr)
{
  std::cout << "Candidate :" << from_expr(expr) << "\n";

  null_message_handlert null_message_handler;
  ui_message_handlert ui_null_message_handler(null_message_handler);
  messaget null_log(ui_null_message_handler);

  original_program.copy_from(parse_option.goto_model.goto_functions
                               .function_map[parse_option.target_function_name]
                               .body);

  natural_loops_mutablet natural_loops(
    parse_option.goto_model.goto_functions
      .function_map[parse_option.target_function_name]
      .body);

  // Iterate over the (natural) loops in the function,
  // to find the target loop end
  exprt guard;
  for(const auto &loop : natural_loops.loop_map)
  {
    goto_programt::targett loop_end = loop.first;
    guard = loop_end->condition();
    for(const auto &t : loop.second)
    {
      if(
        t->is_goto() && t->get_target() == loop.first &&
        t->location_number > loop_end->location_number)
        loop_end = t;
    }
    target_loop_end = loop_end;
    target_loop_head = loop.first;
  }
  exprt condition = target_loop_end->get_condition();
  condition.add(ID_C_spec_loop_invariant) =
    and_exprt(true_exprt(), or_exprt(guard, expr));
  target_loop_end->set_condition(condition);

  // exprt invariant = static_cast<const exprt &>(target_loop_end->get_condition().find(ID_C_spec_loop_invariant));
  // std::cout<< from_expr(invariant) << "\n";

  code_contractst cont(parse_option.goto_model, null_log);
  cont.apply_loop_contracts();

  optionst options = get_options();

  link_to_library(
    parse_option.goto_model, ui_message_handler, cprover_cpp_library_factory);
  link_to_library(
    parse_option.goto_model, ui_message_handler, cprover_c_library_factory);
  process_goto_program(parse_option.goto_model, options, null_log);
  remove_skip(parse_option.goto_model);
  label_properties(parse_option.goto_model);

  //show_goto_functions(parse_option.goto_model, ui_message_handler, false);

  std::unique_ptr<
    all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>
    verifier = nullptr;
  //verifier = util_make_unique<
  //      all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
  //      options, ui_null_message_handler, parse_option.goto_model);

  verifier = util_make_unique<
    all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
    options, ui_message_handler, parse_option.goto_model);

  const resultt result = (*verifier)();

  verifier->report();

  parse_option.goto_model.goto_functions
    .function_map[parse_option.target_function_name]
    .body.swap(original_program);

  if(result != resultt::PASS)
  {
    const auto sorted_properties =
      get_sorted_properties(verifier->get_properties());
    for(const auto &property_it : sorted_properties)
    {
      if(property_it->second.status == property_statust::FAIL)
      {
        cex_typet cex_type;
        if((property_it->second.description.find(
              "pointer outside object bounds") != std::string::npos))
        {
          //offset = get_index(property_it->second.pc->condition());
          offset = property_it->second.pc->condition();
          dereferenced_object = get_object(property_it->second.pc->condition());
          cex_type = cex_oob;
        }

        if(
          property_it->second.description.find("pointer NULL") !=
          std::string::npos)
        {
          cex_type = cex_null_pointer;
          checked_pointer =
            get_checked_pointer(property_it->second.pc->condition());
        }

        if(
          property_it->second.description.find("preserved") !=
          std::string::npos)
        {
          cex_type = cex_not_preserved;
        }

        return_cex = get_cex(
          verifier->get_traces().get_namespace(),
          verifier->get_traces()[property_it->first],
          target_loop_head->source_location(),
          cex_type);
        return_cex.checked_pointer = checked_pointer;
        return_cex.dereferenced_object = dereferenced_object;
        return_cex.offset = offset;
        // std::cout << "failure type : " << (int)property_it->second.status << "\n";

        return false;
      }
    }
  }
  return (result == resultt::PASS);
}
/*******************************************************************\

Module: Verifier Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Verifier Interface

#include "goto_synthesizer_verifier.h"

#include <fstream>
#include <iostream>
#include <memory>

#include <util/config.h>
#include <util/version.h>
#include <util/exit_codes.h>
#include <util/c_types.h>
#include <util/range.h>
#include <util/string_constant.h>
#include <util/unicode.h>

#include <cpp/cprover_library.h>
#include <ansi-c/cprover_library.h>

#include <langapi/language_util.h>

#ifdef _MSC_VER
#endif

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
#include <goto-programs/goto_function.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/goto_trace.h>

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include <goto-instrument/loop_utils.h>
#include <goto-instrument/contracts/contracts.h>

#include <cbmc/cbmc_parse_options.h>

#include <goto-checker/all_properties_verifier.h>
#include <goto-checker/all_properties_verifier_with_fault_localization.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/bmc_util.h>
#include <goto-checker/cover_goals_verifier_with_trace_storage.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <goto-checker/multi_path_symex_only_checker.h>
#include <goto-checker/properties.h>
#include <goto-checker/single_loop_incremental_symex_checker.h>
#include <goto-checker/single_path_symex_checker.h>
#include <goto-checker/single_path_symex_only_checker.h>
#include <goto-checker/stop_on_fail_verifier.h>
#include <goto-checker/stop_on_fail_verifier_with_fault_localization.h>
#include <goto-checker/report_util.cpp>

cext::cext(const namespacet &ns, const goto_tracet &goto_trace, const source_locationt &loop_entry_loc)
{

  std::string next_object_size = "";
  bool have_seen_entry = false;
  for(const auto &step : goto_trace.steps)
  {        

    // stop record after the entry of the loop
    if(!step.pc->source_location().is_nil())
    {
      const auto &source_location = step.pc->source_location();
      if(source_location.get_file() == loop_entry_loc.get_file() 
          && source_location.get_function() == loop_entry_loc.get_function() 
          && source_location.get_line() == loop_entry_loc.get_line())
      {
        have_seen_entry = true;
      }
      else
      {
        if(have_seen_entry){
          continue;
        }
      }
    }

    // hide the hidden ones
    if(step.hidden)
      continue;

    switch(step.type)
    {
      case goto_trace_stept::typet::ASSERT:
        break;

      case goto_trace_stept::typet::DECL:
      case goto_trace_stept::typet::ASSIGNMENT:
      {
        irep_idt identifier;
        if(step.get_lhs_object().has_value())
          identifier=step.get_lhs_object()->get_identifier();

        if(step.full_lhs_value.is_nil())
          std::cout << "(assignment removed)";
        else
        {
          std::string lhs = from_expr(ns, identifier, step.full_lhs);
          std::string rhs = from_expr(ns, identifier, step.full_lhs_value);
          lhs_eval[step.full_lhs] =  rhs;

          if(step.pc->source_location().get_function() == loop_entry_loc.get_function() && step.type == goto_trace_stept::typet::DECL)
            live_lhs.insert(step.full_lhs);

          if(rhs.find("dynamic_object") != std::string::npos  && next_object_size != "")
          {
            object_size[rhs] = next_object_size;
            next_object_size = "";
          }

          if(lhs.find("malloc_size") != std::string::npos ){
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

  /*
  for(std::map<exprt, std::string>::const_iterator it = lhs_eval.begin(); it != lhs_eval.end(); ++it)
  {
    std::cout << it->first.get(ID_identifier) << " : " << it->second << " " << ";\n";
  }
    std::cout <<  ";\n";

  for(std::map<std::string, std::string>::const_iterator it = object_size.begin(); it != object_size.end(); ++it)
  {
    std::cout << it->first << " :: " << it->second << " " << ";\n";
  }  
  
    std::cout <<  ";\n";
  for(exprt expr : live_lhs)
  {
    std::cout << expr.get(ID_identifier) << ";\n";
  }
  */
}

exprt get_object(exprt range_predicate)
{
  return range_predicate.operands()[0].operands()[0].operands()[0].operands()[0];
}

exprt get_index(exprt range_predicate)
{
  return range_predicate.operands()[1].operands()[1];
}

bool simple_verifiert::verify(const exprt &expr)
{

  std::cout << "Candidate :" << from_expr(expr) << "\n";

  null_message_handlert null_message_handler;
  ui_message_handlert ui_null_message(null_message_handler);
  messaget null_log(ui_null_message);

  original_program.copy_from(parse_option.goto_model.goto_functions.function_map[parse_option.target_function_name].body);
  
  natural_loops_mutablet natural_loops(parse_option.goto_model.goto_functions.function_map[parse_option.target_function_name].body);

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
  condition.add(ID_C_spec_loop_invariant) = expr;// binary_exprt(unary_exprt(ID_not , guard), ID_or, expr);
  target_loop_end->set_condition(condition);

  // exprt invariant = static_cast<const exprt &>(target_loop_end->get_condition().find(ID_C_spec_loop_invariant));

  code_contractst cont(parse_option.goto_model, null_log);
  cont.apply_loop_contracts();

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

  link_to_library(
    parse_option.goto_model, ui_message_handler, cprover_cpp_library_factory);
  link_to_library(
    parse_option.goto_model, ui_message_handler, cprover_c_library_factory);
  process_goto_program(parse_option.goto_model,options,null_log);
  remove_skip(parse_option.goto_model);
  label_properties(parse_option.goto_model);


  //show_goto_functions(parse_option.goto_model, ui_message_handler, false);

  std::unique_ptr<
        all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>> verifier = nullptr;
  verifier = util_make_unique<
        all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
        options, ui_message_handler, parse_option.goto_model);
  
  const resultt result = (*verifier)();

  verifier->report();

  parse_option.goto_model.goto_functions.function_map[parse_option.target_function_name].body.swap(original_program);

  if (result != resultt::PASS)
  {
    const auto sorted_properties = get_sorted_properties(verifier->get_properties());
    for(const auto &property_it : sorted_properties)
    {
      if(property_it->second.status == property_statust::FAIL)
      {
        if((property_it->second.description.find("pointer outside object bounds") != std::string::npos))
        {
          offset = get_index(property_it->second.pc->condition());
          dereferenced_object = get_object(property_it->second.pc->condition());
        }
        // std::cout << property_it->second.pc->condition().pretty() << "\n";
        return_cex = cext(verifier->get_traces().get_namespace(), verifier->get_traces()[property_it->first], target_loop_head->source_location());
        return false;
      }
    }
  }

  return (result == resultt::PASS);
}
/*******************************************************************\

Module: Command Line Parsing

Author: Qinheping Hu, qinhh@amazon.com

\*******************************************************************/

/// \file
/// Command Line Parsing
#include "goto_synthesizer_parse_options.h"

#include <util/c_types.h>
#include <util/config.h>
#include <util/exit_codes.h>
#include <util/pointer_predicates.h>
#include <util/range.h>
#include <util/string_constant.h>
#include <util/unicode.h>
#include <util/version.h>

#include <analyses/dependence_graph.h>
#include <ansi-c/c_expr.h>
#include <langapi/language_util.h>

#include "goto_synthesizer_enumerator.h"
#include "goto_synthesizer_verifier.h"
#include "synthesizer_utils.h"

#ifdef _MSC_VER
#endif

#include <goto-programs/goto_function.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>

#include <ansi-c/ansi_c_language.h>
#include <cbmc/cbmc_parse_options.h>
#include <cpp/cpp_language.h>
#include <goto-instrument/contracts/contracts.h>
#include <goto-instrument/loop_utils.h>
#include <langapi/mode.h>

#include <fstream>
#include <iostream>
#include <memory>

// substitute all tmp_post variables with their origins in `expr`
void substitute_tmp_post_rec(
  exprt &dest,
  const goto_synthesizer_parse_optionst::expr_mapt &tmp_post_map)
{
  if(dest.id() != ID_address_of)
    Forall_operands(it, dest)
      substitute_tmp_post_rec(*it, tmp_post_map);

  // possibly substitute?
  if(dest.id() == ID_symbol && tmp_post_map.count(dest))
  {
    dest = tmp_post_map.at(dest);
  }
}

// extract symbol exprt from exprt
void extract_symbol_exprt_rec(const exprt &expr, std::set<exprt> &result)
{
  if(expr.id() == ID_object_size)
    return;

  if(expr.id() == ID_symbol)
  {
    result.insert(expr);
  }
  else
  {
    if((expr).has_operands())
    {
      for(exprt::operandst::const_iterator it = (expr).operands().begin();
          it != (expr).operands().end();
          ++it)
      {
        extract_symbol_exprt_rec(*it, result);
      }
    }
  }
  return;
}

void goto_synthesizer_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
}

std::set<exprt>
goto_synthesizer_parse_optionst::compute_flow_dependent_set_in_loop(
  const loop_idt &cause_loop_id,
  const std::set<exprt> &to)
{
  std::set<exprt> result = std::set<exprt>();

  goto_functiont &cause_function =
    goto_model.goto_functions.function_map[cause_loop_id.func_name];

  // construct a dummy predicate v1==v1 && ... && vn==vn
  // we later use it to compute flow dependent set of vi's
  exprt dummy_predicate = true_exprt();
  for(const auto &e : to)
  {
    dummy_predicate = and_exprt(dummy_predicate, equal_exprt(e, e));
  }

  // insert the dummy predicate into the goto program
  goto_programt generated_code;
  goto_convertt converter(goto_model.symbol_table, ui_message_handler);
  code_assertt assertion(dummy_predicate);
  converter.goto_convert(
    assertion,
    generated_code,
    goto_model.symbol_table.lookup_ref(cause_loop_id.func_name).mode);
  goto_programt::targett loop_end = get_loop_end(
    cause_loop_id.func_name,
    cause_loop_id.loop_number,
    goto_model.goto_functions.function_map);
  goto_programt::targett loop_head = get_loop_head(
    cause_loop_id.func_name,
    cause_loop_id.loop_number,
    goto_model.goto_functions.function_map);
  cause_function.body.instructions.insert(
    loop_end, generated_code.instructions.front());

  // build the dependence graph
  const namespacet ns(goto_model.symbol_table);
  dependence_grapht dependence_graph(ns);
  dependence_graph(goto_model);

  // BFS to search for flow dependent variables
  std::set<node_indext> visited = std::set<node_indext>();
  std::queue<goto_programt::const_targett> to_visit =
    std::queue<goto_programt::const_targett>();
  to_visit.push(std::prev(loop_end));
  while(!to_visit.empty())
  {
    goto_programt::const_targett current_target = to_visit.front();
    to_visit.pop();
    const dep_graph_domaint current_domain = dependence_graph[current_target];

    // `current_domain` is control dependent on what varaibles?
    for(const auto node : current_domain.get_control_deps())
    {
      if(
        visited.count(dependence_graph[node].get_node_id()) ||
        node->location_number < loop_head->location_number ||
        node->location_number > loop_end->location_number)
        continue;

      visited.insert(dependence_graph[node].get_node_id());
      to_visit.push(node);

      // add a variable to result if it is in the guard
      std::set<exprt> extracted_vars = std::set<exprt>();
      extract_symbol_exprt_rec(node->guard, extracted_vars);
      result.insert(extracted_vars.begin(), extracted_vars.end());
    }

    // `current_domain` is data dependent on what varaibles?
    for(const auto node : current_domain.get_data_deps())
    {
      if(
        visited.count(dependence_graph[node].get_node_id()) ||
        node->location_number < loop_head->location_number ||
        node->location_number > loop_end->location_number)
        continue;

      visited.insert(dependence_graph[node].get_node_id());
      to_visit.push(node);

      // add a variable to result if it is lhs of assignment
      if(node->type() == goto_program_instruction_typet::ASSIGN)
      {
        result.insert(node->assign_lhs());
      }
    }
  }

  // remove the added dummy predicate
  cause_function.body.instructions.erase(std::prev(loop_end));

  return result;
}

std::set<exprt> goto_synthesizer_parse_optionst::compute_requried_variables(
  const loop_idt &cause_loop_id,
  exprt &new_clause)
{
  // initialize result as Vars(new_clause)
  std::set<exprt> required_set = std::set<exprt>();
  extract_symbol_exprt_rec(new_clause, required_set);

  // construct Vars(candidate)
  std::set<exprt> vars_prev_candidate = std::set<exprt>();
  exprt prev_candidate = invariant_map[cause_loop_id];
  extract_symbol_exprt_rec(prev_candidate, vars_prev_candidate);

  size_t old_number_of_required_variables = 0;
  while(old_number_of_required_variables != required_set.size())
  {
    old_number_of_required_variables = required_set.size();
    std::set<exprt> dependent_set =
      compute_flow_dependent_set_in_loop(cause_loop_id, required_set);

    required_set.insert(dependent_set.begin(), dependent_set.end());

    std::set<exprt> antidependent_set =
      compute_flow_dependent_set_in_loop(cause_loop_id, vars_prev_candidate);
    std::set<exprt> intersect;
    set_intersection(
      antidependent_set.begin(),
      antidependent_set.end(),
      required_set.begin(),
      required_set.end(),
      std::inserter(intersect, intersect.begin()));
  }

  return required_set;
}

exprt goto_synthesizer_parse_optionst::synthesize_range_predicate_simple(
  const exprt &violated_predicate)
{
  return violated_predicate;
}

exprt goto_synthesizer_parse_optionst::synthesize_same_object_predicate_simple(
  const exprt &checked_pointer)
{
  return same_object(
    checked_pointer, unary_exprt(ID_loop_entry, checked_pointer));
}

void goto_synthesizer_parse_optionst::synthesize_loop_invariants(
  const irep_idt &function_name,
  goto_functionst::goto_functiont &goto_function,
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  PRECONDITION(!loop.empty());

  target_function_name = function_name;

  exprt current_candidate = true_exprt();
  exprt one = from_integer(1, size_type());
  exprt zero = from_integer(0, size_type());
  //terminal_symbols.push_back(one);

  while(true)
  {
    simple_verifiert v(*this, this->ui_message_handler);
    if(v.verify(current_candidate))
    {
      log.result() << "result : " << log.green << "PASS" << messaget::eom
                   << log.reset;
      return;
    }
    else
    {
      log.result() << "result : " << log.red << "FAIL" << messaget::eom
                   << log.reset;
    }

    if(terminal_symbols.empty())
    {
      log.result() << "start to construct \n";
      for(exprt lhs : v.return_cex.live_lhs)
      {
        std::cout << "live1 : " << from_expr(lhs) << "\n";
        if(lhs.type().id() == ID_unsignedbv)
        {
          terminal_symbols.push_back(lhs);
          terminal_symbols.push_back(
            unary_exprt(ID_loop_entry, lhs, size_type()));
          //idx_type = lhs.type();
        }
        if((lhs.type().id() == ID_pointer))
        {
          // terminal_symbols.push_back(unary_exprt(ID_object_size, lhs, size_type()));
          terminal_symbols.push_back(
            unary_exprt(ID_pointer_offset, lhs, size_type()));
          terminal_symbols.push_back(unary_exprt(
            ID_pointer_offset,
            unary_exprt(ID_loop_entry, lhs, lhs.type()),
            size_type()));
          if(lhs.type().subtype().id() == ID_unsignedbv)
          {
            //TODO terminal_symbols.push_back(dereference_exprt(lhs));
          }
        }
      }
    }

    if(v.return_cex.cex_type == cext::cex_typet::cex_null_pointer)
    {
      exprt original_checked_pointer = v.checked_pointer_deprecated;
      current_candidate = and_exprt(
        current_candidate,
        same_object(
          original_checked_pointer,
          unary_exprt(ID_loop_entry, original_checked_pointer)));
    }
    else if(deductive && v.return_cex.cex_type == cext::cex_typet::cex_oob)
    {
      exprt offset = v.offset_deprecated;
      exprt deref_object = v.dereferenced_object_deprecated;

      // TODO: modify this!
      exprt four = from_integer(0, size_type());

      //current_candidate = and_exprt(current_candidate, and_exprt(less_than_or_equal_exprt(zero, offset), less_than_or_equal_exprt(offset, deref_object)));
      current_candidate = and_exprt(current_candidate, offset);
    }
    else
    {
      simple_enumeratort enumerator(
        *this, current_candidate, v.return_cex, ui_message_handler);
      if(enumerator.enumerate())
        break;
    }
  }
}

void goto_synthesizer_parse_optionst::preprocess(
  const irep_idt &function_name,
  goto_functionst::goto_functiont &goto_function)
{
  natural_loops_mutablet natural_loops(goto_function.body);

  // build the map from tmp_post to their original variables
  for(const auto &instruction : goto_function.body.instructions)
  {
    if(instruction.type() == goto_program_instruction_typet::ASSIGN)
    {
      if(
        instruction.assign_lhs().id() == ID_symbol &&
        from_expr(instruction.assign_lhs()).find("tmp_post") !=
          std::string::npos)
      {
        tmp_post_map[instruction.assign_lhs()] = instruction.assign_rhs();
      }
    }
  }

  size_t loop_number = 0;
  // first candidatge invairant for unannotated loop is true
  while(loop_number < natural_loops.loop_map.size())
  {
    loop_idt new_id = {.func_name = function_name, .loop_number = loop_number};
    goto_programt::targett loop_end = get_loop_end(
      new_id.func_name,
      new_id.loop_number,
      goto_model.goto_functions.function_map);
    if(loop_end->get_condition().find(ID_C_spec_loop_invariant).is_nil())
    {
      invariant_map[new_id] = true_exprt();
      post_invariant_map[new_id] = true_exprt();
    }
    loop_number++;
  }
}

void goto_synthesizer_parse_optionst::synthesize_loop_invariants(
  goto_functionst &goto_functions)
{
  for(auto &goto_function : goto_functions.function_map)
  {
    preprocess(goto_function.first, goto_function.second);
  }

  cext prev_cex;

  while(true)
  {
    simple_verifiert v(*this, this->ui_message_handler);

    // verify the current invariants_map
    if(v.verify())
    {
      log.result() << "result : " << log.green << "PASS" << messaget::eom
                   << log.reset;
      return;
    }
    else
    {
      log.result() << "result : " << log.red << "FAIL" << messaget::eom
                   << log.reset;
    }

    exprt new_clause = true_exprt();
    simple_enumeratort enumerator(
      *this, true_exprt(), v.return_cex, ui_message_handler);
    // synthsize the new_clause
    switch(v.return_cex.cex_type)
    {
    case cext::cex_typet::cex_null_pointer:
      new_clause =
        synthesize_same_object_predicate_simple(v.return_cex.checked_pointer);
      break;

    case cext::cex_typet::cex_oob:
      new_clause =
        synthesize_range_predicate_simple(v.return_cex.violated_predicate);
      break;

    case cext::cex_typet::cex_not_preserved:
      enumerator.enumerate();
      break;

    case cext::cex_typet::cex_ERROR:
      INVARIANT(false, "unsupported violation type");
      break;
    }
    INVARIANT(
      new_clause != true_exprt(), "failed to synthesized meaningful clause");

    // take care of tmp_post
    substitute_tmp_post_rec(new_clause, tmp_post_map);

    // store the previous cex
    prev_cex = v.return_cex;
    prev_cex.cause_loop_id.func_name = v.return_cex.cause_loop_id.func_name;
    prev_cex.cause_loop_id.loop_number = v.return_cex.cause_loop_id.loop_number;

    compute_requried_variables(prev_cex.cause_loop_id, new_clause);

    // add the new cluase to the candidate invairants
    if(v.return_cex.is_violation_in_loop)
      invariant_map[prev_cex.cause_loop_id] =
        and_exprt(invariant_map[prev_cex.cause_loop_id], new_clause);
    else
      post_invariant_map[prev_cex.cause_loop_id] =
        and_exprt(post_invariant_map[prev_cex.cause_loop_id], new_clause);
  }
}

/// invoke main modules
int goto_synthesizer_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.args.size() != 1 && cmdline.args.size() != 2 &&
    cmdline.args.size() != 3)
  {
    help();
    return CPROVER_EXIT_USAGE_ERROR;
  }

  messaget::eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);

  {
    register_languages();

    get_goto_program();

    {
      const bool validate_only = cmdline.isset("validate-goto-binary");

      if(validate_only || cmdline.isset("validate-goto-model"))
      {
        goto_model.validate(validation_modet::EXCEPTION);

        if(validate_only)
        {
          return CPROVER_EXIT_SUCCESS;
        }
      }
      log.status() << "Model is valid" << messaget::eom;
    }

    if(cmdline.isset("deductive"))
      deductive = true;

    if(cmdline.isset("hybrid"))
      hybrid = true;

    synthesize_loop_invariants(goto_model.goto_functions);
    return CPROVER_EXIT_SUCCESS;
  }

  help();
  return CPROVER_EXIT_USAGE_ERROR;
}

void goto_synthesizer_parse_optionst::get_goto_program()
{
  log.status() << "Reading GOTO program from '" << cmdline.args[0] << "'"
               << messaget::eom;

  config.set(cmdline);

  auto result = read_goto_binary(cmdline.args[0], ui_message_handler);

  if(!result.has_value())
    throw 0;

  goto_model = std::move(result.value());

  config.set_from_symbol_table(goto_model.symbol_table);
}

/// display command line help
void goto_synthesizer_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("InvSynthesizer", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2008-2013") << '\n'
            << align_center_with_border("Qinheping Hu") << '\n'
            << align_center_with_border("qinhh@amazon.com") << '\n'
            <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " goto-synthesizer [-?] [-h] [--help]  show help\n"
    " goto-synthesizer in out              perform synthesizing\n"
    "\n"
    "Main options:\n"
    "\n"
    "Other options:\n"
    " --no-system-headers          with --dump-c/--dump-cpp: generate C source expanding libc includes\n" // NOLINT(*)
    " --use-all-headers            with --dump-c/--dump-cpp: generate C source with all includes\n" // NOLINT(*)
    " --harness                    with --dump-c/--dump-cpp: include input generator in output\n" // NOLINT(*)
    " --version                    show version and exit\n"
    HELP_FLUSH
    " --xml-ui                     use XML-formatted output\n"
    " --json-ui                    use JSON-formatted output\n"
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}

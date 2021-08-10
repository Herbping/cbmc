/*******************************************************************\

Module: Main Module

Author: Qinheping Hu, qinhh@amazon.com

\*******************************************************************/

/// \file
/// Main Module

#include "goto_synthesizer_parse_options.h"

#include <fstream>
#include <iostream>
#include <memory>

#include <analyses/local_may_alias.h>

#include <util/config.h>
#include <util/version.h>
#include <util/exit_codes.h>
#include <util/c_types.h>
#include <util/range.h>
#include <util/string_constant.h>

#include <langapi/language_util.h>

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif


#include <goto-programs/add_malloc_may_fail_variable_initializations.h>
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

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include <goto-instrument/loop_utils.h>
#include <goto-instrument/code_contracts.h>

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



void goto_synthesizer_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
}

exprt goto_synthesizer_parse_optionst::copy_exprt(const exprt &expr)
{
  exprt result(expr.id(), expr.type());
  for(const auto &operand : expr.operands())
  {
    result.add_to_operands(operand);
  }
  return result;
}

void goto_synthesizer_parse_optionst::paste_original_instructions(goto_functiont & goto_function)
{
  while(!goto_function.body.instructions.empty())
  {
    goto_function.body.instructions.pop_front();
  }
  for(goto_programt::instructionst::iterator it=(goto_function.body).instructions.begin(); \
    it!=(goto_function.body).instructions.end(); it++)
    {
      goto_programt::instructiont &i=*it;
      i.turn_into_skip();
      i.target_number = 0;
    }
  for(goto_programt::instructionst::iterator it=original_instructions.begin(); \
    it!=original_instructions.end(); it++)
    {
      goto_programt::instructiont &i=*it;
      goto_function.body.instructions.push_back(i);
    }
    original_instructions.clear();
}

void goto_synthesizer_parse_optionst::copy_original_instructions(goto_functiont & goto_function)
{
  int idx = 0;
  std::vector<std::pair<int, int>> edges;
  for(goto_programt::instructionst::iterator it=(goto_function.body).instructions.begin(); 
    it!=(goto_function.body).instructions.end(); it++)
  {
    goto_programt::instructiont &i=*it;
    goto_programt::instructiont c(i.get_code(),i.source_location,i.type,i.guard,i.targets);
    if(i.is_goto())
    {
      int jdx = 0;
      for(goto_programt::instructionst::iterator jt=(goto_function.body).instructions.begin(); 
        jt!=(goto_function.body).instructions.end(); jt++)
      {
        goto_programt::instructiont &j=*jt;
        if(i.targets.front()->equals(j))
          break;
        jdx++;
      }
      std::pair<int, int> edge{idx,jdx};
      edges.push_back(edge);
    }
    c.target_number = i.target_number;
    c.location_number = i.location_number;
    log.status() << i.incoming_edges.size() << messaget::eom;
    original_instructions.push_back(c);
    idx++;
    }
  for(auto &edge : edges)
  {
    int from = edge.first;
    int to = edge.second;
    std::list<goto_programt::instructiont>::iterator it = original_instructions.begin();
    std::advance(it, from);

    std::list<goto_programt::instructiont>::iterator jt = original_instructions.begin();
    std::advance(jt, to);

    it->set_target(jt);
  }
}

bool goto_synthesizer_parse_optionst::simple_verification(const exprt &expr)
{
  original_program.copy_from(goto_model.goto_functions.function_map[target_function_name].body);
     show_goto_functions(
      goto_model, ui_message_handler, cmdline.isset("list-goto-functions"));
  
  /*
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(gf_entry.first == target_function_name)
      copy_original_instructions(gf_entry.second);
  }

  for(auto &i : original_instructions)
  {
    log.status() << i.to_string() << messaget::eom;
    log.status() << i.incoming_edges.size() << messaget::eom;
  }
  */


  local_may_aliast local_may_alias(goto_model.goto_functions.function_map[target_function_name]);
  natural_loops_mutablet natural_loops(goto_model.goto_functions.function_map[target_function_name].body);

  // Iterate over the (natural) loops in the function,
  // and syntehsize loop invaraints.
  for(const auto &loop : natural_loops.loop_map)
  {
    goto_programt::targett loop_end = loop.first;

  log.status() << "loop_end" << loop_end->to_string()  << messaget::eom;
    for(const auto &t : loop.second)
    {
  log.status() << "loop_end" << loop_end->to_string()  << messaget::eom;
      
      if(
        t->is_goto() && t->get_target() == loop.first &&
        t->location_number > loop_end->location_number)
        loop_end = t;
    }

    target_loop_end = loop_end;
  }


  log.status() << "HERE?" << messaget::eom;
  log.status() << target_loop_end->to_string() << messaget::eom;
  exprt condition = target_loop_end->get_condition();
  log.status() << "HERE!" << messaget::eom;
  condition.add(ID_C_spec_loop_invariant) = expr;
  target_loop_end->set_condition(condition);

  exprt invariant = static_cast<const exprt &>(
    target_loop_end->get_condition().find(ID_C_spec_loop_invariant));
  log.status() << "Candidate :" << from_expr(invariant) << messaget::eom;


     show_goto_functions(
      goto_model, ui_message_handler, cmdline.isset("list-goto-functions"));

  code_contractst cont(goto_model, log);
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

  // Other default
  options.set_option("arrays-uf", "auto");

  process_goto_program(goto_model,options,log);


  label_properties(goto_model);

     show_goto_functions(
      goto_model, ui_message_handler, cmdline.isset("list-goto-functions"));


  std::unique_ptr<goto_verifiert> verifier = nullptr;
  verifier = util_make_unique<
        all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
        options, ui_message_handler, goto_model);
  
  const resultt result = (*verifier)();

  verifier->report();
  log.status() << "result : " << as_string(result) << messaget::eom;

/*
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(gf_entry.first == target_function_name)
      paste_original_instructions(gf_entry.second);
  }
*/
  goto_model.goto_functions.function_map[target_function_name].body.swap(original_program);
  return (result == resultt::PASS);
}

bool goto_synthesizer_parse_optionst::call_back(const exprt &expr)
{
  return true;
}

exprt goto_synthesizer_parse_optionst::eterm(int size)
{
  if(size == 1)
  {
    return nonterminal_E;
  }

  return plus_exprt(nonterminal_E, eterm(size-1));
}

exprt goto_synthesizer_parse_optionst::sterm(const irep_idt &id, int size)
{
  return binary_relation_exprt(eterm(size), id, eterm(size));
}

bool goto_synthesizer_parse_optionst::contain_E(const exprt &expr)
{
  if(expr == nonterminal_E)
  {
    return true;
  }

  for(const auto &operand : expr.operands()){
    if(contain_E(operand))
      return true;
  } 
  return false;
}

bool goto_synthesizer_parse_optionst::is_partial(const exprt &expr)
{
  if(expr == nonterminal_S || expr == nonterminal_E)
  {
    return true;
  }

  for(const auto &operand : expr.operands()){
    if(is_partial(operand))
      return true;
  } 
  return false;
}

bool goto_synthesizer_parse_optionst::expand_with_symbol(exprt &expr, const exprt &symbol)
{
  if(expr == nonterminal_E)
  {
    expr = symbol;
    return true;
  }
  for(auto &operand : expr.operands())
  {
    if(expand_with_symbol(operand, symbol))
    {
      return true;
    }
  }
  return false;
}

std::queue<exprt> goto_synthesizer_parse_optionst::expand_with_terminals(std::queue<exprt> &exprs)
{
  std::queue<exprt> result;

  while(!exprs.empty())
  {
    exprt current_expr = exprs.front();

    if(contain_E(current_expr))
    {
      for(const auto &symbol : terminal_symbols)
      {
        exprt new_expr = copy_exprt(current_expr);
        expand_with_symbol(new_expr, symbol);
        exprs.push(new_expr);
      }
    }
    else
    {
      result.push(current_expr);
    }

    exprs.pop();
  }
  return result;
}

bool goto_synthesizer_parse_optionst::simple_enumeration()
{
  std::deque<exprt> current_partial_terms;

  // number of clauses in the invariant
  // depth of each clause
  int num_clauses = 0;
  int size_eterm = 0; 

  // limit the search depth?
  while(true)  
  {
    num_clauses++;
    if(num_clauses % 2 == 1)
      size_eterm++;

    for(int i = 0; i <= num_clauses; i++)
    {
      exprt skeleton = true_exprt();
      for(int j = 0; j < num_clauses; j++)
      {
        if(i > j)
        {
          skeleton = and_exprt(skeleton, sterm(ID_equal, size_eterm));
        }
        else
        {
          skeleton = and_exprt(skeleton, sterm(ID_le, size_eterm));
        }
      }
      current_partial_terms.push_back(skeleton);
    }

    while(!current_partial_terms.empty())
    {
      exprt partial_term = current_partial_terms.front();
      current_partial_terms.pop_front();

      std::queue<exprt> to_add;
      if(contain_E(partial_term))
      {
        to_add.push(partial_term);
        to_add = expand_with_terminals(to_add);
        while(!to_add.empty())
        {
          current_partial_terms.push_front(to_add.front());
          to_add.pop();
        }
      }
      else
      {
        if(!is_partial(partial_term))
        {
          if(simple_verification(partial_term))
          {
            return true;
          }
        }
      }

    }
  }
}

void goto_synthesizer_parse_optionst::extract_exprt(const exprt &expr)
{
  if(expr.operands().size() != 0)
  {
    for(const auto &operand : expr.operands())
    {
      extract_exprt(operand);
    }
  }
  else
  {
    for(const auto &symbol : terminal_symbols)
    {
      if(expr == symbol)
        return;
    }
    terminal_symbols.push_back(expr);
  }
}

void goto_synthesizer_parse_optionst::synthesize_loop_contracts(
  const irep_idt &function_name,
  goto_functionst::goto_functiont &goto_function,
  const goto_programt::targett loop_head,
  const loopt &loop
)
{
  PRECONDITION(!loop.empty());

  target_function_name = function_name;

  // find the last back edge
  goto_programt::targett loop_end = loop_head;
  for(const auto &t : loop)
  {
    if(
      t->is_goto() && t->get_target() == loop_head &&
      t->location_number > loop_end->location_number)
      loop_end = t;

    if(t->is_assign())
    {
      extract_exprt(t->assign_lhs());
      extract_exprt(t->assign_rhs());
    }
  }

  target_loop_end = loop_end;

  // add the constant 0 to terminal_symbols
  exprt zero = constant_exprt(irep_idt(dstringt("0")), terminal_symbols[0].type());
  terminal_symbols.push_back(zero);

  nonterminal_S = copy_exprt(nonterminal_S);
  nonterminal_E = copy_exprt(nonterminal_E);
  simple_enumeration();

  // see whether we have an invariant and a decreases clause
  /*
  exprt invariant = static_cast<const exprt &>(
    loop_end->get_condition().find(ID_C_spec_loop_invariant));
  exprt decreases_clause = static_cast<const exprt &>(
    loop_end->get_condition().find(ID_C_spec_decreases));
  log.status() << from_expr(loop_end->get_condition()) << messaget::eom;
  log.status() << from_expr(invariant) << messaget::eom;
  invariant = conjunction(invariant.operands());
  log.status() << from_expr(invariant) << messaget::eom;
  */

}

void goto_synthesizer_parse_optionst::synthesize_loop_contracts(
  const irep_idt &function_name,
  goto_functionst::goto_functiont &goto_function)
{
  local_may_aliast local_may_alias(goto_function);
  natural_loops_mutablet natural_loops(goto_function.body);

  // Iterate over the (natural) loops in the function,
  // and syntehsize loop invaraints.
  for(const auto &loop : natural_loops.loop_map)
  {
    synthesize_loop_contracts(
      function_name,
      goto_function,
      loop.first,
      loop.second);
  }
}

void goto_synthesizer_parse_optionst::synthesize_loop_contracts(goto_functionst &goto_functions)
{
  for(auto &goto_function : goto_functions.function_map){
    synthesize_loop_contracts(goto_function.first, goto_function.second);
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

  if(cmdline.args.size()!=1 && cmdline.args.size()!=2)
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

    symbol_table = goto_model.symbol_table;

    synthesize_loop_contracts(goto_model.goto_functions);
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
  std::cout << '\n' << banner_string("Goto-Synthesizer", CBMC_VERSION) << '\n'
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

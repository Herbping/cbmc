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

#include <langapi/language_util.h>

#ifdef _MSC_VER
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


bool simple_verifiert::verify(const exprt &expr)
{
  null_message_handlert null_message_handler;
  ui_message_handlert ui_null_message(null_message_handler);
  messaget null_log(ui_null_message);

  original_program.copy_from(parse_option.goto_model.goto_functions.function_map[parse_option.target_function_name].body);
  

  natural_loops_mutablet natural_loops(parse_option.goto_model.goto_functions.function_map[parse_option.target_function_name].body);

  // Iterate over the (natural) loops in the function,
  // and syntehsize loop invaraints.
  for(const auto &loop : natural_loops.loop_map)
  {
    goto_programt::targett loop_end = loop.first;

    for(const auto &t : loop.second)
    {
      
      if(
        t->is_goto() && t->get_target() == loop.first &&
        t->location_number > loop_end->location_number)
        loop_end = t;
    }

    target_loop_end = loop_end;
  }


  exprt condition = target_loop_end->get_condition();
  condition.add(ID_C_spec_loop_invariant) = expr;
  target_loop_end->set_condition(condition);

  exprt invariant = static_cast<const exprt &>(
    target_loop_end->get_condition().find(ID_C_spec_loop_invariant));


    
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

  // Other default
  options.set_option("arrays-uf", "auto");

  process_goto_program(parse_option.goto_model,options,null_log);


  label_properties(parse_option.goto_model);

  std::unique_ptr<goto_verifiert> verifier = nullptr;
  verifier = util_make_unique<
        all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
        options, ui_null_message, parse_option.goto_model);
  
  const resultt result = (*verifier)();

  parse_option.goto_model.goto_functions.function_map[parse_option.target_function_name].body.swap(original_program);
  return (result == resultt::PASS);
}
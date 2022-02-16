/*******************************************************************\

Module: Command Line Parsing

Author: Qinheping Hu, qinhh@amazon.com

\*******************************************************************/

/// \file
/// Command Line Parsing
#include "goto_synthesizer_parse_options.h"
#include "goto_synthesizer_enumerator.h"
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


#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/goto_function.h>
#include <goto-programs/goto_program.h>

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include <goto-instrument/loop_utils.h>
#include <goto-instrument/contracts/contracts.h>

#include <cbmc/cbmc_parse_options.h>

void goto_synthesizer_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
}

bool goto_synthesizer_parse_optionst::call_back(const exprt &expr)
{
  simple_verifiert v(*this);
  log.status() << "Candidate :" << from_expr(expr) << messaget::eom;
  if(v.verify(expr))
  {
    log.result() << "result : " << log.green << "PASS" << messaget::eom << log.reset;

    return true;
  }
  else
  {
    log.result() << "result : " << log.red << "FAIL" << messaget::eom << log.reset;

    return false;
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
    log.status() << from_expr(expr) << messaget::eom;
    log.status() << expr.type().pretty() << messaget::eom;
    if(expr.type() == bitvector_typet(ID_signedbv,32) || expr.type() == bitvector_typet(ID_unsignedbv,32))
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

    if(t->has_condition())
    {
      extract_exprt(t->get_condition());
    }
  }

  // add the constant 0 to terminal_symbols
  exprt zero = constant_exprt(irep_idt(dstringt("0")), terminal_symbols[0].type());
  terminal_symbols.push_back(zero);

  simple_enumeratort enumerator(*this);  
  enumerator.enumerate();
}

void goto_synthesizer_parse_optionst::synthesize_loop_contracts(
  const irep_idt &function_name,
  goto_functionst::goto_functiont &goto_function)
{
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

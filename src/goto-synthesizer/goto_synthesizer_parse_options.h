/*******************************************************************\

Module: Command Line Parsing

Author: Qinheping Hu, qinhh@amazon.com

\*******************************************************************/

/// \file
/// Command Line Parsing

#ifndef CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_PARSE_OPTIONS_H
#define CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_PARSE_OPTIONS_H

#include <ansi-c/ansi_c_language.h>

#include <util/parse_options.h>
#include <util/timestamper.h>
#include <util/ui_message.h>
#include <util/validation_interface.h>

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/remove_calls_no_body.h>
#include <goto-programs/remove_const_function_pointers.h>
#include <goto-programs/restrict_function_pointers.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/goto_model.h>

#include <analyses/goto_check.h>

// clang-format off
#define GOTO_SYNTHESIZER_OPTIONS \
  "(all)" \
  "(dump-c-type-header):" \
  "(dump-c)(dump-cpp)(no-system-headers)(use-all-headers)(dot)(xml)" \
  "(verbosity):(version)(xml-ui)(json-ui)(show-loops)" \
  OPT_FLUSH \
  OPT_TIMESTAMP \
  "(validate-goto-binary)" \
  OPT_VALIDATE \
  // empty last line

// clang-format on

class goto_synthesizer_parse_optionst : public parse_options_baset
{
public:
  virtual int doit();
  virtual void help();

  goto_synthesizer_parse_optionst(int argc, const char **argv)
    : parse_options_baset(
        GOTO_SYNTHESIZER_OPTIONS,
        argc,
        argv,
        "goto-synthesizer"),
      function_pointer_removal_done(false),
      partial_inlining_done(false),
      remove_returns_done(false)
  {
  }

protected:
  void register_languages();

  void get_goto_program();
  
  bool function_pointer_removal_done;
  bool partial_inlining_done;
  bool remove_returns_done;
  
  goto_modelt goto_model;
};

#endif // CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_PARSE_OPTIONS_H

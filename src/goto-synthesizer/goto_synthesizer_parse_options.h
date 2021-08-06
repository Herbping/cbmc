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

#include <goto-instrument/loop_utils.h>
#include <util/symbol_table_base.h>



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

  void synthesize_loop_contracts(goto_functionst &goto_functions);
  void synthesize_loop_contracts(
    const irep_idt &function_name,
    goto_functionst::goto_functiont &goto_function);
  void synthesize_loop_contracts(
    const irep_idt &function_name,
    goto_functionst::goto_functiont &goto_function,
    const goto_programt::targett loop_head,
    const loopt &loop);
  void extract_exprt(const exprt &expr);
  bool call_back(const exprt &expr);

  exprt copy_exprt(const exprt &expr);
  exprt eterm(int size);
  exprt sterm(const irep_idt &id, int size);
  bool contain_E(const exprt &expr);
  bool is_partial(const exprt &expr);
  bool expand_with_symbol(exprt &expr, const exprt &symbol);
  std::queue<exprt> expand_with_terminals(std::queue<exprt> &expr);
  bool simple_verification(const exprt &candidate);
  bool simple_enumeration();
  
  bool function_pointer_removal_done;
  bool partial_inlining_done;
  bool remove_returns_done;

  exprt nonterminal_S = exprt(dstringt("ND_S"));
  exprt nonterminal_E = exprt(dstringt("ND_E"));
  
  goto_modelt goto_model;
  
  typedef std::unordered_map<irep_idt, symbolt> symbolst;

  symbol_tablet symbol_table;
  
  std::vector<exprt> terminal_symbols = {};
};

#endif // CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_PARSE_OPTIONS_H


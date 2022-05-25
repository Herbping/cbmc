/*******************************************************************\

Module: Command Line Parsing

Author: Qinheping Hu, qinhh@amazon.com

\*******************************************************************/

/// \file
/// Command Line Parsing

#ifndef CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_PARSE_OPTIONS_H
#define CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_PARSE_OPTIONS_H

#include <util/parse_options.h>
#include <util/symbol_table_base.h>
#include <util/timestamper.h>
#include <util/ui_message.h>
#include <util/validation_interface.h>

#include <analyses/goto_check.h>
#include <ansi-c/ansi_c_language.h>
#include <goto-instrument/loop_utils.h>

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
  "(deductive)"\
  "(hybrid)"\
  // empty last line

// clang-format on

class goto_synthesizer_parse_optionst : public parse_options_baset
{
public:
  virtual int doit();
  virtual void help();

  struct invariant_idt
  {
    irep_idt func_name;
    size_t loop_id;

    bool operator=(const invariant_idt &o) const
    {
      return func_name == o.func_name && loop_id == o.loop_id;
    }

    bool operator<(const invariant_idt &o) const
    {
      return func_name < o.func_name ||
             (func_name == o.func_name && loop_id < o.loop_id);
    }
  };

  typedef std::map<invariant_idt, exprt> invariantst;

  std::vector<exprt> terminal_symbols = {};
  goto_modelt goto_model;
  irep_idt target_function_name;
  invariantst invariant_map;

  goto_synthesizer_parse_optionst(int argc, const char **argv)
    : parse_options_baset(
        GOTO_SYNTHESIZER_OPTIONS,
        argc,
        argv,
        "goto-synthesizer"),
      function_pointer_removal_done(false),
      partial_inlining_done(false),
      remove_returns_done(false),
      deductive(false),
      hybrid(false)
  {
    tmp_post_map = expr_mapt();
    invariant_map = invariantst();
  }

  goto_programt::targett get_loop_head(const invariant_idt);
  goto_programt::targett get_loop_end(const invariant_idt);
  loopt get_loop(const invariant_idt);

protected:
  void register_languages();

  void get_goto_program();

  void synthesize_loop_contracts(goto_functionst &goto_functions);
  void synthesize_loop_contracts(
    const irep_idt &function_name,
    goto_functionst::goto_functiont &goto_function);
  void preprocess(
    const irep_idt &function_name,
    goto_functionst::goto_functiont &goto_function);
  void synthesize_loop_contracts(
    const irep_idt &function_name,
    goto_functionst::goto_functiont &goto_function,
    const goto_programt::targett loop_head,
    const loopt &loop);
  void extract_exprt(const exprt &expr);

  bool function_pointer_removal_done;
  bool partial_inlining_done;
  bool remove_returns_done;

  bool deductive;
  bool hybrid;

  typedef std::unordered_map<irep_idt, symbolt> symbolst;
  typedef std::map<exprt, exprt> expr_mapt;

  expr_mapt tmp_post_map;
  symbol_tablet symbol_table;
};

#endif // CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_PARSE_OPTIONS_H

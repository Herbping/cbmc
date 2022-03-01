/*******************************************************************\

Module: Verifier Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Verifier Interface

#ifndef CPROVER_GOTO_CHECKER_GOTO_SYNTHESIZER_VERIFIER_H
#define CPROVER_GOTO_CHECKER_GOTO_SYNTHESIZER_VERIFIER_H

#include "goto_synthesizer_parse_options.h"

class goto_synthesizer_verifiert
{
public:
  virtual ~goto_synthesizer_verifiert() = default;
  virtual bool verify(const exprt &expr) = 0;
};

class simple_verifiert : public goto_synthesizer_verifiert
{
public:
  simple_verifiert(goto_synthesizer_parse_optionst &po, ui_message_handlert &umh)
    : parse_option(po),
      ui_message_handler(umh)
  {
  }

  bool verify(const exprt &expr) override;

protected:
  goto_synthesizer_parse_optionst &parse_option;

  goto_programt original_program;
  goto_programt::targett target_loop_end;

  ui_message_handlert &ui_message_handler;

};

#endif // CPROVER_GOTO_CHECKER_GOTO_SYNTHESIZER_VERIFIER_H
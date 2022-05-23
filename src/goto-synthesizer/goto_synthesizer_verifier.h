/*******************************************************************\

Module: Verifier Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Verifier Interface

#ifndef CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_VERIFIER_H
#define CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_VERIFIER_H

#include <goto-programs/goto_trace.h>

#include "goto_synthesizer_parse_options.h"

class goto_synthesizer_verifiert
{
public:
  virtual ~goto_synthesizer_verifiert() = default;
  virtual bool verify(const exprt &expr) = 0;
};

enum cex_typet
{
  cex_oob,
  cex_null_pointer,
  cex_not_preserved,
  cex_ERROR
};
class cext
{
public:
  cext(
    std::map<exprt, std::string> &l_e,
    std::map<std::string, std::string> &o_s,
    std::map<std::string, std::string> &p_o,
    std::map<std::string, std::string> &l_e_e,
    std::map<std::string, std::string> &l_e_o,
    std::set<exprt> &l_l,
    cex_typet &type)
    : lhs_eval(l_e),
      object_sizes(o_s),
      pointer_offsets(p_o),
      loop_entry_eval(l_e_e),
      loop_entry_offsets(l_e_o),
      live_lhs(l_l),
      cex_type(type)
  {
  }
  cext() = default;

  exprt checked_pointer;
  exprt dereferenced_object;
  exprt offset;

  std::map<exprt, std::string> lhs_eval;
  std::map<std::string, std::string> object_sizes;
  std::map<std::string, std::string> pointer_offsets;
  std::map<std::string, std::string> loop_entry_eval;
  std::map<std::string, std::string> loop_entry_offsets;
  std::set<exprt> live_lhs;
  cex_typet cex_type;
};

class simple_verifiert : public goto_synthesizer_verifiert
{
public:
  simple_verifiert(
    goto_synthesizer_parse_optionst &po,
    ui_message_handlert &umh)
    : parse_option(po), ui_message_handler(umh)
  {
    original_functions = std::map<irep_idt, goto_programt>();
  }

  bool verify(const exprt &expr) override;
  bool verify();
  cext get_cex(
    const namespacet &ns,
    const goto_tracet &goto_trace,
    const source_locationt &loop_entry_loc,
    cex_typet type);

  cext return_cex;
  exprt checked_pointer;
  exprt dereferenced_object;
  exprt offset;

protected:
  goto_synthesizer_parse_optionst &parse_option;

  std::map<irep_idt, goto_programt> original_functions;
  goto_programt original_program;
  goto_programt::targett target_loop_end;
  goto_programt::targett target_loop_head;

  ui_message_handlert &ui_message_handler;
};

#endif // CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_VERIFIER_H

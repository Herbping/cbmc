/*******************************************************************\

Module: Utility functions for loop invariant synthesizer.

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

class cext
{
public:
  enum class cex_typet
  {
    cex_oob,
    cex_null_pointer,
    cex_not_preserved,
    cex_ERROR
  };

  cext(
    std::map<exprt, std::string> &lhs_eval,
    std::map<std::string, std::string> &object_sizes,
    std::map<std::string, std::string> &pointer_offsets,
    std::map<std::string, std::string> &loop_entry_eval,
    std::map<std::string, std::string> &loop_entry_offsets,
    std::set<exprt> &live_lhs,
    cex_typet &type)
    : lhs_eval(lhs_eval),
      object_sizes(object_sizes),
      pointer_offsets(pointer_offsets),
      loop_entry_eval(loop_entry_eval),
      loop_entry_offsets(loop_entry_offsets),
      live_lhs(live_lhs),
      cex_type(type)
  {
  }
  cext() = default;

  // pointer that failed the null pointer check
  exprt checked_pointer;

  exprt violated_predicate;
  exprt dereferenced_object_deprecated;
  exprt offset_deprecated;
  goto_synthesizer_parse_optionst::loop_idt cause_loop_id;

  // true if the violation happens in the cause loop
  // false if the violation happens after the cause loop
  bool is_violation_in_loop = true;

  // all the valuation of havoced variables
  std::map<exprt, std::string> lhs_eval;

  // __CPROVER_OBJECT_SIZE
  std::map<std::string, std::string> object_sizes;

  // __CPROVER_POINTER_OFFSET
  std::map<std::string, std::string> pointer_offsets;

  // __CPROVER_loop_entry
  std::map<std::string, std::string> loop_entry_eval;

  // __CPROVER_POINTER_OFFSET(__CPROVER_loop_entry( ))
  std::map<std::string, std::string> loop_entry_offsets;

  // set of live variables at the entry of loops
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

  cext return_cex;
  exprt checked_pointer_deprecated;
  exprt dereferenced_object_deprecated;
  exprt offset_deprecated;

protected:
  cext get_cex(
    const namespacet &ns,
    const goto_tracet &goto_trace,
    const source_locationt &loop_entry_loc,
    cext::cex_typet type);
  goto_synthesizer_parse_optionst::loop_idt get_cause_loop_id(
    const goto_tracet &goto_trace,
    const goto_programt::const_targett violation);

  goto_synthesizer_parse_optionst &parse_option;

  std::map<irep_idt, goto_programt> original_functions;
  goto_programt original_program_old;
  goto_programt::targett target_loop_end_old;
  goto_programt::targett target_loop_head_old;

  ui_message_handlert &ui_message_handler;
};

#endif // CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_VERIFIER_H

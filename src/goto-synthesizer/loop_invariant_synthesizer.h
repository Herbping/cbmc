
/*******************************************************************\

Module: Loop Invariant Synthesizer Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Verifier Interface

#ifndef CPROVER_GOTO_SYNTHESIZER_LOOP_INVARIANT_SYNTHESIZER_H
#define CPROVER_GOTO_SYNTHESIZER_LOOP_INVARIANT_SYNTHESIZER_H

#include <util/message.h>

#include <goto-programs/goto_model.h>

struct loop_idt
{
  irep_idt func_name;
  unsigned int loop_number;

  bool operator==(const loop_idt &o) const
  {
    return func_name == o.func_name && loop_number == o.loop_number;
  }

  bool operator<(const loop_idt &o) const
  {
    return func_name < o.func_name ||
           (func_name == o.func_name && loop_number < o.loop_number);
  }
};

class loop_invaraint_synthesizer_baset
{
public:
  loop_invaraint_synthesizer_baset(goto_modelt &goto_model, messaget &log)
    : goto_model(goto_model), log(log)
  {
  }
  virtual ~loop_invaraint_synthesizer_baset() = default;
  virtual bool synthesize() = 0;

protected:
  goto_modelt &goto_model;

  messaget &log;
};

class enumerative_loop_invariant_synthesizert
  : public loop_invaraint_synthesizer_baset
{
public:
  bool synthesize() override;
};

#endif // CPROVER_GOTO_SYNTHESIZER_LOOP_INVARIANT_SYNTHESIZER_H

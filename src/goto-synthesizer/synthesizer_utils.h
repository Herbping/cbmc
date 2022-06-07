/*******************************************************************\

Module: Utility functions for loop invariant synthesizer.

Author: Qinheping Hu, qinhh@amazon.com

Date: May 2022

\*******************************************************************/

#ifndef CPROVER_GOTO_SYNTHESIZER_SYNTHESIZER_UTILS_H
#define CPROVER_GOTO_SYNTHESIZER_SYNTHESIZER_UTILS_H

#include <goto-programs/goto_model.h>
#include <goto-programs/goto_program.h>

#include <goto-instrument/loop_utils.h>

goto_programt::targett get_loop_head(
  const irep_idt &fun_name,
  const size_t loop_number,
  goto_functionst::function_mapt &function_map);

goto_programt::targett get_loop_end(
  const irep_idt &fun_name,
  const size_t loop_number,
  goto_functionst::function_mapt &function_map);

loopt get_loop(
  const irep_idt &fun_name,
  const size_t loop_number,
  goto_functionst::function_mapt &function_map);

bool check_violation_in_loop(
  const irep_idt &fun_name,
  const size_t loop_number,
  goto_functionst::function_mapt &function_map,
  const size_t violation_location_number);

#endif // CPROVER_GOTO_SYNTHESIZER_SYNTHESIZER_UTILS_H
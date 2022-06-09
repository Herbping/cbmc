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

bool check_violation_in_loop(
  const irep_idt &fun_name,
  const size_t loop_number,
  goto_functionst::function_mapt &function_map,
  const size_t violation_location_number);

irep_idt convert_static_function_name(const source_locationt &source_location);

// find the original instruction of an possibly inlined instruction
goto_programt::const_targett get_original_instruction(
  const goto_functiont &function,
  goto_programt::const_targett instruction);

bool check_same_line(
  const goto_programt::const_targett &in1,
  const goto_programt::const_targett &in2);

#endif // CPROVER_GOTO_SYNTHESIZER_SYNTHESIZER_UTILS_H

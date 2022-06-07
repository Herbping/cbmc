/*******************************************************************\

Module: Utility functions for loop invariant synthesizer.

Author: Qinheping Hu, qinhh@amazon.com

Date: May 2022

\*******************************************************************/

#include "synthesizer_utils.h"

#include <langapi/language_util.h>

loopt get_loop(
  const irep_idt &fun_name,
  const size_t target_loop_number,
  goto_functionst::function_mapt &function_map)
{
  natural_loops_mutablet natural_loops(function_map[fun_name].body);

  size_t loop_number = 0;
  for(const auto &loop : natural_loops.loop_map)
  {
    if(loop_number == target_loop_number)
      return loop.second;
    loop_number++;
  }
  UNREACHABLE;
}

goto_programt::targett get_loop_end(
  const irep_idt &fun_name,
  const size_t target_loop_number,
  goto_functionst::function_mapt &function_map)
{
  natural_loops_mutablet natural_loops(function_map[fun_name].body);

  size_t loop_number = 0;
  for(const auto &loop_p : natural_loops.loop_map)
  {
    if(loop_number == target_loop_number)
    {
      const goto_programt::targett loop_head = loop_p.first;
      goto_programt::targett loop_end = loop_p.first;
      const loopt &loop = loop_p.second;
      for(const auto &t : loop)
      {
        if(
          t->is_goto() && t->get_target() == loop_head &&
          t->location_number > loop_end->location_number)
          loop_end = t;
      }
      return loop_end;
    }
    loop_number++;
  }
  UNREACHABLE;
}

goto_programt::targett get_loop_head(
  const irep_idt &fun_name,
  const size_t target_loop_number,
  goto_functionst::function_mapt &function_map)
{
  natural_loops_mutablet natural_loops(function_map[fun_name].body);

  size_t loop_number = 0;
  for(const auto &loop : natural_loops.loop_map)
  {
    if(loop_number == target_loop_number)
      return loop.first;
    loop_number++;
  }
  UNREACHABLE;
}

bool check_violation_in_loop(
  const irep_idt &fun_name,
  const size_t loop_number,
  goto_functionst::function_mapt &function_map,
  const size_t violation_location_number)
{
  bool is_in_the_target_loop = false;
  for(goto_programt::const_targett it =
        function_map[fun_name].body.instructions.begin();
      it != function_map[fun_name].body.instructions.end();
      ++it)
  {
    if(it->is_loop_havoc())
    {
      if(loop_number == it->loop_number)
        is_in_the_target_loop = true;
    }

    if(
      is_in_the_target_loop && it->is_assume() &&
      it->condition() == false_exprt())
    {
      return violation_location_number < it->location_number;
    }
  }
  UNREACHABLE;
}

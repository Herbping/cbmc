/*******************************************************************\

Module: Utility functions for loop invariant synthesizer.

Author: Qinheping Hu, qinhh@amazon.com

Date: May 2022

\*******************************************************************/

#include "synthesizer_utils.h"

#include <langapi/language_util.h>

goto_programt::targett get_loop_end(
  const irep_idt &fun_name,
  const size_t target_loop_number,
  goto_functionst::function_mapt &function_map)
{
  natural_loops_mutablet natural_loops(function_map[fun_name].body);

  for(const auto &loop_p : natural_loops.loop_map)
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
    if(loop_end->loop_number == target_loop_number)
      return loop_end;
  }

  UNREACHABLE;
}

goto_programt::targett get_loop_head(
  const irep_idt &fun_name,
  const size_t target_loop_number,
  goto_functionst::function_mapt &function_map)
{
  natural_loops_mutablet natural_loops(function_map[fun_name].body);

  for(const auto &loop_p : natural_loops.loop_map)
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
      if(loop_end->loop_number == target_loop_number)
        return loop_head;
    }
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

irep_idt convert_static_function_name(const source_locationt &source_location)
{
  std::string path = source_location.get_file().c_str();
  std::string base_filename = path.substr(path.find_last_of("/\\") + 1);

  size_t dot = base_filename.find_last_of(".");
  std::string name = base_filename.substr(0, dot);
  std::string ext = base_filename.substr(dot + 1, base_filename.size() - dot);

  // are there more ext for static file?
  if(ext == "inl")
  {
    return ("__CPROVER_file_local_" + name + "_" + ext + "_") +
           source_location.get_function().c_str();
  }
  return source_location.get_function();
}

bool check_same_line(
  const goto_programt::const_targett &in1,
  const goto_programt::const_targett &in2)
{
  return in1->source_location().get_line() == in2->source_location().get_line();
}

goto_programt::const_targett get_original_instruction(
  const goto_functiont &function,
  goto_programt::const_targett instruction)
{
  for(goto_programt::const_targett it = function.body.instructions.begin();
      it != function.body.instructions.end();
      it++)
  {
    if(it->is_assert() && instruction->is_assert())
    {
      if(it->get_condition().full_eq(instruction->get_condition()))
        return it;
    }

    if(it->is_loop_havoc() && instruction->is_loop_havoc())
    {
      if(
        it->assign_lhs().full_eq(instruction->assign_lhs()) &&
        check_same_line(it, instruction))
        return it;
    }
  }
  UNREACHABLE;
}

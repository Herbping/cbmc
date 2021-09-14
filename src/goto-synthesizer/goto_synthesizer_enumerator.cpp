/*******************************************************************\

Module: Enumerator Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Enumerator Interface

#include "goto_synthesizer_enumerator.h"
#include "goto_synthesizer_parse_options.h"

#include "util/expr.h"
#include "util/irep.h"

#include <langapi/language_util.h>

#include <fstream>
#include <iostream>
#include <memory>

exprt simple_enumeratort::eterm(int size)
{
  if(size == 1)
  {
    return nonterminal_E;
  }

  return plus_exprt(nonterminal_E, eterm(size-1));
}

exprt simple_enumeratort::sterm(const irep_idt &id, int size)
{
  return binary_relation_exprt(eterm(size), id, eterm(size));
}

exprt simple_enumeratort::copy_exprt(const exprt &expr)
{
  exprt result(expr.id(), expr.type());
  for(const auto &operand : expr.operands())
  {
    result.add_to_operands(operand);
  }
  return result;
}

bool simple_enumeratort::contain_E(const exprt &expr)
{
  if(expr == nonterminal_E)
  {
    return true;
  }

  for(const auto &operand : expr.operands()){
    if(contain_E(operand))
      return true;
  } 
  return false;
}

bool simple_enumeratort::is_partial(const exprt &expr)
{
  if(expr == nonterminal_S || expr == nonterminal_E)
  {
    return true;
  }

  for(const auto &operand : expr.operands()){
    if(is_partial(operand))
      return true;
  } 
  return false;
}

bool simple_enumeratort::expand_with_symbol(exprt &expr, const exprt &symbol)
{
  if(expr == nonterminal_E)
  {
    expr = symbol;
    return true;
  }
  for(auto &operand : expr.operands())
  {
    if(expand_with_symbol(operand, symbol))
    {
      return true;
    }
  }
  return false;
}

std::queue<exprt> simple_enumeratort::expand_with_terminals(std::queue<exprt> &exprs)
{
  std::queue<exprt> result;

  while(!exprs.empty())
  {
    exprt current_expr = exprs.front();

    if(contain_E(current_expr))
    {
      for(const auto &symbol : parse_option.terminal_symbols)
      {
        exprt new_expr = copy_exprt(current_expr);
        expand_with_symbol(new_expr, symbol);
        exprs.push(new_expr);
      }
    }
    else
    {
      result.push(current_expr);
    }

    exprs.pop();
  }
  return result;
}

bool simple_enumeratort::enumerate()
{
  std::deque<exprt> current_partial_terms;

  // number of clauses in the invariant
  // depth of each clause

  nonterminal_S = copy_exprt(nonterminal_S);
  nonterminal_E = copy_exprt(nonterminal_E);

  int num_clauses = 0;
  int size_eterm = 0; 

  // limit the search depth?
  while(true)  
  {
    num_clauses++;
    if(num_clauses % 2 == 1)
      size_eterm++;
    for(int i = 0; i <= num_clauses; i++)
    {
      exprt skeleton = true_exprt();
      for(int j = 0; j < num_clauses; j++)
      {
        if(i > j)
        {
          skeleton = and_exprt(skeleton, sterm(ID_equal, size_eterm));
        }
        else
        {
          skeleton = and_exprt(skeleton, sterm(ID_le, size_eterm));
        }
      }
      current_partial_terms.push_back(skeleton);
      // instantiate skeleton with terminal symbols
      // and send candidate back to call_back function
      while(!current_partial_terms.empty())
      {
        exprt partial_term = current_partial_terms.front();
        current_partial_terms.pop_front();

        std::queue<exprt> to_add;
        if(contain_E(partial_term))
        {
          to_add.push(partial_term);
          to_add = expand_with_terminals(to_add);
          while(!to_add.empty())
          {
            current_partial_terms.push_front(to_add.front());
            to_add.pop();
          }
        }
        else
        {
          if(!is_partial(partial_term) && parse_option.call_back(partial_term))
          {
            return true;
          }
        }
      }
    }
  }
}
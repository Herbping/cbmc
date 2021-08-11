/*******************************************************************\

Module: Enumerator Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Enumerator Interface

#ifndef CPROVER_GOTO_CHECKER_GOTO_SYNTHESIZER_ENUMERATOR_H
#define CPROVER_GOTO_CHECKER_GOTO_SYNTHESIZER_ENUMERATOR_H

#include "goto_synthesizer_parse_options.h"

class goto_synthesizer_enumeratort
{
public:
  virtual ~goto_synthesizer_enumeratort() = default;
  virtual bool enumerate() = 0;
};

class simple_enumerator : public goto_synthesizer_enumeratort
{
public:
  simple_enumerator(goto_synthesizer_parse_optionst &po)
    : parse_option(po)
  {
  }

  bool enumerate() override;

protected:
  goto_synthesizer_parse_optionst &parse_option;

  exprt nonterminal_S = exprt(dstringt("ND_S"));
  exprt nonterminal_E = exprt(dstringt("ND_E"));
  
  exprt eterm(int size);
  exprt sterm(const irep_idt &id, int size);
  exprt copy_exprt(const exprt &expr);

  bool contain_E(const exprt &expr);
  bool is_partial(const exprt &expr);
  bool expand_with_symbol(exprt &expr, const exprt &symbol);
  std::queue<exprt> expand_with_terminals(std::queue<exprt> &expr);
};

#endif // CPROVER_GOTO_CHECKER_GOTO_SYNTHESIZER_ENUMERATOR_H
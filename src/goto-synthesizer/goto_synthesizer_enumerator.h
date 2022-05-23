/*******************************************************************\

Module: Enumerator Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Enumerator Interface

#ifndef CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_ENUMERATOR_H
#define CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_ENUMERATOR_H

#include <langapi/language_util.h>

#include "goto_synthesizer_parse_options.h"
#include "goto_synthesizer_verifier.h"

#include <iostream>

typedef std::list<exprt> exprst;
typedef std::list<cext> cexst;
typedef std::list<size_t> sizest;
class generator_baset
{
public:
  virtual void set_size(size_t new_size) = 0;
  virtual exprst generate() = 0;
  virtual generator_baset *clone() = 0;
  virtual std::string get_name()
  {
    return name;
  }
  virtual std::string get_type_name()
  {
    return type_name;
  }
  virtual ~generator_baset()
  {
  }

protected:
  std::string name;
  std::string type_name = "base";
};

typedef std::list<generator_baset *> generatorst;

class leaf_geneartort : public generator_baset
{
public:
  explicit leaf_geneartort(exprst le, std::string n = "")
  {
    leaf_exprs = le;
    name = n;
    allowed_size = 0;
    iterable_size = le.size();
    type_name = "leaf";
  }

  exprst generate() override
  {
    exprst result = exprst();
    if(allowed_size != 1)
      return result;

    for(auto expr : leaf_exprs)
    {
      result.push_back(expr);
    }
    return result;
  }

  void set_size(size_t new_size) override
  {
    allowed_size = new_size;
  }

  leaf_geneartort *clone() override
  {
    return new leaf_geneartort(leaf_exprs, name);
  }

  size_t get_allowed_size()
  {
    return allowed_size;
  }

protected:
  size_t allowed_size;
  exprst leaf_exprs;
  size_t iterable_size;
};

class non_leaf_geneartort : public generator_baset
{
public:
  non_leaf_geneartort() = default;

  static bool default_good_size_tuple(sizest sizes)
  {
    return true;
  }

  static bool add_good_size_tuple(sizest sizes)
  {
    if(sizes.size() <= 1)
      return true;
    return sizes.front() == 1;
  }

  static bool commutative_good_size_tuple(sizest sizes)
  {
    if(sizes.size() <= 1)
      return true;
    return sizes.front() <= sizes.back();
  }

  explicit non_leaf_geneartort(generatorst sg, std::string n = "")
  {
    sub_generators = generatorst();
    for(auto g : sg)
    {
      sub_generators.push_back(g->clone());
    }
    name = n;
    allowed_size = 0;
    arity = sg.size();
    INVARIANT(arity > 0, "zero arity");
    good_size_tuple = default_good_size_tuple;
    type_name = "nonleaf";
  }

  std::list<exprst>
  cartesian_product_of_generators(generatorst &generators, size_t pos = 0)
  {
    std::list<exprst> result = std::list<exprst>();
    size_t tuple_size = generators.size();
    if(tuple_size == pos + 1)
    {
      for(auto e : generators.back()->generate())
      {
        exprst new_tuple = exprst();
        new_tuple.push_back(e);
        result.push_back(new_tuple);
      }
      return result;
    }
    else
    {
      for(auto sub_tuple : cartesian_product_of_generators(generators, pos + 1))
      {
        auto front = generators.begin();
        std::advance(front, pos);
        for(auto elem : (*front)->generate())
        {
          exprst new_tuple = exprst(sub_tuple);
          new_tuple.push_front(elem);
          result.push_back(new_tuple);
        }
      }
    }
    return result;
  }

  std::list<sizest> get_partitions(size_t n, size_t k)
  {
    // generate all splits of n into k components.
    // Order of the split components is considered relevant.
    INVARIANT(n >= k, "too less elements to be partitioned");

    std::list<sizest> result = std::list<sizest>();

    size_t *cuts = new size_t[k + 1];
    cuts[0] = 0;
    cuts[1] = (n - k + 1);
    for(size_t i = 0; i < k - 1; i++)
    {
      cuts[i + 2] = (n - k + 1 + i + 1);
    }

    bool done = false;

    while(!done)
    {
      sizest new_partition = sizest();
      for(size_t i = 1; i < k + 1; i++)
      {
        new_partition.push_back(cuts[i] - cuts[i - 1]);
      }

      size_t rightmost = 0;
      for(size_t i = 1; i < k; i++)
      {
        if(cuts[i] - cuts[i - 1] > 1)
        {
          rightmost = i;
          cuts[i] = cuts[i] - 1;
          break;
        }
      }

      if(rightmost == 0)
        done = true;
      else
      {
        size_t accum = 1;
        for(size_t i = rightmost - 1; i >= 1; i++)
        {
          cuts[i] = cuts[rightmost] - accum;
          accum++;
        }
      }
      result.push_back(new_partition);
    }
    return result;
  }

  exprst generate() override
  {
    exprst result = exprst();
    if(allowed_size - 1 < arity)
      return result;

    for(auto partition : get_partitions(allowed_size - 1, arity))
    {
      if(!good_size_tuple(partition))
        continue;

      set_sub_generator_sizes(partition);
      for(auto product_tuple : cartesian_product_of_generators(sub_generators))
      {
        if(commutative_check(product_tuple))
          result.push_back(instantiate(product_tuple));
      }
    }

    return result;
  }

  void set_size(size_t new_size) override
  {
    allowed_size = new_size;
  }

  non_leaf_geneartort *clone() override
  {
    return new non_leaf_geneartort(sub_generators);
  }

  virtual bool commutative_check(exprst es)
  {
    return true;
  }

protected:
  void set_sub_generator_sizes(sizest sizes)
  {
    INVARIANT(sizes.size() == arity, "arity not equal to number of arguments");
    auto front = sizes.begin();
    for(auto sub_generator : sub_generators)
    {
      sub_generator->set_size(*front);
      std::advance(front, 1);
    }
  }

  virtual exprt instantiate(exprst exprs)
  {
    return true_exprt();
  };
  size_t arity;
  size_t allowed_size;
  generatorst sub_generators;
  bool (*good_size_tuple)(sizest);
};

class binary_functional_generatort : public non_leaf_geneartort
{
public:
  binary_functional_generatort(irep_idt op, generatorst sg, std::string n = "")
    : non_leaf_geneartort(sg, n)
  {
    INVARIANT(sg.size() == 2, "number of argument should be 2");
    op_id = op;
    if(op_id == ID_plus)
      good_size_tuple = add_good_size_tuple;
    if(op_id == ID_equal || op_id == ID_and)
      good_size_tuple = commutative_good_size_tuple;
    type_name = "binary_fun";
  }

  binary_functional_generatort(
    irep_idt op,
    generator_baset &op1,
    generator_baset &op2,
    std::string n = "")
  {
    name = n;
    sub_generators = generatorst();
    sub_generators.push_back(&op1);
    sub_generators.push_back(&op2);
    op_id = op;
    if(op_id == ID_plus)
      good_size_tuple = add_good_size_tuple;
    if(op_id == ID_equal || op_id == ID_and)
      good_size_tuple = commutative_good_size_tuple;
    type_name = "binary_fun";
  }

  void set_size(size_t new_size) override
  {
    allowed_size = new_size;
  }

  binary_functional_generatort *clone() override
  {
    generatorst copied_sg = generatorst();
    for(auto g : sub_generators)
    {
      auto to_add_ptr = g->clone();
      copied_sg.push_back(to_add_ptr);
    }
    return new binary_functional_generatort(op_id, copied_sg, name);
  }

  bool commutative_check(exprst exprs) override
  {
    if(
      (op_id == ID_equal || op_id == ID_le || op_id == ID_lt ||
       op_id == ID_and) &&
      from_expr(exprs.front()) == from_expr(exprs.back()))
      return false;

    if(op_id != ID_plus)
      return true;

    if(from_expr(exprs.front()) > from_expr(exprs.back()))
      return false;
    return true;
  }

protected:
  exprt instantiate(exprst exprs) override
  {
    INVARIANT(
      exprs.size() == 2,
      "number of arugment should be 2 but not " + integer2string(exprs.size()));
    if(op_id == ID_equal)
      return equal_exprt(exprs.front(), exprs.back());
    if(op_id == ID_le)
      return less_than_or_equal_exprt(exprs.front(), exprs.back());
    if(op_id == ID_lt)
      return less_than_exprt(exprs.front(), exprs.back());
    if(op_id == ID_and)
      return and_exprt(exprs.front(), exprs.back());
    if(op_id == ID_plus)
      return plus_exprt(exprs.front(), exprs.back());
    return binary_exprt(exprs.front(), op_id, exprs.back());
  }

  irep_idt op_id;
};

class alternatives_generatort : public generator_baset
{
public:
  explicit alternatives_generatort(generatorst sg)
  {
    sub_generators = generatorst();
    for(auto g : sg)
    {
      sub_generators.push_back(g->clone());
    }
    type_name = "alt";
  }

  void set_size(size_t new_size) override
  {
    allowed_size = new_size;
    for(auto g : sub_generators)
    {
      g->set_size(new_size);
    }
  }

  exprst generate() override
  {
    exprst result = exprst();
    for(auto generator : sub_generators)
    {
      for(auto e : generator->generate())
      {
        result.push_back(e);
      }
    }
    return result;
  }

  alternatives_generatort *clone() override
  {
    return new alternatives_generatort(sub_generators);
  }

protected:
  size_t allowed_size;
  generatorst sub_generators;
};

class generator_factory_baset;

class recursive_generator_placeholdert : public generator_baset
{
public:
  recursive_generator_placeholdert()
  {
    type_name = "placeholder";
  }

  recursive_generator_placeholdert(
    generator_factory_baset *fac,
    std::string id,
    std::string n = "")
    : identifier(id), factory(fac)
  {
    name = n;
    type_name = "placeholder";
  }

  void set_size(size_t new_size) override;

  exprst generate() override
  {
    exprst result = exprst();
    if(actual_generator->get_name() == "None")
      return result;

    return actual_generator->generate();
  }

  recursive_generator_placeholdert *clone() override
  {
    return new recursive_generator_placeholdert(factory, identifier);
  }

  std::string identifier;

protected:
  bool eq(recursive_generator_placeholdert other)
  {
    return other.identifier == identifier;
  }
  bool ne(recursive_generator_placeholdert other)
  {
    return other.identifier != identifier;
  }

  generator_factory_baset *factory;
  generator_baset *actual_generator;
};

class generator_factory_baset
{
public:
  generator_factory_baset()
  {
    generator_map = std::map<std::string, recursive_generator_placeholdert>();
    generator_constructors = std::map<std::string, generatorst>();
  }

  recursive_generator_placeholdert make_placeholder(std::string identifier)
  {
    INVARIANT(generator_map.count(identifier) == 0, "duplicated non-terminals");
    recursive_generator_placeholdert result =
      recursive_generator_placeholdert(this, identifier);
    generator_map[identifier] = result;
    return result;
  }

  recursive_generator_placeholdert
  make_generator(std::string generator_name, generatorst arg_geneartors)
  {
    generator_constructors[generator_name] = arg_geneartors;
    return generator_map[generator_name];
  }

  bool has_placeholder(std::string id)
  {
    return generator_map.count(id) == 1;
  }

  virtual generator_baset *
    instantiate_placeholder(recursive_generator_placeholdert) = 0;

protected:
  std::map<std::string, recursive_generator_placeholdert> generator_map;
  std::map<std::string, generatorst> generator_constructors;
};

class recursive_geneartor_factoryt : public generator_factory_baset
{
public:
  recursive_geneartor_factoryt() : generator_factory_baset()
  {
  }

  alternatives_generatort *
  instantiate_placeholder(recursive_generator_placeholdert placeholder) override
  {
    generatorst args = generator_constructors[placeholder.identifier];
    return new alternatives_generatort(args);
  }
};

class goto_synthesizer_enumeratort
{
public:
  virtual ~goto_synthesizer_enumeratort() = default;
  virtual bool enumerate() = 0;
};

class simple_enumeratort : public goto_synthesizer_enumeratort
{
public:
  simple_enumeratort(
    goto_synthesizer_parse_optionst &po,
    exprt fc,
    cext &c,
    ui_message_handlert &uimh)
    : parse_option(po),
      first_candidate(fc),
      neg_test(c),
      ui_message_handler(uimh)
  {
    neg_tests = cexst();
    neg_tests.push_back(c);
  }
  static void test_geneartors(size_t num_var, size_t size_term);

  bool enumerate() override;

protected:
  goto_synthesizer_parse_optionst &parse_option;

  exprt nonterminal_S = exprt(dstringt("ND_S"));
  exprt nonterminal_E = exprt(dstringt("ND_E"));

  exprt first_candidate;

  exprt eterm(int size);
  exprt sterm(const irep_idt &id, int size);
  exprt copy_exprt(const exprt &expr);

  bool contain_E(const exprt &expr);
  bool is_partial(const exprt &expr);
  bool expand_with_symbol(exprt &expr, const exprt &symbol);
  std::queue<exprt> expand_with_terminals(std::queue<exprt> &expr);

  cext neg_test;
  cexst neg_tests;
  bool quick_verify(const exprt &candidate, const cext &cex);
  ui_message_handlert &ui_message_handler;
};

#endif // CPROVER_GOTO_SYNTHESIZER_GOTO_SYNTHESIZER_ENUMERATOR_H

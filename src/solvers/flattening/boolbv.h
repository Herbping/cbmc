/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BOOLBV_H
#define CPROVER_SOLVERS_FLATTENING_BOOLBV_H

//
// convert expression to boolean formula
//

#include <util/endianness_map.h>
#include <util/expr.h>
#include <util/mp_arith.h>

#include <solvers/lowering/functions.h>

#include "arrays.h"
#include "boolbv_map.h"
#include "boolbv_width.h"
#include "bv_utils.h" // IWYU pragma: keep

class binary_overflow_exprt;
class bitreverse_exprt;
class bswap_exprt;
class byte_extract_exprt;
class byte_update_exprt;
class concatenation_exprt;
class extractbit_exprt;
class extractbits_exprt;
class floatbv_round_to_integral_exprt;
class floatbv_typecast_exprt;
class ieee_float_op_exprt;
class overflow_result_exprt;
class replication_exprt;
class unary_overflow_exprt;
class union_typet;
class update_bit_exprt;
class update_bits_exprt;

class boolbvt:public arrayst
{
public:
  boolbvt(
    const namespacet &_ns,
    propt &_prop,
    message_handlert &message_handler,
    bool get_array_constraints = false)
    : arrayst(_ns, _prop, message_handler, get_array_constraints),
      unbounded_array(unbounded_arrayt::U_NONE),
      bv_width(_ns),
      bv_utils(_prop),
      functions(*this),
      map(_prop)
  {
  }

  virtual const bvt &convert_bv( // check cache
    const exprt &expr,
    const std::optional<std::size_t> expected_width = {});

  virtual bvt convert_bitvector(const exprt &expr); // no cache

  // overloading
  exprt get(const exprt &expr) const override;
  void set_to(const exprt &expr, bool value) override;
  void print_assignment(std::ostream &out) const override;
  exprt handle(const exprt &) override;

  void clear_cache() override
  {
    SUB::clear_cache();
    bv_cache.clear();
  }

  void finish_eager_conversion() override
  {
    finish_eager_conversion_quantifiers();
    functions.finish_eager_conversion();
    SUB::finish_eager_conversion();
  }

  enum class unbounded_arrayt { U_NONE, U_ALL, U_AUTO };
  unbounded_arrayt unbounded_array;

  mp_integer get_value(const bvt &bv)
  {
    return get_value(bv, 0, bv.size());
  }

  mp_integer get_value(const bvt &bv, std::size_t offset, std::size_t width);

  const boolbv_mapt &get_map() const
  {
    return map;
  }

  virtual std::size_t boolbv_width(const typet &type) const
  {
    return bv_width(type);
  }

  virtual endianness_mapt
  endianness_map(const typet &type, bool little_endian) const
  {
    return endianness_mapt{type, little_endian, ns};
  }

  virtual endianness_mapt endianness_map(const typet &type) const;

protected:
  boolbv_widtht bv_width;
  bv_utilst bv_utils;

  // uninterpreted functions
  functionst functions;

  // the mapping from identifiers to literals
  boolbv_mapt map;

  // overloading
  literalt convert_rest(const exprt &expr) override;
  virtual bool boolbv_set_equality_to_true(const equal_exprt &expr);

  // NOLINTNEXTLINE(readability/identifiers)
  typedef arrayst SUB;

  bvt conversion_failed(const exprt &expr);

  typedef std::unordered_map<const exprt, bvt, irep_hash> bv_cachet;
  bv_cachet bv_cache;

  bool type_conversion(
    const typet &src_type, const bvt &src,
    const typet &dest_type, bvt &dest);

  virtual literalt convert_bv_rel(const binary_relation_exprt &);
  virtual literalt convert_typecast(const typecast_exprt &expr);
  virtual literalt convert_reduction(const unary_exprt &expr);
  virtual literalt convert_onehot(const unary_exprt &expr);
  virtual literalt convert_extractbit(const extractbit_exprt &expr);
  virtual literalt convert_binary_overflow(const binary_overflow_exprt &expr);
  virtual literalt convert_unary_overflow(const unary_overflow_exprt &expr);
  virtual literalt convert_equality(const equal_exprt &expr);
  virtual literalt convert_verilog_case_equality(
    const binary_relation_exprt &expr);
  virtual literalt convert_ieee_float_rel(const binary_relation_exprt &);
  virtual literalt convert_quantifier(const quantifier_exprt &expr);

  virtual bvt convert_index(const exprt &array, const mp_integer &index);
  virtual bvt convert_index(const index_exprt &expr);
  virtual bvt convert_bswap(const bswap_exprt &expr);
  virtual bvt convert_byte_extract(const byte_extract_exprt &expr);
  virtual bvt convert_byte_update(const byte_update_exprt &expr);
  virtual bvt convert_constraint_select_one(const exprt &expr);
  virtual bvt convert_if(const if_exprt &expr);
  virtual bvt convert_struct(const struct_exprt &expr);
  virtual bvt convert_array(const exprt &expr);
  virtual bvt convert_complex(const complex_exprt &expr);
  virtual bvt convert_complex_real(const complex_real_exprt &expr);
  virtual bvt convert_complex_imag(const complex_imag_exprt &expr);
  virtual bvt convert_array_comprehension(const array_comprehension_exprt &);
  virtual bvt convert_let(const let_exprt &);
  virtual bvt convert_array_of(const array_of_exprt &expr);
  virtual bvt convert_union(const union_exprt &expr);
  virtual bvt convert_empty_union(const empty_union_exprt &expr);
  virtual bvt convert_bv_typecast(const typecast_exprt &expr);
  virtual bvt convert_add_sub(const exprt &expr);
  virtual bvt convert_mult(const mult_exprt &expr);
  virtual bvt convert_div(const div_exprt &expr);
  virtual bvt convert_mod(const mod_exprt &expr);
  virtual bvt convert_floatbv_op(const ieee_float_op_exprt &);
  virtual bvt convert_floatbv_mod_rem(const binary_exprt &);
  virtual bvt convert_floatbv_typecast(const floatbv_typecast_exprt &expr);
  virtual bvt
  convert_floatbv_round_to_integral(const floatbv_round_to_integral_exprt &);
  virtual bvt convert_member(const member_exprt &expr);
  virtual bvt convert_with(const with_exprt &expr);
  virtual bvt convert_update(const update_exprt &);
  virtual bvt convert_update_bit(const update_bit_exprt &);
  virtual bvt convert_update_bits(const update_bits_exprt &);
  virtual bvt convert_case(const exprt &expr);
  virtual bvt convert_cond(const cond_exprt &);
  virtual bvt convert_shift(const binary_exprt &expr);
  virtual bvt convert_bitwise(const exprt &expr);
  virtual bvt convert_unary_minus(const unary_minus_exprt &expr);
  virtual bvt convert_abs(const abs_exprt &expr);
  virtual bvt convert_concatenation(const concatenation_exprt &expr);
  virtual bvt convert_replication(const replication_exprt &expr);
  virtual bvt convert_constant(const constant_exprt &expr);
  virtual bvt convert_extractbits(const extractbits_exprt &expr);
  virtual bvt convert_symbol(const exprt &expr);
  virtual bvt convert_bv_reduction(const unary_exprt &expr);
  virtual bvt convert_not(const not_exprt &expr);
  virtual bvt convert_power(const binary_exprt &expr);
  virtual bvt convert_function_application(
    const function_application_exprt &expr);
  virtual bvt convert_bitreverse(const bitreverse_exprt &expr);
  virtual bvt convert_saturating_add_sub(const binary_exprt &expr);
  virtual bvt convert_overflow_result(const overflow_result_exprt &expr);

  bvt convert_update_bits(bvt src, const exprt &index, const bvt &new_value);

  void convert_with(
    const typet &type,
    const exprt &where,
    const exprt &new_value,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_with_bv(
    const exprt &index,
    const exprt &new_value,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_with_array(
    const array_typet &type,
    const exprt &index,
    const exprt &new_value,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_with_union(
    const union_typet &type,
    const exprt &new_value,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_with_struct(
    const struct_typet &type,
    const exprt &where,
    const exprt &new_value,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_update_rec(
    const exprt::operandst &designator,
    std::size_t d,
    const typet &type,
    std::size_t offset,
    const exprt &new_value,
    bvt &bv);

  virtual exprt bv_get_unbounded_array(const exprt &) const;

  virtual exprt
  bv_get_rec(const exprt &expr, const bvt &bv, std::size_t offset) const;

  exprt bv_get(const bvt &bv, const typet &type) const;
  exprt bv_get_cache(const exprt &expr) const;

  // unbounded arrays
  bool is_unbounded_array(const typet &type) const override;

  // quantifier instantiations
  class quantifiert
  {
  public:
    quantifiert(exprt _expr, literalt _l)
      : expr(std::move(_expr)), l(std::move(_l))
    {
    }

    exprt expr;
    literalt l;
  };

  typedef std::list<quantifiert> quantifier_listt;
  quantifier_listt quantifier_list;

  void finish_eager_conversion_quantifiers();

  typedef std::vector<std::size_t> offset_mapt;
  offset_mapt build_offset_map(const struct_typet &src);

  // strings
  numberingt<irep_idt> string_numbering;

  // scopes
  std::size_t scope_counter = 0;

  /// create new, unique variables for the given binding
  binding_exprt::variablest fresh_binding(const binding_exprt &);
};

#endif // CPROVER_SOLVERS_FLATTENING_BOOLBV_H

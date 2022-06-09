/*******************************************************************\

Module: Enumerator Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Enumerator Interface

#include "goto_synthesizer_enumerator.h"

#include <util/c_types.h>
#include <util/run.h>
#include <util/tempfile.h>

#include <langapi/language_util.h>

#include "goto_synthesizer_parse_options.h"

#include <chrono>
#include <fstream>
#include <iostream>
#include <memory>

#include "util/expr.h"
#include "util/irep.h"

size_t smt_time;
float sum_rate = 0;
size_t num_rate = 0;

size_t count_smt_reject = 0;
size_t count_cbmc_reject = 0;

std::string expr2smtstring(const exprt &expr, size_t index_postfix)
{
  std::string result = "UNDEFINED_OP" + expr.pretty();
  if(expr.id() == ID_and)
  {
    result = "(and " + expr2smtstring(expr.operands()[0], index_postfix) + " " +
             expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_plus)
  {
    result = "(+ " + expr2smtstring(expr.operands()[0], index_postfix) + " " +
             expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_typecast)
  {
    result = expr2smtstring(expr.operands()[0], index_postfix);
  }
  if(expr.id() == ID_loop_entry)
  {
    result = "LOOP_ENTRY_" + expr2smtstring(expr.operands()[0], index_postfix);
  }

  if(expr.id() == ID_constant)
  {
    result = id2string(to_constant_expr(expr).get_value());
  }
  if(expr.id() == ID_symbol)
  {
    result = from_expr(expr) + "_" + std::to_string(index_postfix);
  }
  if(expr.id() == ID_pointer_object)
  {
    result = "1";
  }
  if(expr.id() == ID_pointer_offset)
  {
    result = "OFFSET_" + expr2smtstring(expr.operands()[0], index_postfix);
  }
  if(expr.id() == ID_object_size)
  {
    result = "SIZE_" + expr2smtstring(expr.operands()[0], index_postfix);
  }
  if(expr.id() == ID_le)
  {
    result = "(<= " + expr2smtstring(expr.operands()[0], index_postfix) + " " +
             expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_ge)
  {
    result = "(>= " + expr2smtstring(expr.operands()[0], index_postfix) + " " +
             expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_lt)
  {
    result = "(< " + expr2smtstring(expr.operands()[0], index_postfix) + " " +
             expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_gt)
  {
    result = "(> " + expr2smtstring(expr.operands()[0], index_postfix) + " " +
             expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_equal)
  {
    result = "(= " + expr2smtstring(expr.operands()[0], index_postfix) + " " +
             expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  return result;
}

std::string get_decls(const cext &cex, size_t index_postfix)
{
  std::string result = "";
  for(auto expr : cex.live_lhs)
  {
    if(expr.type().id() == ID_pointer)
    {
      result += "(declare-fun OFFSET_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= OFFSET_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " " +
                cex.pointer_offsets.at(from_expr(expr)) + "))\n";

      result += "(declare-fun OFFSET_LOOP_ENTRY_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= OFFSET_LOOP_ENTRY_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " " +
                cex.loop_entry_offsets.at(from_expr(expr)) + "))\n";

      result += "(declare-fun SIZE_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= SIZE_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " " +
                cex.object_sizes.at(from_expr(expr)) + "))\n";
    }
    else
    {
      result += "(declare-fun " + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= " + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " " + cex.lhs_eval.at(expr) +
                "))\n";
      result += "(declare-fun LOOP_ENTRY_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= LOOP_ENTRY_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " " +
                cex.loop_entry_eval.at(from_expr(expr)) + "))\n";
    }
  }
  return result;
}

std::string get_loop_entry_decls(const cext &cex, size_t index_postfix)
{
  std::string result = "";
  for(auto expr : cex.live_lhs)
  {
    if(expr.type().id() == ID_pointer)
    {
      result += "(declare-fun OFFSET_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= OFFSET_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " " +
                cex.loop_entry_offsets.at(from_expr(expr)) + "))\n";

      result += "(declare-fun OFFSET_LOOP_ENTRY_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= OFFSET_LOOP_ENTRY_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " " +
                cex.loop_entry_offsets.at(from_expr(expr)) + "))\n";

      result += "(declare-fun SIZE_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= SIZE_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " " +
                cex.object_sizes.at(from_expr(expr)) + "))\n";
    }
    else
    {
      result += "(declare-fun " + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= " + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " " +
                cex.loop_entry_eval.at(from_expr(expr)) + "))\n";
      result += "(declare-fun LOOP_ENTRY_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= LOOP_ENTRY_" + from_expr(expr) + "_" +
                std::to_string(index_postfix) + " " +
                cex.loop_entry_eval.at(from_expr(expr)) + "))\n";
    }
  }
  return result;
}

bool simple_enumeratort::quick_verify(const exprt &candidate, const cext &cex)
{
  size_t index_cex = 1;

  std::string declstring = "";
  std::string smtstring = "";
  for(cext neg_test : neg_tests)
  {
    if(index_cex == 1)
    {
      declstring += get_loop_entry_decls(neg_test, 0);
      smtstring += "(assert " + expr2smtstring(candidate, 0) + ")\n";
    }

    declstring += get_decls(neg_test, index_cex);
    smtstring +=
      "(assert (not " + expr2smtstring(candidate, index_cex) + "))\n";
    index_cex++;
  }

  std::string query = declstring + smtstring + "(check-sat)";
  std::cout << query << "\n";
  if(smtstring.find("UNDEFINED_OP") != std::string::npos)
    return false;

  temporary_filet temp_file_problem("smt2_dec_problem_", ""),
    temp_file_stdout("smt2_dec_stdout_", ""),
    temp_file_stderr("smt2_dec_stderr_", "");

  const auto write_problem_to_file = [&](std::ofstream problem_out)
  { problem_out << query; };
  write_problem_to_file(std::ofstream(
    temp_file_problem(), std::ios_base::out | std::ios_base::trunc));

  std::vector<std::string> argv;
  std::string stdin_filename;

  argv = {"cvc4", "-L", "smt2", temp_file_problem()};

  std::chrono::steady_clock::time_point begin =
    std::chrono::steady_clock::now();
  int res =
    run(argv[0], argv, stdin_filename, temp_file_stdout(), temp_file_stderr());
  std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();

  if(res < 0)
    return false;

  // Create a text string, which is used to output the text file
  std::string myText;
  std::ifstream MyReadFile(temp_file_stdout());

  std::cout << (std::chrono::duration_cast<std::chrono::microseconds>(
                  end - begin)
                  .count())
            << "\n";

  smt_time =
    std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();

  while(getline(MyReadFile, myText))
  {
    // Output the text from the file
    std::cout << myText << "\n";
    return (myText.find("unsat") != std::string::npos);
  }
  return false;
}

void recursive_generator_placeholdert::set_size(size_t new_size)
{
  if(new_size > 0)
  {
    actual_generator = factory->instantiate_placeholder(*this);
    actual_generator->set_size(new_size);
  }
  else
  {
    leaf_geneartort non_g = leaf_geneartort(exprst(), "None");
    actual_generator = &non_g;
  }
}

void simple_enumeratort::test_geneartors(size_t num_var, size_t size_term)
{
  recursive_geneartor_factoryt factory = recursive_geneartor_factoryt();
  recursive_generator_placeholdert start_bool_ph =
    factory.make_placeholder("StartBool");
  recursive_generator_placeholdert start_ph = factory.make_placeholder("Start");

  exprst leafexprs = exprst();
  for(int i = 0; i < num_var; i++)
  {
    leafexprs.push_back(symbol_exprt("a" + std::to_string(i), size_type()));
  }

  generatorst start_args = generatorst();
  leaf_geneartort leaf_g = leaf_geneartort(leafexprs);
  start_args.push_back(&leaf_g);
  binary_functional_generatort plus_g =
    binary_functional_generatort(ID_plus, start_ph, start_ph);
  start_args.push_back(&plus_g);

  generatorst start_bool_args = generatorst();
  binary_functional_generatort and_g =
    binary_functional_generatort(ID_and, start_bool_ph, start_bool_ph);
  start_bool_args.push_back(&and_g);
  binary_functional_generatort equal_g =
    binary_functional_generatort(ID_equal, start_ph, start_ph);
  start_bool_args.push_back(&equal_g);
  binary_functional_generatort le_g =
    binary_functional_generatort(ID_le, start_ph, start_ph);
  start_bool_args.push_back(&le_g);
  binary_functional_generatort lt_g =
    binary_functional_generatort(ID_lt, start_ph, start_ph);
  start_bool_args.push_back(&lt_g);

  recursive_generator_placeholdert start_g =
    factory.make_generator("Start", start_args);
  recursive_generator_placeholdert start_bool_g =
    factory.make_generator("StartBool", start_bool_args);

  start_bool_g.set_size(size_term);
  std::cout << num_var << " : " << size_term << " : "
            << start_bool_g.generate().size() << "\n";
}

bool simple_enumeratort::enumerate()
{
  return true;
}
bool simple_enumeratort::enumerate_deprecated()
{
  recursive_geneartor_factoryt factory = recursive_geneartor_factoryt();
  recursive_generator_placeholdert start_bool_ph =
    factory.make_placeholder("StartBool");
  recursive_generator_placeholdert start_ph = factory.make_placeholder("Start");

  exprst leafexprs = exprst();
  for(auto e : parse_option.terminal_symbols)
  {
    leafexprs.push_back(e);
    std::cout << from_expr(e) << "\n";
  }

  generatorst start_args = generatorst();
  leaf_geneartort leaf_g = leaf_geneartort(leafexprs);
  start_args.push_back(&leaf_g);
  binary_functional_generatort plus_g =
    binary_functional_generatort(ID_plus, start_ph, start_ph);
  start_args.push_back(&plus_g);

  generatorst start_bool_args = generatorst();
  binary_functional_generatort and_g =
    binary_functional_generatort(ID_and, start_bool_ph, start_bool_ph);
  start_bool_args.push_back(&and_g);
  binary_functional_generatort equal_g =
    binary_functional_generatort(ID_equal, start_ph, start_ph);
  start_bool_args.push_back(&equal_g);
  binary_functional_generatort le_g =
    binary_functional_generatort(ID_le, start_ph, start_ph);
  start_bool_args.push_back(&le_g);
  binary_functional_generatort lt_g =
    binary_functional_generatort(ID_lt, start_ph, start_ph);
  start_bool_args.push_back(&lt_g);

  recursive_generator_placeholdert start_g =
    factory.make_generator("Start", start_args);
  recursive_generator_placeholdert start_bool_g =
    factory.make_generator("StartBool", start_bool_args);

  size_t size_bound = 0;
  size_t seen_terms = 0;
  while(true)
  {
    size_bound++;
    start_bool_g.set_size(size_bound);
    for(auto candidate : start_bool_g.generate())
    {
      seen_terms++;
      candidate = and_exprt(first_candidate, candidate);
      std::cout << "Candidate: " << from_expr(candidate) << "\n";
      if(quick_verify(candidate, neg_test))
      {
        count_smt_reject++;
        continue;
      }

      cext new_cex;

      simple_verifiert v(parse_option, ui_message_handler);
      if(v.verify(candidate))
      {
        std::cout << "Candidate: " << from_expr(candidate) << "\n";
        std::cout << "result : "
                  << "PASS"
                  << "\n";

        return true;
      }
      else
      {
        new_cex = v.return_cex;
      }

      neg_tests.push_back(new_cex);
      count_cbmc_reject++;
      std::cout << "rate : " << count_smt_reject << " / " << seen_terms << "\n";
    }
  }
  return true;
}

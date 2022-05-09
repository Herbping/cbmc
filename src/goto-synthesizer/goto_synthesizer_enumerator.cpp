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
#include <util/c_types.h>
#include <util/run.h>
#include <util/tempfile.h>

#include <langapi/language_util.h>

#include <fstream>
#include <iostream>
#include <chrono>
#include <memory>

size_t smt_time;
float sum_rate = 0;
size_t num_rate = 0;

size_t count_smt_reject = 0;
size_t count_cbmc_reject = 0;

std::string expr2smtstring(const exprt &expr, size_t index_postfix)
{
  std::string result = "UNDEFINED_OP" + expr.pretty();
  if(expr.id() == ID_and){
    result = "(and " + expr2smtstring(expr.operands()[0], index_postfix) + " " + expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_plus){
    result = "(+ " + expr2smtstring(expr.operands()[0], index_postfix) + " " + expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_typecast)
  {
    result = expr2smtstring(expr.operands()[0], index_postfix);
  }
  if (expr.id() == ID_loop_entry)
  {
    result = "LOOP_ENTRY_" + expr2smtstring(expr.operands()[0], index_postfix);
  }

  if(expr.id() == ID_constant){
    result = id2string(to_constant_expr(expr).get_value());
  }
  if(expr.id() == ID_symbol){
    result = from_expr(expr) + "_" + std::to_string(index_postfix) ;
  }
  if(expr.id() == ID_pointer_object){
    result = "1";
  }
  if(expr.id() == ID_pointer_offset){
    result = "OFFSET_"+expr2smtstring(expr.operands()[0], index_postfix);
  }
  if(expr.id() == ID_object_size){
    result = "SIZE_"+expr2smtstring(expr.operands()[0], index_postfix);
  }
  if(expr.id() == ID_le){
    result = "(<= " + expr2smtstring(expr.operands()[0], index_postfix) + " " + expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_ge){
    result = "(>= " + expr2smtstring(expr.operands()[0], index_postfix) + " " + expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_lt){
    result = "(< " + expr2smtstring(expr.operands()[0], index_postfix) + " " + expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_gt){
    result = "(> " + expr2smtstring(expr.operands()[0], index_postfix) + " " + expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  if(expr.id() == ID_equal){
    result = "(= " + expr2smtstring(expr.operands()[0], index_postfix) + " " + expr2smtstring(expr.operands()[1], index_postfix) + ")";
  }
  return result;
}

std::string get_decls(const cext &cex, size_t index_postfix)
{
  std::string result = "";
  for(auto expr: cex.live_lhs){
    if(expr.type().id() == ID_pointer){
      result += "(declare-fun OFFSET_"+ from_expr(expr) + "_" + std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= OFFSET_"+ from_expr(expr) + "_" + std::to_string(index_postfix) + " " + cex.pointer_offsets.at(from_expr(expr)) + "))\n";

      result += "(declare-fun OFFSET_LOOP_ENTRY_"+ from_expr(expr) + "_" + std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= OFFSET_LOOP_ENTRY_"+ from_expr(expr) + "_" + std::to_string(index_postfix) + " " + cex.loop_entry_offsets.at(from_expr(expr)) + "))\n";
      
      result += "(declare-fun SIZE_" + from_expr(expr) + "_" + std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= SIZE_" + from_expr(expr) + "_" + std::to_string(index_postfix) + " " + cex.object_sizes.at(from_expr(expr)) + "))\n";
    }else
    {
      result += "(declare-fun " + from_expr(expr) + "_" + std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= " + from_expr(expr) + "_" + std::to_string(index_postfix) + " " + cex.lhs_eval.at(expr) + "))\n";
      result += "(declare-fun LOOP_ENTRY_" + from_expr(expr) + "_" + std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= LOOP_ENTRY_" + from_expr(expr) + "_" + std::to_string(index_postfix) + " " + cex.loop_entry_eval.at(from_expr(expr)) + "))\n";
    }
  }
  return result;
}

std::string get_loop_entry_decls(const cext &cex, size_t index_postfix)
{
  std::string result = "";
  for(auto expr: cex.live_lhs){
    if(expr.type().id() == ID_pointer){
      result += "(declare-fun OFFSET_"+ from_expr(expr) + "_" + std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= OFFSET_"+ from_expr(expr) + "_" + std::to_string(index_postfix) + " " + cex.loop_entry_offsets.at(from_expr(expr)) + "))\n";

      result += "(declare-fun OFFSET_LOOP_ENTRY_"+ from_expr(expr) + "_" + std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= OFFSET_LOOP_ENTRY_"+ from_expr(expr) + "_" + std::to_string(index_postfix) + " " + cex.loop_entry_offsets.at(from_expr(expr)) + "))\n";
      
      result += "(declare-fun SIZE_" + from_expr(expr) + "_" + std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= SIZE_" + from_expr(expr) + "_" + std::to_string(index_postfix) + " " + cex.object_sizes.at(from_expr(expr)) + "))\n";
    }else
    {
      result += "(declare-fun " + from_expr(expr) + "_" + std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= " + from_expr(expr) + "_" + std::to_string(index_postfix) + " " + cex.loop_entry_eval.at(from_expr(expr)) + "))\n";
      result += "(declare-fun LOOP_ENTRY_" + from_expr(expr) + "_" + std::to_string(index_postfix) + " () Int)\n";
      result += "(assert (= LOOP_ENTRY_" + from_expr(expr) + "_" + std::to_string(index_postfix) + " " + cex.loop_entry_eval.at(from_expr(expr)) + "))\n";
    }
  }
  return result;
}

bool simple_enumeratort::quick_verify(const exprt &candidate, const cext &cex)
{
  size_t index_cex = 1;

  std::string declstring = "";
  std::string smtstring = ""; 
  for (cext neg_test : neg_tests)
  {
    if (index_cex == 1)
    {
      declstring += get_loop_entry_decls(neg_test, 0);
      smtstring += "(assert " + expr2smtstring(candidate, 0) + ")\n";
    }

    declstring += get_decls(neg_test, index_cex);
    smtstring += "(assert (not " + expr2smtstring(candidate, index_cex) + "))\n";
    index_cex++;
  }

  std::string query = declstring + smtstring + "(check-sat)";
  //std::cout<< "Candidate for quick check: " << from_expr(candidate) <<"\n";
  std::cout<< query <<"\n";
  if(smtstring.find("UNDEFINED_OP") != std::string::npos)
    return false;

  temporary_filet temp_file_problem("smt2_dec_problem_", ""),
    temp_file_stdout("smt2_dec_stdout_", ""),
    temp_file_stderr("smt2_dec_stderr_", "");

  const auto write_problem_to_file = [&](std::ofstream problem_out) {
    problem_out << query;
  };
  write_problem_to_file(std::ofstream(
    temp_file_problem(), std::ios_base::out | std::ios_base::trunc));

  std::vector<std::string> argv;
  std::string stdin_filename;

  argv = {"cvc4", "-L", "smt2", temp_file_problem()};

  //std::cout << query << "\n";
  std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
  int res = run(argv[0], argv, stdin_filename, temp_file_stdout(), temp_file_stderr());
  std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();


  if(res <0)
    return false;

  // Create a text string, which is used to output the text file
  std::string myText;
  std::ifstream MyReadFile(temp_file_stdout());


  std::cout << (std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count()) << "\n";

  smt_time =  std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
  // Use a while loop together with the getline() function to read the file line by line
  while (getline (MyReadFile, myText)) {
    // Output the text from the file
    std::cout << myText << "\n";
    return (myText.find("unsat") != std::string::npos);
  }
  return false;
}

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

void recursive_generator_placeholdert::set_size(size_t new_size)
  {
    if (new_size > 0)
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

void test_geneartors()
{
  recursive_geneartor_factoryt factory = recursive_geneartor_factoryt();
  recursive_generator_placeholdert start_bool_ph = factory.make_placeholder("StartBool");
  recursive_generator_placeholdert start_ph = factory.make_placeholder("Start");

  exprst leafexprs = exprst();
  leafexprs.push_back(symbol_exprt("a", size_type()));
  leafexprs.push_back(symbol_exprt("b", size_type()));
  leafexprs.push_back(symbol_exprt("c", size_type()));
  leafexprs.push_back(symbol_exprt("d", size_type()));
  

  generatorst start_args = generatorst();
  leaf_geneartort leaf_g = leaf_geneartort(leafexprs);
  start_args.push_back(&leaf_g);
  binary_functional_generatort plus_g = binary_functional_generatort(ID_plus, start_ph, start_ph);
  start_args.push_back(&plus_g);

  generatorst start_bool_args = generatorst();
  binary_functional_generatort and_g = binary_functional_generatort(ID_and, start_bool_ph, start_bool_ph);
  start_bool_args.push_back(&and_g);
  binary_functional_generatort equal_g = binary_functional_generatort(ID_equal, start_ph, start_ph);
  start_bool_args.push_back(&equal_g);
  binary_functional_generatort le_g = binary_functional_generatort(ID_le, start_ph, start_ph);
  start_bool_args.push_back(&le_g);
  binary_functional_generatort lt_g = binary_functional_generatort(ID_lt, start_ph, start_ph);
  start_bool_args.push_back(&lt_g);

  recursive_generator_placeholdert start_g = factory.make_generator("Start", start_args);
  recursive_generator_placeholdert start_bool_g = factory.make_generator("StartBool", start_bool_args);

  start_bool_g.set_size(11);
  //start_g.set_size(13);
  size_t i = 0;
  for (auto e : start_bool_g.generate())
  {
    i++;
    std::cout << from_expr(e) << "\n";
  }
  std::cout << i << "\n";
}


bool simple_enumeratort::enumerate()
{
  recursive_geneartor_factoryt factory = recursive_geneartor_factoryt();
  recursive_generator_placeholdert start_bool_ph = factory.make_placeholder("StartBool");
  recursive_generator_placeholdert start_ph = factory.make_placeholder("Start");

  exprst leafexprs = exprst();
  for (auto e : parse_option.terminal_symbols)
  {
    leafexprs.push_back(e);
    std::cout << from_expr(e) << "\n";
  }

  generatorst start_args = generatorst();
  leaf_geneartort leaf_g = leaf_geneartort(leafexprs);
  start_args.push_back(&leaf_g);
  binary_functional_generatort plus_g = binary_functional_generatort(ID_plus, start_ph, start_ph);
  start_args.push_back(&plus_g);

  generatorst start_bool_args = generatorst();
  binary_functional_generatort and_g = binary_functional_generatort(ID_and, start_bool_ph, start_bool_ph);
  start_bool_args.push_back(&and_g);
  binary_functional_generatort equal_g = binary_functional_generatort(ID_equal, start_ph, start_ph);
  start_bool_args.push_back(&equal_g);
  binary_functional_generatort le_g = binary_functional_generatort(ID_le, start_ph, start_ph);
  start_bool_args.push_back(&le_g);
  binary_functional_generatort lt_g = binary_functional_generatort(ID_lt, start_ph, start_ph);
  start_bool_args.push_back(&lt_g);

  recursive_generator_placeholdert start_g = factory.make_generator("Start", start_args);
  recursive_generator_placeholdert start_bool_g = factory.make_generator("StartBool", start_bool_args);

  size_t size_bound = 0;
  size_t seen_terms = 0;
  while (true)
  {
    size_bound++;
    start_bool_g.set_size(size_bound);
    for (auto candidate : start_bool_g.generate())
    {
      seen_terms++;
      candidate = and_exprt(first_candidate, candidate);
      std::cout<< "Candidate: " << from_expr(candidate) <<"\n";
      if(quick_verify(candidate, neg_test))
      {
        count_smt_reject++;
        continue;
      }

      cext new_cex;

      simple_verifiert v(parse_option, ui_message_handler);
      if(v.verify(candidate))
      {
        std::cout << "Candidate: " << from_expr(candidate) <<"\n";
        std::cout <<  "result : " << "PASS" << "\n";

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

bool simple_enumeratort::enumerate_unused()
{
  test_geneartors();
  return true;

  std::deque<exprt> current_partial_terms;

  // number of clauses in the invariant
  // depth of each clause
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
      exprt skeleton = first_candidate;
      for(int j = 0; j < num_clauses; j++)
      {
        if(i > j)
        {
          skeleton = and_exprt(skeleton, sterm(ID_lt, size_eterm));
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
          if(!is_partial(partial_term))
          {
            if(quick_verify(partial_term, neg_test))
              continue;

            
            std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
            cext new_cex;
            if(parse_option.call_back(partial_term))
            {
              return true;
            }
            count_cbmc_reject++;

            std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
            sum_rate += (float)(std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count())/(float)smt_time;
            num_rate++;
          }
          // TODO delete here later
          //return true;
        }
      }
    }
  }
}
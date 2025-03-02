/*******************************************************************\

Module: Parser utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Parser utilities

#ifndef CPROVER_UTIL_PARSER_H
#define CPROVER_UTIL_PARSER_H

#include "expr.h"
#include "message.h"

#include <filesystem>
#include <iosfwd>
#include <limits>
#include <string>
#include <vector>

class parsert
{
public:
  std::istream *in;

  std::string this_line, last_line;

  std::vector<exprt> stack;

  explicit parsert(message_handlert &message_handler)
    : in(nullptr),
      log(message_handler),
      line_no(0),
      previous_line_no(std::numeric_limits<unsigned int>::max()),
      column(1)
  {
  }

  virtual ~parsert() { }

  // The following are for the benefit of the scanner

  bool read(char &ch)
  {
    if(!in->read(&ch, 1))
      return false;

    if(ch=='\n')
    {
      last_line.swap(this_line);
      this_line.clear();
    }
    else
      this_line+=ch;

    return true;
  }

  virtual bool parse()=0;

  bool eof()
  {
    return in->eof();
  }

  void parse_error(
    const std::string &message,
    const std::string &before);

  void inc_line_no()
  {
    ++line_no;
    column=1;
  }

  void set_line_no(unsigned _line_no)
  {
    line_no=_line_no;
  }

  void set_file(const irep_idt &file)
  {
    _source_location.set_file(file);
    _source_location.set_working_directory(
      std::filesystem::current_path().string());
  }

  irep_idt get_file() const
  {
    return _source_location.get_file();
  }

  unsigned get_line_no() const
  {
    return line_no;
  }

  unsigned get_column() const
  {
    return column;
  }

  void set_column(unsigned _column)
  {
    column=_column;
  }

  const source_locationt &source_location()
  {
    // Only set line number when needed, as this destroys sharing.
    if(previous_line_no!=line_no)
    {
      previous_line_no=line_no;

      // for the case of a file with no newlines
      if(line_no == 0)
        _source_location.set_line(1);
      else
        _source_location.set_line(line_no);
    }

    return _source_location;
  }

  void set_source_location(exprt &e)
  {
    e.add_source_location() = source_location();
  }

  void set_function(const irep_idt &function)
  {
    _source_location.set_function(function);
  }

  void advance_column(unsigned token_width)
  {
    column+=token_width;
  }

protected:
  messaget log;
  source_locationt _source_location;
  unsigned line_no, previous_line_no;
  unsigned column;
};

exprt &_newstack(parsert &parser, unsigned &x);

#define newstack(x) _newstack(PARSER, (x))

#define parser_stack(x) (PARSER.stack[x])
#define stack_expr(x) (PARSER.stack[x])
#define stack_type(x) \
  (static_cast<typet &>(static_cast<irept &>(PARSER.stack[x])))

#define YY_INPUT(buf, result, max_size) \
    do { \
        for(result=0; result<max_size;) \
        { \
          char ch; \
          if(!PARSER.read(ch)) /* NOLINT(readability/braces) */ \
          { \
            if(result==0) \
              result=YY_NULL; \
            break; \
          } \
          \
          if(ch!='\r') /* NOLINT(readability/braces) */ \
          { \
            buf[result++]=ch; \
            if(ch=='\n') /* NOLINT(readability/braces) */ \
            { \
              PARSER.inc_line_no(); \
              break; \
            } \
          } \
        } \
    } while(0)

// The following tracks the column of the token, and is nicely explained here:
// http://oreilly.com/linux/excerpts/9780596155971/error-reporting-recovery.html

#define YY_USER_ACTION PARSER.advance_column(yyleng);

#endif // CPROVER_UTIL_PARSER_H

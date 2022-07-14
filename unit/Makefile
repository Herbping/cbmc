.PHONY: all cprover.dir test testing-utils-clean

# Source files for test utilities
SRC = unit_tests.cpp \
      # Empty last line

# Test source files
SRC += util/symbol_table.cpp \
       util/symbol.cpp \
       # Empty last line

ifeq ($(OS),Windows_NT)
    detected_OS := Windows
else
    detected_OS := $(shell sh -c 'uname 2>/dev/null || echo Unknown')
endif

ifeq ($(detected_OS),Linux)
  ifneq ($(WITH_MEMORY_ANALYZER),0)
    # only set if it wasn't explicitly unset
    WITH_MEMORY_ANALYZER=1
  endif
endif

ifeq ($(WITH_MEMORY_ANALYZER),1)
  SRC += memory-analyzer/gdb_api.cpp
endif

INCLUDES= -I ../src/ -I.

CPROVER_DIR = .
include ../src/config.inc
include ../src/common

cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

testing-utils/testing-utils$(LIBEXT): cprover.dir
	$(MAKE) $(MAKEARGS) -C testing-utils

testing-utils-clean:
	$(MAKE) $(MAKEARGS) -C testing-utils clean

# We need to link bmc.o to the unit test, so here's everything it depends on...
BMC_DEPS =../src/cbmc/c_test_input_generator$(OBJEXT) \
          ../src/cbmc/cbmc_languages$(OBJEXT) \
          ../src/cbmc/cbmc_parse_options$(OBJEXT) \
          ../src/goto-cc/armcc_cmdline$(OBJEXT) \
          ../src/goto-cc/goto_cc_cmdline$(OBJEXT) \
          ../src/goto-instrument/source_lines$(OBJEXT) \
          ../src/goto-instrument/cover$(OBJEXT) \
          ../src/goto-instrument/cover_basic_blocks$(OBJEXT) \
          ../src/goto-instrument/cover_filter$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_assume$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_branch$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_condition$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_decision$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_location$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_mcdc$(OBJEXT) \
          ../src/goto-instrument/cover_instrument_other$(OBJEXT) \
          ../src/goto-instrument/cover_util$(OBJEXT) \
          ../src/goto-instrument/goto_program2code$(OBJEXT) \
          ../src/goto-instrument/reachability_slicer$(OBJEXT) \
          ../src/goto-instrument/nondet_static$(OBJEXT) \
          ../src/goto-instrument/full_slicer$(OBJEXT) \
          ../src/goto-instrument/unwindset$(OBJEXT) \
          ../src/xmllang/xmllang$(LIBEXT) \
          ../src/goto-symex/goto-symex$(LIBEXT) \
          ../src/jsil/jsil$(LIBEXT) \
          # Empty last line
#
CPROVER_LIBS =../src/ansi-c/ansi-c$(LIBEXT) \
              ../src/cpp/cpp$(LIBEXT) \
              ../src/json/json$(LIBEXT) \
              ../src/json-symtab-language/json-symtab-language$(LIBEXT) \
              ../src/linking/linking$(LIBEXT) \
              ../src/util/util$(LIBEXT) \
              ../src/big-int/big-int$(LIBEXT) \
              ../src/goto-checker/goto-checker$(LIBEXT) \
              ../src/goto-programs/goto-programs$(LIBEXT) \
              ../src/pointer-analysis/pointer-analysis$(LIBEXT) \
              ../src/langapi/langapi$(LIBEXT) \
              ../src/assembler/assembler$(LIBEXT) \
              ../src/analyses/analyses$(LIBEXT) \
              ../src/solvers/solvers$(LIBEXT) \
              ../src/statement-list/statement-list$(LIBEXT) \
              $(BMC_DEPS)
              # Empty last line

OBJ += $(CPROVER_LIBS) testing-utils/testing-utils$(LIBEXT)

CATCH_TEST = unit_tests$(EXEEXT)
EXCLUDED_TESTS=expr_undefined_casts.cpp
ifneq ($(WITH_MEMORY_ANALYZER),1)
EXCLUDED_TESTS += gdb_api.cpp
endif
ifeq ($(MINISAT2),)
EXCLUDED_TESTS += satcheck_minisat2.cpp
endif
ifeq ($(CADICAL),)
EXCLUDED_TESTS += satcheck_cadical.cpp
endif

N_CATCH_TESTS = $(shell ./count_tests.py --exclude-files "$(EXCLUDED_TESTS)")

memory-analyzer/input.inc: memory-analyzer/input.txt
	../src/ansi-c/file_converter$(EXEEXT) $< > $@

memory-analyzer/test.inc: memory-analyzer/test.c
	../src/ansi-c/file_converter$(EXEEXT) $< > $@

memory-analyzer/gdb_api$(OBJEXT): memory-analyzer/input.inc memory-analyzer/test.inc

CLEANFILES = $(CATCH_TEST) testing-utils/testing-utils$(LIBEXT) \
             memory-analyzer/input.inc memory-analyzer/test.inc

# only add a dependency for libraries to avoid triggering implicit rules, which
# would cause unnecessary rebuilds
$(filter %$(LIBEXT), $(CPROVER_LIBS)): cprover.dir

all: $(CATCH_TEST)

clean: testing-utils-clean

test: $(CATCH_TEST)
	# Include hidden tests by specifying "*,[.]" for tests to count
	if ! ./$(CATCH_TEST) "*,[.]" -l | grep -q "^$(N_CATCH_TESTS) matching test cases" ; then \
		./$(CATCH_TEST) "*,[.]" -l ; fi
	./$(CATCH_TEST) ${TAGS}


###############################################################################

unit_tests$(EXEEXT): $(OBJ)
	$(LINKBIN)

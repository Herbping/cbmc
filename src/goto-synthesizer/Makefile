SRC = goto_synthesizer_enumerator.cpp \
      goto_synthesizer_verifier.cpp \
      utils.cpp \
      goto_synthesizer_parse_options.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../json/json$(LIBEXT) \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = goto-synthesizer$(EXEEXT) 

all: goto-synthesizer$(EXEEXT)

###############################################################################

goto-synthesizer$(EXEEXT): $(OBJ)
	$(LINKLIB)

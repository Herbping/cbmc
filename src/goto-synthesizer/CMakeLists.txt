# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/goto_synthesizer_main.cpp
)
add_library(goto-synthesizer-lib ${sources})

generic_includes(goto-synthesizer-lib)

target_link_libraries(goto-synthesizer-lib
    ansi-c
    cpp
    linking
    big-int
    goto-programs
    goto-instrument-lib
    goto-symex
    assembler
    pointer-analysis
    analyses
    langapi
    xml
    util
    json
    solvers
)

add_if_library(goto-synthesizer-lib glpk)

# Executable
add_executable(goto-synthesizer goto_synthesizer_main.cpp)
target_link_libraries(goto-synthesizer goto-synthesizer-lib)
install(TARGETS goto-synthesizer DESTINATION ${CMAKE_INSTALL_BINDIR})

file(GLOB_RECURSE sources "*.cpp" "*.h")
add_executable(goto-synthesizer ${sources})
generic_includes(goto-synthesizer)

target_link_libraries(goto-synthesizer
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
install(TARGETS goto-synthesizer DESTINATION ${CMAKE_INSTALL_BINDIR})

add_subdirectory(regression)
add_subdirectory(src)
add_subdirectory(unit)

cprover_default_properties(
    java_bytecode
    jbmc
    jbmc-lib
    janalyzer
    janalyzer-lib
    jdiff
    jdiff-lib
    java-testing-utils
    java-unit
    miniz
)

# java models library
find_program(MAVEN_PROGRAM mvn REQUIRED)

file(GLOB_RECURSE java_models_sources "lib/java-models-library/src/*.java")

add_custom_command(OUTPUT "${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library/target/core-models.jar"
    COMMAND ${MAVEN_PROGRAM} --quiet -Dmaven.test.skip=true package
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library
    DEPENDS ${java_models_sources}
)

add_custom_target(java-models-library ALL
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library/target/core-models.jar"
)

install(
    FILES
        "${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library/target/core-models.jar"
        "${CMAKE_CURRENT_SOURCE_DIR}/lib/java-models-library/target/cprover-api.jar"
        DESTINATION ${CMAKE_INSTALL_LIBDIR}
)

# java regression tests
file(GLOB_RECURSE java_regression_sources "regression/**/*.java,regression/**/*.kt,regression/**/*.j,regression/**/pom.xml")
file(GLOB java_regression_test_dirs LIST_DIRECTORIES true "regression/*/*")
foreach(dir ${java_regression_test_dirs})
    # TODO: remove the last condition as soon as jbmc/deterministic_assignments_json has been converted
    IF(IS_DIRECTORY ${dir} AND EXISTS "${dir}/pom.xml" AND NOT EXISTS "${dir}/Foo.class")
        list(APPEND java_regression_compiled_sources "${dir}/target")
    ENDIF()
endforeach()

add_custom_command(OUTPUT ${java_regression_compiled_sources}
    COMMAND ${MAVEN_PROGRAM} --quiet clean package -T1C
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/regression
    DEPENDS ${java_regression_sources}
)

add_custom_target(java-regression ALL
    DEPENDS ${java_regression_compiled_sources}
)

add_dependencies(java-regression java-models-library)

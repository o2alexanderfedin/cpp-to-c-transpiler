cmake_minimum_required(VERSION 3.20)
project(acsl_annotation_tests C CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Set LLVM/Clang paths (using Homebrew installation)
set(LLVM_DIR "/opt/homebrew/opt/llvm/lib/cmake/llvm")
set(Clang_DIR "/opt/homebrew/opt/llvm/lib/cmake/clang")

# Find LLVM/Clang
find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# Fetch Google Test
include(FetchContent)
FetchContent_Declare(
  googletest
  GIT_REPOSITORY https://github.com/google/googletest.git
  GIT_TAG v1.14.0
)
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

# Include directories
include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${CLANG_INCLUDE_DIRS})
include_directories(${CMAKE_SOURCE_DIR}/../../../include)
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

# ACSL Statement Annotator Tests (18 tests)
add_executable(test_acsl_statement_annotator
    ../ACSLStatementAnnotatorTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLStatementAnnotator.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLGenerator.cpp
)

target_link_libraries(test_acsl_statement_annotator
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# ACSL Function Annotator Tests (15 tests)
add_executable(test_acsl_function_annotator
    ../ACSLFunctionAnnotatorTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLFunctionAnnotator.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLMemoryPredicateAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLGenerator.cpp
)

target_link_libraries(test_acsl_function_annotator
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# ACSL Memory Predicate Analyzer Tests (12 tests)
add_executable(test_acsl_memory_predicate_analyzer
    ../ACSLMemoryPredicateAnalyzerTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLMemoryPredicateAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLGenerator.cpp
)

target_link_libraries(test_acsl_memory_predicate_analyzer
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# ACSL Loop Annotator Tests (12 tests)
add_executable(test_acsl_loop_annotator
    ../ACSLLoopAnnotatorTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLLoopAnnotator.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLGenerator.cpp
)

target_link_libraries(test_acsl_loop_annotator
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# ACSL Ghost Code Injector Tests (10 tests)
add_executable(test_acsl_ghost_code_injector
    ../ACSLGhostCodeInjectorTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLGhostCodeInjector.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLGenerator.cpp
)

target_link_libraries(test_acsl_ghost_code_injector
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# Template Integration Tests (15 tests)
add_executable(test_template_integration
    ../TemplateIntegrationTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/TemplateExtractor.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/TemplateMonomorphizer.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/TemplateInstantiationTracker.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/NameMangler.cpp
)

target_link_libraries(test_template_integration
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# ACSL Class Annotator Tests (10 tests)
add_executable(test_acsl_class_annotator
    ../ACSLClassAnnotatorTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLClassAnnotator.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLGenerator.cpp
)

target_link_libraries(test_acsl_class_annotator
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)


# ACSL Type Invariant Generator Tests (12 tests)
add_executable(test_acsl_type_invariant_generator
    ../ACSLTypeInvariantGeneratorTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLTypeInvariantGenerator.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLGenerator.cpp
)

target_link_libraries(test_acsl_type_invariant_generator
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# ACSL Behavior Annotator Tests (15 tests)
add_executable(test_acsl_behavior_annotator
    ../ACSLBehaviorAnnotatorTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLBehaviorAnnotator.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/ACSLGenerator.cpp
)

target_link_libraries(test_acsl_behavior_annotator
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# Enable testing
enable_testing()
include(GoogleTest)

gtest_discover_tests(test_acsl_statement_annotator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "acsl;annotations;phase-1"
)

gtest_discover_tests(test_acsl_function_annotator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "acsl;annotations;phase-6"
)

gtest_discover_tests(test_acsl_memory_predicate_analyzer
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "acsl;annotations;phase-6"
)

gtest_discover_tests(test_acsl_loop_annotator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "acsl;annotations;phase-6"
)

gtest_discover_tests(test_acsl_ghost_code_injector
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "acsl;ghost-code;phase-4"
)

gtest_discover_tests(test_template_integration
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "template;phase-11"
)

gtest_discover_tests(test_acsl_class_annotator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "acsl;class-annotations;phase-15-02"
)

gtest_discover_tests(test_acsl_type_invariant_generator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "acsl;type-invariants;phase-2"
)

gtest_discover_tests(test_acsl_behavior_annotator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "acsl;behaviors;phase-5"
)

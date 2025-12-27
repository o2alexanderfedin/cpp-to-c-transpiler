# Phase 51: Comparison Operators Integration Tests
# Tests for comprehensive comparison operator overloading support

cmake_minimum_required(VERSION 3.20)
project(comparison_operators_integration_tests C CXX)

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
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

# LLVM/Clang libraries
set(CLANG_LIBS
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# Phase 51: Comparison Operators Integration Tests
add_executable(ComparisonOperatorsIntegrationTest
    ComparisonOperatorsIntegrationTest.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/HandlerContext.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/FunctionHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/VariableHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/ExpressionHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/StatementHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/RecordHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/MethodHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/ConstructorHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/DestructorHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/ComparisonOperatorTranslator.cpp
    ${CMAKE_SOURCE_DIR}/../../src/ArithmeticOperatorTranslator.cpp
    ${CMAKE_SOURCE_DIR}/../../src/NameMangler.cpp
)
target_link_libraries(ComparisonOperatorsIntegrationTest GTest::gtest GTest::gtest_main ${CLANG_LIBS})
target_include_directories(ComparisonOperatorsIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/../../include
    ${CMAKE_SOURCE_DIR}/../../include/handlers
    ${CMAKE_SOURCE_DIR}/../../src
)

# Enable testing
enable_testing()
include(GoogleTest)

# Discover and register tests
gtest_discover_tests(ComparisonOperatorsIntegrationTest
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;comparison_operators;phase51"
)

message(STATUS "Phase 51 Comparison Operators Integration Tests configured:")
message(STATUS "  - ComparisonOperatorsIntegrationTest: 15 tests")
message(STATUS "    * Sorting Category (4 tests): bubble sort, quick sort, insertion sort, stability")
message(STATUS "    * Searching Category (3 tests): binary search, linear search, lower bound")
message(STATUS "    * Container Operations Category (3 tests): sorted insertion, duplicate detection, range query")
message(STATUS "    * Conditional Chains Category (5 tests): chained comparisons, equality chains, logical operators, complex conditionals, ternary")
message(STATUS "  Total: 15 comprehensive integration tests")

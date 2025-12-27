cmake_minimum_required(VERSION 3.20)
project(comparison_operators_tests C CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Use parent project's find_package results if available
if(NOT LLVM_FOUND)
    set(LLVM_DIR "/opt/homebrew/opt/llvm/lib/cmake/llvm")
    set(Clang_DIR "/opt/homebrew/opt/llvm/lib/cmake/clang")
    find_package(LLVM REQUIRED CONFIG)
    find_package(Clang REQUIRED CONFIG)
endif()

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# Fetch Google Test if not already available
if(NOT TARGET GTest::gtest)
    include(FetchContent)
    FetchContent_Declare(
        googletest
        GIT_REPOSITORY https://github.com/google/googletest.git
        GIT_TAG v1.14.0
    )
    set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
    FetchContent_MakeAvailable(googletest)
endif()

# Include directories
include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${CLANG_INCLUDE_DIRS})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

# Test executables for comparison operators
add_executable(test_less_than_operator
    LessThanOperatorTest.cpp
)

add_executable(test_less_than_or_equal_operator
    LessThanOrEqualOperatorTest.cpp
)

add_executable(test_greater_than_operator
    GreaterThanOperatorTest.cpp
)

add_executable(test_greater_than_or_equal_operator
    GreaterThanOrEqualOperatorTest.cpp
)

add_executable(test_equality_operator
    EqualityOperatorTest.cpp
)

add_executable(test_inequality_operator
    InequalityOperatorTest.cpp
)

add_executable(test_logical_not_operator
    LogicalNotOperatorTest.cpp
)

add_executable(test_logical_or_operator
    LogicalOrOperatorTest.cpp
)

# Link libraries - reusable for all test executables
function(link_comparison_test TEST_TARGET)
    target_link_libraries(${TEST_TARGET}
        GTest::gtest
        GTest::gtest_main
        clangTooling
        clangFrontend
        clangBasic
        clangAST
        clangLex
    )
endfunction()

# Link all test executables
link_comparison_test(test_less_than_operator)
link_comparison_test(test_less_than_or_equal_operator)
link_comparison_test(test_greater_than_operator)
link_comparison_test(test_greater_than_or_equal_operator)
link_comparison_test(test_equality_operator)
link_comparison_test(test_inequality_operator)
link_comparison_test(test_logical_not_operator)
link_comparison_test(test_logical_or_operator)

# Enable testing
enable_testing()
include(GoogleTest)

# Register tests with GoogleTest discovery
gtest_discover_tests(test_less_than_operator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;comparison-operators;less-than"
)

gtest_discover_tests(test_less_than_or_equal_operator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;comparison-operators;less-than-or-equal"
)

gtest_discover_tests(test_greater_than_operator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;comparison-operators;greater-than"
)

gtest_discover_tests(test_greater_than_or_equal_operator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;comparison-operators;greater-than-or-equal"
)

gtest_discover_tests(test_equality_operator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;comparison-operators;equality"
)

gtest_discover_tests(test_inequality_operator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;comparison-operators;inequality"
)

gtest_discover_tests(test_logical_not_operator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;comparison-operators;logical-not"
)

gtest_discover_tests(test_logical_or_operator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;comparison-operators;logical-or"
)

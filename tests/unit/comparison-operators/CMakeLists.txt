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
add_executable(test_less_than_or_equal_operator
    LessThanOrEqualOperatorTest.cpp
)

# Link libraries
target_link_libraries(test_less_than_or_equal_operator
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

gtest_discover_tests(test_less_than_or_equal_operator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;comparison-operators;less-than-or-equal"
)

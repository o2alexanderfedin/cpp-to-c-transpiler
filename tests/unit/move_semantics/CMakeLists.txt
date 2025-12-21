cmake_minimum_required(VERSION 3.20)
project(move_semantics_tests C CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Set LLVM/Clang paths (using Homebrew installation)
set(LLVM_DIR "/opt/homebrew/opt/llvm/lib/cmake/llvm")
set(Clang_DIR "/opt/homebrew/opt/llvm/lib/cmake/clang")

# Find LLVM and Clang
find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "Using ClangConfig.cmake in: ${Clang_DIR}")

# Fetch Google Test
include(FetchContent)
FetchContent_Declare(
  googletest
  GIT_REPOSITORY https://github.com/google/googletest.git
  GIT_TAG v1.14.0
)
# For Windows: Prevent overriding the parent project's compiler/linker settings
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

# Include directories
include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${CLANG_INCLUDE_DIRS})
include_directories(${CMAKE_CURRENT_SOURCE_DIR})
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/../../../include)

# Add definitions
add_definitions(${LLVM_DEFINITIONS})
add_definitions(${CLANG_DEFINITIONS})

# LLVM/Clang link components
llvm_map_components_to_libnames(llvm_libs
    support
    core
    irreader
)

# Clang libraries
set(CLANG_LIBS
    clangAST
    clangBasic
    clangDriver
    clangFrontend
    clangRewriteFrontend
    clangSerialization
    clangTooling
    clangParse
    clangSema
    clangAnalysis
    clangEdit
    clangLex
)

# Test executables - one per test file for clarity and parallel execution
# Only building migrated Google Test files
add_executable(test_move_semantic_translator
    MoveSemanticTranslatorTest_gtest.cpp
)

# Link libraries for all tests
set(ALL_TEST_TARGETS
    test_move_semantic_translator
)

foreach(TEST_TARGET ${ALL_TEST_TARGETS})
    target_link_libraries(${TEST_TARGET}
        ${CLANG_LIBS}
        ${llvm_libs}
        GTest::gtest
        GTest::gtest_main
    )
endforeach()

# Enable testing
enable_testing()
include(GoogleTest)

# Discover tests for each executable
gtest_discover_tests(test_move_semantic_translator
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;move_semantics;core"
)

# Summary message
message(STATUS "Move Semantics Test Suite configured with 1 test executable (MoveSemanticTranslatorTest_gtest: 50 tests)")
message(STATUS "NOTE: Other test files require migration to Google Test format")

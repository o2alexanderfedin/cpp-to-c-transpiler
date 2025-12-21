cmake_minimum_required(VERSION 3.20)
project(move_semantics_tests CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

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
add_executable(test_move_semantic_translator
    MoveSemanticTranslatorTest_gtest.cpp
)

add_executable(test_rvalue_ref_parameter
    RvalueRefParameterTest_gtest.cpp
)

add_executable(test_std_move_translation
    StdMoveTranslationTest_gtest.cpp
)

add_executable(test_copy_move_integration
    CopyMoveIntegrationTest_gtest.cpp
)

add_executable(test_move_constructor_translation
    MoveConstructorTranslationTest_gtest.cpp
)

add_executable(test_move_assignment_translation
    MoveAssignmentTranslationTest_gtest.cpp
)

# Link libraries for all tests
set(ALL_TEST_TARGETS
    test_move_semantic_translator
    test_rvalue_ref_parameter
    test_std_move_translation
    test_copy_move_integration
    test_move_constructor_translation
    test_move_assignment_translation
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

gtest_discover_tests(test_rvalue_ref_parameter
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;move_semantics;parameters"
)

gtest_discover_tests(test_std_move_translation
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;move_semantics;std_move"
)

gtest_discover_tests(test_copy_move_integration
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;move_semantics;integration"
)

gtest_discover_tests(test_move_constructor_translation
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;move_semantics;constructor"
)

gtest_discover_tests(test_move_assignment_translation
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;move_semantics;assignment"
)

# Summary message
message(STATUS "Move Semantics Test Suite configured with 6 test executables (~94 tests total)")

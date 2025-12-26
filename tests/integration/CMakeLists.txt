cmake_minimum_required(VERSION 3.20)
project(integration_tests C CXX)

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

# Test executables
add_executable(test_feature_interaction FeatureInteractionTest.cpp)
target_link_libraries(test_feature_interaction GTest::gtest GTest::gtest_main ${CLANG_LIBS})

add_executable(test_feature_combination FeatureCombinationTest.cpp)
target_link_libraries(test_feature_combination GTest::gtest GTest::gtest_main ${CLANG_LIBS})

add_executable(test_edge_cases EdgeCasesTest.cpp)
target_link_libraries(test_edge_cases GTest::gtest GTest::gtest_main ${CLANG_LIBS})

add_executable(test_error_handling ErrorHandlingTest.cpp)
target_link_libraries(test_error_handling GTest::gtest GTest::gtest_main ${CLANG_LIBS})

add_executable(test_error_handling_gtest ErrorHandlingTest_gtest.cpp)
target_link_libraries(test_error_handling_gtest GTest::gtest GTest::gtest_main ${CLANG_LIBS})

add_executable(test_move_semantic_integration MoveSemanticIntegrationTest.cpp)
target_link_libraries(test_move_semantic_integration GTest::gtest GTest::gtest_main ${CLANG_LIBS})

# Phase 42: Pointers and References Integration Tests
add_executable(PointersIntegrationTest handlers/PointersIntegrationTest.cpp)
target_link_libraries(PointersIntegrationTest GTest::gtest GTest::gtest_main ${CLANG_LIBS})
target_include_directories(PointersIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/../../include
    ${CMAKE_SOURCE_DIR}/../../include/handlers
    ${CMAKE_SOURCE_DIR}/../../src
)

# Enable testing
enable_testing()
include(GoogleTest)

# Discover and register tests
gtest_discover_tests(test_feature_interaction)
gtest_discover_tests(test_feature_combination)
gtest_discover_tests(test_edge_cases)
gtest_discover_tests(test_error_handling)
gtest_discover_tests(test_error_handling_gtest)
gtest_discover_tests(test_move_semantic_integration
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;move_semantics;epic18"
)
gtest_discover_tests(PointersIntegrationTest
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;pointers;phase42"
)

message(STATUS "Integration tests configured:")
message(STATUS "  - FeatureInteractionTest: 30 tests")
message(STATUS "  - FeatureCombinationTest: 20 tests")
message(STATUS "  - EdgeCasesTest: 30 tests")
message(STATUS "  - ErrorHandlingTest: 25 tests (legacy)")
message(STATUS "  - ErrorHandlingTest_gtest: 25 tests (Google Test)")
message(STATUS "  - MoveSemanticIntegrationTest: 16 tests (Google Test)")
message(STATUS "  - PointersIntegrationTest: 24 tests (Phase 42)")
message(STATUS "  Total: 170 integration tests")

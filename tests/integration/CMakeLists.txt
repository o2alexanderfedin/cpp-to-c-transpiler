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

# Phase 43: Structs (C-style) Integration Tests
add_executable(StructsIntegrationTest handlers/StructsIntegrationTest.cpp)
target_link_libraries(StructsIntegrationTest GTest::gtest GTest::gtest_main ${CLANG_LIBS})
target_include_directories(StructsIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/../../include
    ${CMAKE_SOURCE_DIR}/../../include/handlers
    ${CMAKE_SOURCE_DIR}/../../src
)

# Phase 44: Classes (C++ classes) Integration Tests
add_executable(ClassesIntegrationTest
    handlers/ClassesIntegrationTest.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/HandlerContext.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/FunctionHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/VariableHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/ExpressionHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/StatementHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/RecordHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/MethodHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/ConstructorHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/DestructorHandler.cpp
)
target_link_libraries(ClassesIntegrationTest GTest::gtest GTest::gtest_main ${CLANG_LIBS})
target_include_directories(ClassesIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/../../include
    ${CMAKE_SOURCE_DIR}/../../include/handlers
    ${CMAKE_SOURCE_DIR}/../../src
)

# Phase 45: Virtual Methods Integration Tests
add_executable(VirtualMethodsIntegrationTest
    handlers/VirtualMethodsIntegrationTest.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/HandlerContext.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/FunctionHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/VariableHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/ExpressionHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/StatementHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/RecordHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/MethodHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/ConstructorHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/DestructorHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VirtualMethodAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VtableGenerator.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VptrInjector.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VtableInitializer.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VirtualCallTranslator.cpp
    ${CMAKE_SOURCE_DIR}/../../src/OverrideResolver.cpp
    ${CMAKE_SOURCE_DIR}/../../src/MethodSignatureHelper.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VirtualInheritanceAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/../../src/helpers/VtableTypedefGenerator.cpp
)
target_link_libraries(VirtualMethodsIntegrationTest GTest::gtest GTest::gtest_main ${CLANG_LIBS})
target_include_directories(VirtualMethodsIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/../../include
    ${CMAKE_SOURCE_DIR}/../../include/handlers
    ${CMAKE_SOURCE_DIR}/../../src
)

# Phase 46: Multiple Inheritance Integration Tests
add_executable(MultipleInheritanceIntegrationTest
    handlers/MultipleInheritanceIntegrationTest.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/HandlerContext.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/FunctionHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/VariableHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/ExpressionHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/StatementHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/RecordHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/MethodHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/ConstructorHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/DestructorHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VirtualMethodAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VtableGenerator.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VptrInjector.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VtableInitializer.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VirtualCallTranslator.cpp
    ${CMAKE_SOURCE_DIR}/../../src/OverrideResolver.cpp
    ${CMAKE_SOURCE_DIR}/../../src/MethodSignatureHelper.cpp
    ${CMAKE_SOURCE_DIR}/../../src/VirtualInheritanceAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/../../src/helpers/VtableTypedefGenerator.cpp
    ${CMAKE_SOURCE_DIR}/../../src/MultipleInheritanceAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/../../src/ThunkGenerator.cpp
    ${CMAKE_SOURCE_DIR}/../../src/BaseOffsetCalculator.cpp
)
target_link_libraries(MultipleInheritanceIntegrationTest GTest::gtest GTest::gtest_main ${CLANG_LIBS})
target_include_directories(MultipleInheritanceIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/../../include
    ${CMAKE_SOURCE_DIR}/../../include/handlers
    ${CMAKE_SOURCE_DIR}/../../src
)

# Phase 47: Scoped Enums Integration Tests
add_executable(EnumIntegrationTest
    handlers/EnumIntegrationTest.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/HandlerContext.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/FunctionHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/VariableHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/ExpressionHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/handlers/StatementHandler.cpp
    ${CMAKE_SOURCE_DIR}/../../src/BaseOffsetCalculator.cpp
)
target_link_libraries(EnumIntegrationTest GTest::gtest GTest::gtest_main ${CLANG_LIBS})
target_include_directories(EnumIntegrationTest PRIVATE
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
gtest_discover_tests(StructsIntegrationTest
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;structs;phase43"
)
gtest_discover_tests(ClassesIntegrationTest
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;classes;phase44"
)
gtest_discover_tests(VirtualMethodsIntegrationTest
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;virtual_methods;phase45"
)
gtest_discover_tests(MultipleInheritanceIntegrationTest
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;multiple_inheritance;phase46"
)
gtest_discover_tests(EnumIntegrationTest
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;enums;phase47"
)

message(STATUS "Integration tests configured:")
message(STATUS "  - FeatureInteractionTest: 30 tests")
message(STATUS "  - FeatureCombinationTest: 20 tests")
message(STATUS "  - EdgeCasesTest: 30 tests")
message(STATUS "  - ErrorHandlingTest: 25 tests (legacy)")
message(STATUS "  - ErrorHandlingTest_gtest: 25 tests (Google Test)")
message(STATUS "  - MoveSemanticIntegrationTest: 16 tests (Google Test)")
message(STATUS "  - PointersIntegrationTest: 24 tests (Phase 42)")
message(STATUS "  - StructsIntegrationTest: 25 tests (Phase 43)")
message(STATUS "  - ClassesIntegrationTest: 35 tests (Phase 44)")
message(STATUS "  - VirtualMethodsIntegrationTest: 35 tests (Phase 45)")
message(STATUS "  - MultipleInheritanceIntegrationTest: 37 tests (Phase 46)")
message(STATUS "  - EnumIntegrationTest: 12 tests (Phase 47)")
message(STATUS "  Total: 314 integration tests")

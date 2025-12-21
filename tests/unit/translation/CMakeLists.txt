cmake_minimum_required(VERSION 3.20)
project(translation_tests C CXX)

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

# Source files from main project
set(PROJECT_SRC_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../../src)

# Collect all source files from src directory
file(GLOB PROJECT_SOURCES
    ${PROJECT_SRC_DIR}/*.cpp
)

# Remove main.cpp and CppToCConsumer.cpp (they have compilation conflicts with tests)
list(FILTER PROJECT_SOURCES EXCLUDE REGEX ".*(main|CppToCConsumer|CppToCFrontendAction)\\.cpp$")

# Test executables - one per test file for clarity and parallel execution
add_executable(test_standalone_function_translation
    StandaloneFunctionTranslationTest_gtest.cpp
    ${PROJECT_SOURCES}
)

add_executable(test_dependency_graph_visualizer
    DependencyGraphVisualizerTest_gtest.cpp
    ${PROJECT_SRC_DIR}/DependencyGraphVisualizer.cpp
)

# Link libraries for all tests
set(ALL_TEST_TARGETS
    test_standalone_function_translation
    test_dependency_graph_visualizer
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
gtest_discover_tests(test_standalone_function_translation
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;translation;functions"
)

gtest_discover_tests(test_dependency_graph_visualizer
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;translation;dependencies"
)

# Summary message
message(STATUS "Translation Test Suite configured with 2 test executables (30 tests total)")

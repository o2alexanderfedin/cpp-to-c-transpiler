cmake_minimum_required(VERSION 3.20)
project(runtime_optimization_tests C CXX)

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

# Runtime Mode Inline Tests (10 tests)
add_executable(test_runtime_mode_inline
    ../RuntimeModeInlineTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/RuntimeModeInline.cpp
)

target_link_libraries(test_runtime_mode_inline
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# Runtime Mode Library Tests (12 tests)
add_executable(test_runtime_mode_library
    ../RuntimeModeLibraryTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/RuntimeModeLibrary.cpp
)

target_link_libraries(test_runtime_mode_library
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# Runtime Feature Flags Tests (15 tests)
add_executable(test_runtime_feature_flags
    ../RuntimeFeatureFlagsTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/RuntimeFeatureFlags.cpp
)

target_link_libraries(test_runtime_feature_flags
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# Size Optimization Tests (14 tests)
add_executable(test_size_optimization
    ../SizeOptimizationTest_GTest.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/SizeOptimizer.cpp
    ${CMAKE_SOURCE_DIR}/../../../src/BuildConfiguration.cpp
)

target_link_libraries(test_size_optimization
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

gtest_discover_tests(test_runtime_mode_inline
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "runtime;inline;story-116"
)

gtest_discover_tests(test_runtime_mode_library
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "runtime;library;story-117"
)

gtest_discover_tests(test_runtime_feature_flags
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "runtime;flags;story-118"
)

gtest_discover_tests(test_size_optimization
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "optimization;size;story-119"
)

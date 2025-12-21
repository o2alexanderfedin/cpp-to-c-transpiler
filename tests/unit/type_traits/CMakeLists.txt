# Type Traits and Metaprogramming Test Suite
# Tests for template metaprogramming, type traits, SFINAE, and compile-time evaluation

cmake_minimum_required(VERSION 3.14)
project(TypeTraitsTests CXX)

# Set C++ standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Fetch GoogleTest
include(FetchContent)
FetchContent_Declare(
    googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG v1.15.2
)
# For Windows: Prevent overriding the parent project's compiler/linker settings
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

# Enable testing
enable_testing()
include(GoogleTest)

# Find LLVM and Clang
find_package(LLVM REQUIRED CONFIG PATHS /opt/homebrew/opt/llvm)
find_package(Clang REQUIRED CONFIG PATHS /opt/homebrew/opt/llvm)

# Add LLVM definitions and include directories
add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${CLANG_INCLUDE_DIRS})

# Type Traits Test Executable
add_executable(TypeTraitsTest
    TypeTraitsTest.cpp
)

target_link_libraries(TypeTraitsTest
    PRIVATE
        GTest::gtest
        GTest::gtest_main
        clangTooling
        clangFrontend
        clangSerialization
        clangAST
        clangBasic
)

target_compile_features(TypeTraitsTest PRIVATE cxx_std_17)

# Add test to CTest
gtest_discover_tests(TypeTraitsTest)

# Metaprogramming Test Executable
add_executable(MetaprogrammingTest
    MetaprogrammingTest.cpp
)

target_link_libraries(MetaprogrammingTest
    PRIVATE
        GTest::gtest
        GTest::gtest_main
        clangTooling
        clangFrontend
        clangSerialization
        clangAST
        clangBasic
)

target_compile_features(MetaprogrammingTest PRIVATE cxx_std_17)

# Add test to CTest
gtest_discover_tests(MetaprogrammingTest)

# Set output directory
set_target_properties(TypeTraitsTest MetaprogrammingTest
    PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin/tests"
)

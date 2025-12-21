cmake_minimum_required(VERSION 3.20)
project(smart_pointers_tests C CXX)

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

# Add LLVM definitions
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

# Test executables
add_executable(test_unique_ptr
    UniquePtrTest.cpp
)

add_executable(test_shared_ptr
    SharedPtrTest.cpp
)

add_executable(test_raii_integration
    RaiiIntegrationTest.cpp
)

# Link against LLVM/Clang libraries
llvm_map_components_to_libnames(llvm_libs support core)

target_link_libraries(test_unique_ptr
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangSerialization
    clangDriver
    clangParse
    clangSema
    clangAnalysis
    clangAST
    clangBasic
    clangEdit
    clangLex
    clangRewrite
    ${llvm_libs}
)

target_link_libraries(test_shared_ptr
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangSerialization
    clangDriver
    clangParse
    clangSema
    clangAnalysis
    clangAST
    clangBasic
    clangEdit
    clangLex
    clangRewrite
    ${llvm_libs}
)

target_link_libraries(test_raii_integration
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangSerialization
    clangDriver
    clangParse
    clangSema
    clangAnalysis
    clangAST
    clangBasic
    clangEdit
    clangLex
    clangRewrite
    ${llvm_libs}
)

# Enable testing
enable_testing()
include(GoogleTest)

gtest_discover_tests(test_unique_ptr
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;smart_pointers;unique_ptr"
)

gtest_discover_tests(test_shared_ptr
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;smart_pointers;shared_ptr"
)

gtest_discover_tests(test_raii_integration
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "unit;smart_pointers;raii"
)

# Add a combined test target
add_custom_target(test_all_smart_pointers
    COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure -L smart_pointers
    DEPENDS test_unique_ptr test_shared_ptr test_raii_integration
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
)

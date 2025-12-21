cmake_minimum_required(VERSION 3.20)
project(batch2_miscellaneous_tests C CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Set LLVM/Clang paths
set(LLVM_DIR "/opt/homebrew/opt/llvm/lib/cmake/llvm")
set(Clang_DIR "/opt/homebrew/opt/llvm/lib/cmake/clang")

# Find LLVM/Clang
find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")

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
include_directories(${CMAKE_SOURCE_DIR}/../../include)
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

# Common link libraries
set(COMMON_LIBS
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)

# Test executables - Batch 2
add_executable(test_cpptocvisitor ../CppToCVisitorTest_GTest.cpp)
target_link_libraries(test_cpptocvisitor ${COMMON_LIBS})

add_executable(test_monomorphization ../MonomorphizationTest_GTest.cpp)
target_link_libraries(test_monomorphization ${COMMON_LIBS})

add_executable(test_memberinit ../MemberInitListTest_GTest.cpp)
target_link_libraries(test_memberinit ${COMMON_LIBS})

# Virtual Function and RTTI Tests (Story #175, Phase 13)
add_executable(test_virtual_function_integration ../gtest/VirtualFunctionIntegrationTest_GTest.cpp)
target_link_libraries(test_virtual_function_integration ${COMMON_LIBS})

add_executable(test_rtti_integration
    ../gtest/RTTIIntegrationTest_GTest.cpp
    ../../src/TypeidTranslator.cpp
    ../../src/DynamicCastTranslator.cpp
    ../../src/TypeInfoGenerator.cpp
    ../../src/VirtualMethodAnalyzer.cpp
)
target_link_libraries(test_rtti_integration ${COMMON_LIBS})

add_executable(test_virtual_method_analyzer ../gtest/VirtualMethodAnalyzerTest_GTest.cpp)
target_link_libraries(test_virtual_method_analyzer ${COMMON_LIBS})

add_executable(test_vtable_generator ../gtest/VtableGeneratorTest_GTest.cpp)
target_link_libraries(test_vtable_generator ${COMMON_LIBS})

add_executable(test_vptr_injector ../gtest/VptrInjectorTest_GTest.cpp)
target_link_libraries(test_vptr_injector ${COMMON_LIBS})

add_executable(test_override_resolver ../gtest/OverrideResolverTest_GTest.cpp)
target_link_libraries(test_override_resolver ${COMMON_LIBS})

add_executable(test_virtual_call_translator ../gtest/VirtualCallTranslatorTest_GTest.cpp)
target_link_libraries(test_virtual_call_translator ${COMMON_LIBS})

add_executable(test_pure_virtual_handler ../gtest/PureVirtualHandlerTest_GTest.cpp)
target_link_libraries(test_pure_virtual_handler ${COMMON_LIBS})

add_executable(test_virtual_destructor_handler ../gtest/VirtualDestructorHandlerTest_GTest.cpp)
target_link_libraries(test_virtual_destructor_handler ${COMMON_LIBS})

# Enable testing
enable_testing()
include(GoogleTest)

# Batch 2 tests
gtest_discover_tests(test_cpptocvisitor WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
gtest_discover_tests(test_monomorphization WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
gtest_discover_tests(test_memberinit WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

# Virtual Function and RTTI tests
gtest_discover_tests(test_virtual_function_integration WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
gtest_discover_tests(test_rtti_integration WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
gtest_discover_tests(test_virtual_method_analyzer WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
gtest_discover_tests(test_vtable_generator WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
gtest_discover_tests(test_vptr_injector WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
gtest_discover_tests(test_override_resolver WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
gtest_discover_tests(test_virtual_call_translator WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
gtest_discover_tests(test_pure_virtual_handler WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
gtest_discover_tests(test_virtual_destructor_handler WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

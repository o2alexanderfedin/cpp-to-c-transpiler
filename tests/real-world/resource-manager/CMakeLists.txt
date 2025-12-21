cmake_minimum_required(VERSION 3.20)
project(resource_manager CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

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
include_directories(include)

# Test executable (header-only library)
add_executable(test_resource_manager
    tests/test_resource_manager.cpp
)

target_link_libraries(test_resource_manager
    GTest::gtest
    GTest::gtest_main
)

# Enable testing
enable_testing()
include(GoogleTest)
gtest_discover_tests(test_resource_manager
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;real-world"
)

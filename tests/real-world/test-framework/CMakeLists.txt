cmake_minimum_required(VERSION 3.20)
project(test_framework CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

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

# Include directories (for legacy test framework, if still needed)
include_directories(include)

# Legacy test framework library (kept for backward compatibility)
add_library(test_framework
    src/TestRegistry.cpp
)

# Google Test executable
add_executable(test_test_framework
    tests/test_framework.cpp
)

# Link with Google Test (no longer needs custom test_framework library)
target_link_libraries(test_test_framework
    GTest::gtest
    GTest::gtest_main
)

# Enable testing with CTest
enable_testing()
include(GoogleTest)

# Discover and register all GTest tests
gtest_discover_tests(test_test_framework
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;real-world;gtest-migrated"
)

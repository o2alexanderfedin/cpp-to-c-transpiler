cmake_minimum_required(VERSION 3.20)
project(json_parser CXX)

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

# Include directories
include_directories(include)

# Library
add_library(json_parser
    src/JsonValue.cpp
    src/JsonParser.cpp
)

# Test executable
add_executable(test_json_parser
    tests/test_json_parser.cpp
)

target_link_libraries(test_json_parser
    json_parser
    GTest::gtest
    GTest::gtest_main
)

# Enable testing
enable_testing()
include(GoogleTest)
gtest_discover_tests(test_json_parser
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    PROPERTIES LABELS "integration;real-world"
)

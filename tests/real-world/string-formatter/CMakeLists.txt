cmake_minimum_required(VERSION 3.20)
project(string_formatter CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Include directories
include_directories(include)

# Test executable (header-only library)
add_executable(test_string_formatter
    tests/test_string_formatter.cpp
)

# Enable testing
enable_testing()
add_test(NAME StringFormatterTest COMMAND test_string_formatter)

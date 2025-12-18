cmake_minimum_required(VERSION 3.20)
project(test_framework CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Include directories
include_directories(include)

# Library
add_library(test_framework
    src/TestRegistry.cpp
)

# Test executable
add_executable(test_test_framework
    tests/test_framework.cpp
)

target_link_libraries(test_test_framework test_framework)

# Enable testing
enable_testing()
add_test(NAME TestFrameworkTest COMMAND test_test_framework)

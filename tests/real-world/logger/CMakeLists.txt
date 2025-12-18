cmake_minimum_required(VERSION 3.20)
project(logger CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Include directories
include_directories(include)

# Test executable (header-only library)
add_executable(test_logger
    tests/test_logger.cpp
)

# Enable testing
enable_testing()
add_test(NAME LoggerTest COMMAND test_logger)

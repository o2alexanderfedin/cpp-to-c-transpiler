cmake_minimum_required(VERSION 3.10)
project(safety-critical-example CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(safety-critical-test
    src/main.cpp
)

# Enable all warnings and treat as errors
target_compile_options(safety-critical-test PRIVATE
    -Wall -Wextra -Wpedantic -Werror
    -Wconversion -Wsign-conversion
)

# Add assertions in all builds (critical for safety)
target_compile_definitions(safety-critical-test PRIVATE
    ENABLE_ASSERTS=1
)

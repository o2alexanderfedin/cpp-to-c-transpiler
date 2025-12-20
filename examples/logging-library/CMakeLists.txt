cmake_minimum_required(VERSION 3.10)
project(logging-library-example CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(logging-example
    src/main.cpp
)

# Enable warnings
target_compile_options(logging-example PRIVATE
    -Wall -Wextra -Wpedantic
)

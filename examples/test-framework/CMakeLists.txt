cmake_minimum_required(VERSION 3.10)
project(test-framework-example CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(test-framework-example
    src/main.cpp
)

target_compile_options(test-framework-example PRIVATE
    -Wall -Wextra
)

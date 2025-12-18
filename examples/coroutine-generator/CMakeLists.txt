cmake_minimum_required(VERSION 3.10)
project(coroutine-generator-example CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(coroutine-example
    src/main.cpp
)

target_compile_options(coroutine-example PRIVATE
    -Wall -Wextra
)

cmake_minimum_required(VERSION 3.10)
project(SimpleParser CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include_directories(include)

add_executable(simple_parser
    src/Tokenizer.cpp
    src/ExpressionEvaluator.cpp
    main.cpp
)

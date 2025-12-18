cmake_minimum_required(VERSION 3.20)
project(json_parser CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

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

target_link_libraries(test_json_parser json_parser)

# Enable testing
enable_testing()
add_test(NAME JsonParserTest COMMAND test_json_parser)

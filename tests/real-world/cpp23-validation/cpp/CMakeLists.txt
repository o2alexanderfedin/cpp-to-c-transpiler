cmake_minimum_required(VERSION 3.20)
project(cpp23_validation CXX)

# C++23 is required
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Use Clang for C++23 support
set(CMAKE_CXX_COMPILER "/opt/homebrew/Cellar/llvm/21.1.7/bin/clang++")

# Enable all warnings and treat them as errors
add_compile_options(
    -Wall
    -Wextra
    -Werror
    -pedantic
)

# Include directories
include_directories(include)

# Source files
set(SOURCES
    src/main.cpp
    src/deducing_this.cpp
    src/consteval_if.cpp
    src/multidim_subscript.cpp
    src/static_operators.cpp
    src/attributes.cpp
    src/literals.cpp
)

# Create executable
add_executable(cpp23_validation ${SOURCES})

# Installation
install(TARGETS cpp23_validation DESTINATION bin)

# Display configuration
message(STATUS "C++ Standard: ${CMAKE_CXX_STANDARD}")
message(STATUS "Compiler: ${CMAKE_CXX_COMPILER}")
message(STATUS "Build Type: ${CMAKE_BUILD_TYPE}")

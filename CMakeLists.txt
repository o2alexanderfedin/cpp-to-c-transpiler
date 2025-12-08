cmake_minimum_required(VERSION 3.20)
project(cpptoc C CXX)

# Set C++17 standard (SOLID principle: explicit requirements)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find LLVM and Clang packages
# Using CONFIG mode for better reliability
find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

# Add LLVM definitions and include directories
add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${CLANG_INCLUDE_DIRS})

# Create executable target
# Single responsibility: build the cpptoc tool
add_executable(cpptoc
    src/main.cpp
)

# Link against Clang/LLVM libraries
# Minimal set needed for LibTooling
target_link_libraries(cpptoc
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

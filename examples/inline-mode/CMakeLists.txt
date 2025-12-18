# CMakeLists.txt for Inline Runtime Mode Example
# Story #116: Inline Runtime Mode
#
# This example builds C++ code with the runtime inlined directly into
# the generated C code. No external runtime library is required.

cmake_minimum_required(VERSION 3.10)
project(InlineRuntimeExample CXX)

# Set C++ standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Build the example executable directly from C++ source
add_executable(simple_example
    simple_example.cpp
)

# Enable RTTI and exceptions (required for the example)
target_compile_options(simple_example PRIVATE
    -frtti           # Enable RTTI
    -fexceptions     # Enable exceptions
)

# Display build configuration
message(STATUS "====================================")
message(STATUS "Inline Runtime Mode Example")
message(STATUS "====================================")
message(STATUS "Runtime Mode: INLINE")
message(STATUS "Description: Runtime functions are inlined into generated C code")
message(STATUS "Advantages:")
message(STATUS "  - Simple deployment (no library dependencies)")
message(STATUS "  - Single executable with no external requirements")
message(STATUS "Disadvantages:")
message(STATUS "  - Larger binary size (runtime duplicated)")
message(STATUS "  - Slower compilation for large projects")
message(STATUS "====================================")

# Add custom target to run the example
add_custom_target(run_inline
    COMMAND simple_example
    DEPENDS simple_example
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    COMMENT "Running inline runtime mode example..."
)

# Note: In a real cpptoc workflow, you would:
# 1. Run cpptoc transpiler: cpptoc simple_example.cpp --runtime-mode=inline
# 2. Compile generated C code: gcc simple_example.c -o simple_example
# 3. Run executable: ./simple_example
#
# This CMakeLists.txt builds the C++ directly for demonstration purposes.
# The runtime inlining would happen during the cpptoc transpilation step.

# RuntimeTestHarness Helper Library
# Provides runtime integration testing capabilities

# Create static library for runtime test helpers
add_library(runtime_test_helpers STATIC
    RuntimeTestHarness.cpp
)

# Apply LLVM/Clang compile definitions
target_compile_definitions(runtime_test_helpers PUBLIC ${LLVM_DEFINITIONS})

# Add include directories
target_include_directories(runtime_test_helpers PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

# Link against Clang/LLVM libraries
target_link_libraries(runtime_test_helpers PUBLIC
    cpptoc_core
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# C++ to C Transpiler - Benchmarks
# Performance benchmarking infrastructure
#
# This CMakeLists.txt builds performance benchmarks for the transpiler.
# Benchmarks are OPTIONAL and not built by default.
#
# To build benchmarks:
#   cmake -B build -DBUILD_BENCHMARKS=ON
#   cmake --build build
#
# To run benchmarks:
#   ./benchmarks/run_benchmarks.sh

cmake_minimum_required(VERSION 3.20)

# Only build benchmarks if explicitly requested
option(BUILD_BENCHMARKS "Build performance benchmarks (optional)" OFF)

if(NOT BUILD_BENCHMARKS)
    message(STATUS "Benchmarks disabled. Use -DBUILD_BENCHMARKS=ON to enable.")
    return()
endif()

message(STATUS "Configuring benchmarks...")

# ============================================================================
# RTTI Runtime Benchmarks (Existing)
# ============================================================================
# Performance validation for C++ to C transpiler RTTI runtime implementation.
# Measures dynamic_cast overhead compared to native C++ implementation.
# Target: 10-20% overhead vs native C++ dynamic_cast

# C Transpiled Runtime Benchmark
add_executable(rtti_benchmark
    rtti_benchmark.c
    ${CMAKE_SOURCE_DIR}/runtime/rtti_runtime.c
)

target_include_directories(rtti_benchmark PRIVATE
    ${CMAKE_SOURCE_DIR}/runtime
)

# Enable optimization for accurate performance measurement
target_compile_options(rtti_benchmark PRIVATE
    -O3
    -march=native
)

# Set C standard
set_target_properties(rtti_benchmark PROPERTIES
    C_STANDARD 11
    C_STANDARD_REQUIRED ON
)

# C++ Native Baseline Benchmark
add_executable(rtti_benchmark_cpp
    rtti_benchmark.cpp
)

# Enable RTTI (required for dynamic_cast)
target_compile_options(rtti_benchmark_cpp PRIVATE
    -frtti
    -O3
    -march=native
)

# Set C++ standard
set_target_properties(rtti_benchmark_cpp PROPERTIES
    CXX_STANDARD 17
    CXX_STANDARD_REQUIRED ON
)

# ============================================================================
# Exception Handling Runtime Benchmarks
# ============================================================================
# Performance validation for exception handling runtime implementation.
# Measures try-catch and throw-catch overhead compared to native C++.
# Target: 5-10% overhead (no throw), 15-25% overhead (with throw)

# C Transpiled Exception Benchmark
# Note: We compile the .c file as C++ to link with exception_runtime.cpp
add_executable(exception_benchmark
    exception_benchmark.c
    ${CMAKE_SOURCE_DIR}/runtime/exception_runtime.cpp
)

target_include_directories(exception_benchmark PRIVATE
    ${CMAKE_SOURCE_DIR}/runtime
)

# Enable optimization for accurate performance measurement
target_compile_options(exception_benchmark PRIVATE -O2)

# Compile the .c file as C++ to properly link with exception_runtime.cpp
set_source_files_properties(exception_benchmark.c PROPERTIES LANGUAGE CXX)

# Set C++ standard
set_target_properties(exception_benchmark PROPERTIES
    CXX_STANDARD 11
    CXX_STANDARD_REQUIRED ON
)

# C++ Native Exception Benchmark
add_executable(exception_benchmark_native
    exception_benchmark_native.cpp
)

# Enable optimization for accurate performance measurement
target_compile_options(exception_benchmark_native PRIVATE -O2)

# Set C++ standard
set_target_properties(exception_benchmark_native PROPERTIES
    CXX_STANDARD 17
    CXX_STANDARD_REQUIRED ON
)

# ============================================================================
# Virtual Call Runtime Benchmarks
# ============================================================================
# Performance validation for virtual function call implementation.
# Measures vtable dispatch overhead compared to native C++ virtual calls.
# Target: 0-2% overhead vs native C++ virtual calls

# C Transpiled Virtual Call Benchmark
add_executable(virtual_benchmark
    virtual_benchmark.c
)

# Enable optimization for accurate performance measurement
target_compile_options(virtual_benchmark PRIVATE
    -O3
    -march=native
)

# Set C standard
set_target_properties(virtual_benchmark PROPERTIES
    C_STANDARD 11
    C_STANDARD_REQUIRED ON
)

# C++ Native Virtual Call Baseline Benchmark
add_executable(virtual_benchmark_cpp
    virtual_benchmark.cpp
)

# Enable optimization for accurate performance measurement
target_compile_options(virtual_benchmark_cpp PRIVATE
    -O3
    -march=native
)

# Set C++ standard
set_target_properties(virtual_benchmark_cpp PROPERTIES
    CXX_STANDARD 17
    CXX_STANDARD_REQUIRED ON
)

# ============================================================================
# Coroutine Runtime Benchmarks
# ============================================================================
# Performance validation for coroutine runtime implementation.
# Measures coroutine resume/destroy overhead compared to native C++20.
# Target: 5-15% overhead vs native C++20 coroutines

# C Transpiled Coroutine Benchmark
add_executable(coroutine_benchmark
    coroutine_benchmark.c
)

# Enable optimization for accurate performance measurement
target_compile_options(coroutine_benchmark PRIVATE
    -O3
    -march=native
)

# Set C standard
set_target_properties(coroutine_benchmark PROPERTIES
    C_STANDARD 11
    C_STANDARD_REQUIRED ON
)

# C++20 Native Coroutine Benchmark
add_executable(coroutine_benchmark_cpp
    coroutine_benchmark.cpp
)

# Enable optimization and C++20 coroutines
target_compile_options(coroutine_benchmark_cpp PRIVATE
    -O3
    -march=native
    -fcoroutines
)

# Set C++20 standard (required for coroutines)
set_target_properties(coroutine_benchmark_cpp PROPERTIES
    CXX_STANDARD 20
    CXX_STANDARD_REQUIRED ON
)

# ============================================================================
# Transpiler Component Benchmarks (New)
# ============================================================================

# Benchmark: AST Traversal Performance
add_executable(benchmark_ast_traversal
    benchmark_ast_traversal.cpp
    ${CMAKE_SOURCE_DIR}/src/CppToCVisitor.cpp
    ${CMAKE_SOURCE_DIR}/src/CFGAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/src/NameMangler.cpp
    ${CMAKE_SOURCE_DIR}/src/VirtualMethodAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/src/VptrInjector.cpp
)

target_compile_definitions(benchmark_ast_traversal PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(benchmark_ast_traversal PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(benchmark_ast_traversal PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Benchmark: Name Mangling Performance
add_executable(benchmark_name_mangling
    benchmark_name_mangling.cpp
    ${CMAKE_SOURCE_DIR}/src/NameMangler.cpp
)

target_compile_definitions(benchmark_name_mangling PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(benchmark_name_mangling PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(benchmark_name_mangling PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Benchmark: Code Generation Performance
add_executable(benchmark_code_generation
    benchmark_code_generation.cpp
    ${CMAKE_SOURCE_DIR}/src/CodeGenerator.cpp
)

target_compile_definitions(benchmark_code_generation PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(benchmark_code_generation PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(benchmark_code_generation PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Benchmark: End-to-End Transpilation
add_executable(benchmark_e2e_transpilation
    benchmark_e2e_transpilation.cpp
    ${CMAKE_SOURCE_DIR}/src/CppToCVisitor.cpp
    ${CMAKE_SOURCE_DIR}/src/CppToCConsumer.cpp
    ${CMAKE_SOURCE_DIR}/src/CFGAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/src/NameMangler.cpp
    ${CMAKE_SOURCE_DIR}/src/CodeGenerator.cpp
    ${CMAKE_SOURCE_DIR}/src/HeaderSeparator.cpp
    ${CMAKE_SOURCE_DIR}/src/IncludeGuardGenerator.cpp
    ${CMAKE_SOURCE_DIR}/src/DependencyAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/src/FileOutputManager.cpp
    ${CMAKE_SOURCE_DIR}/src/VirtualMethodAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/src/VptrInjector.cpp
)

target_compile_definitions(benchmark_e2e_transpilation PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(benchmark_e2e_transpilation PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(benchmark_e2e_transpilation PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Benchmark: Memory Usage Profiling
add_executable(benchmark_memory_usage
    benchmark_memory_usage.cpp
    ${CMAKE_SOURCE_DIR}/src/CppToCVisitor.cpp
    ${CMAKE_SOURCE_DIR}/src/CFGAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/src/NameMangler.cpp
    ${CMAKE_SOURCE_DIR}/src/VirtualMethodAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/src/VptrInjector.cpp
)

target_compile_definitions(benchmark_memory_usage PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(benchmark_memory_usage PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(benchmark_memory_usage PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Benchmark: Virtual Function Resolution
add_executable(benchmark_virtual_functions
    benchmark_virtual_functions.cpp
    ${CMAKE_SOURCE_DIR}/src/VirtualMethodAnalyzer.cpp
    ${CMAKE_SOURCE_DIR}/src/VptrInjector.cpp
)

target_compile_definitions(benchmark_virtual_functions PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(benchmark_virtual_functions PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(benchmark_virtual_functions PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

message(STATUS "Benchmarks configured successfully")
message(STATUS "Runtime Benchmarks:")
message(STATUS "  - rtti_benchmark (C transpiled)")
message(STATUS "  - rtti_benchmark_cpp (C++ native baseline)")
message(STATUS "  - exception_benchmark (C transpiled)")
message(STATUS "  - exception_benchmark_native (C++ native baseline)")
message(STATUS "  - virtual_benchmark (C transpiled)")
message(STATUS "  - virtual_benchmark_cpp (C++ native baseline)")
message(STATUS "  - coroutine_benchmark (C transpiled)")
message(STATUS "  - coroutine_benchmark_cpp (C++20 native baseline)")
message(STATUS "Transpiler Component Benchmarks:")
message(STATUS "  - benchmark_ast_traversal: AST traversal performance")
message(STATUS "  - benchmark_name_mangling: Name mangling performance")
message(STATUS "  - benchmark_code_generation: Code generation performance")
message(STATUS "  - benchmark_e2e_transpilation: End-to-end transpilation")
message(STATUS "  - benchmark_memory_usage: Memory usage profiling")
message(STATUS "  - benchmark_virtual_functions: Virtual function resolution")

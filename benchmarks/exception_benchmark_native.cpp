/*
 * exception_benchmark_native.cpp - Native C++ Exception Benchmark
 *
 * This benchmark provides baseline performance measurements for native C++
 * exception handling. Used to compare against the transpiled C runtime.
 *
 * METHODOLOGY:
 * - Matches the test scenarios from exception_benchmark.c
 * - Uses native C++ try/catch/throw
 * - High-resolution timing
 * - Same iteration counts for direct comparison
 *
 * COMPILE:
 *   clang++ -std=c++17 -O2 exception_benchmark_native.cpp -o benchmark_native
 *
 * SOLID PRINCIPLES:
 * - Single Responsibility: Native C++ exception benchmarking
 * - KISS: Simple, direct benchmarks matching C version
 */

#include <iostream>
#include <chrono>
#include <cstring>
#include <exception>

using namespace std;
using namespace std::chrono;

// ============================================================================
// Test Exception Types
// ============================================================================

struct BenchmarkException {
    int code;
    char message[64];

    BenchmarkException(int c) : code(c) {
        snprintf(message, sizeof(message), "Exception %d", c);
    }
};

struct BenchmarkResource {
    int id;
    int data[10];

    BenchmarkResource(int i) : id(i) {
        memset(data, 0, sizeof(data));
    }

    ~BenchmarkResource() {
        id = -1;  // Simulate cleanup
    }
};

// ============================================================================
// Benchmark 1: Try-Catch Overhead (No Exception)
// ============================================================================

static void benchmark_no_exception_native(int iterations) {
    for (int i = 0; i < iterations; i++) {
        try {
            // Normal execution path (no exception)
            volatile int result = i * 2 + i / 2;
            (void)result;
        } catch (...) {
            cerr << "ERROR: Unexpected exception in no-throw benchmark" << endl;
            exit(1);
        }
    }
}

static void run_benchmark_no_exception() {
    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    cout << "Benchmark 1: Try-catch with NO exception (happy path)" << endl;
    cout << "  Iterations: " << ITERATIONS << endl;

    // Warm-up
    benchmark_no_exception_native(WARMUP);

    // Actual benchmark
    auto start = high_resolution_clock::now();
    benchmark_no_exception_native(ITERATIONS);
    auto end = high_resolution_clock::now();

    double duration_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    double per_iteration_ns = (duration_ms * 1e6) / ITERATIONS;

    cout << "  Duration: " << duration_ms << " ms" << endl;
    cout << "  Per iteration: " << per_iteration_ns << " ns" << endl;

    if (per_iteration_ns < 5.0) {
        cout << "  Status: EXCELLENT - Zero-cost exception handling" << endl;
    } else if (per_iteration_ns < 10.0) {
        cout << "  Status: GOOD" << endl;
    } else {
        cout << "  Status: Baseline measurement" << endl;
    }
    cout << endl;
}

// ============================================================================
// Benchmark 2: Throw-Catch Overhead
// ============================================================================

static void benchmark_with_exception_native(int iterations) {
    for (int i = 0; i < iterations; i++) {
        try {
            throw BenchmarkException(i);
        } catch (const BenchmarkException& ex) {
            volatile int code = ex.code;
            (void)code;
        }
    }
}

static void run_benchmark_with_exception() {
    const int ITERATIONS = 100000;
    const int WARMUP = 1000;

    cout << "Benchmark 2: Try-catch WITH exception (exception path)" << endl;
    cout << "  Iterations: " << ITERATIONS << endl;

    // Warm-up
    benchmark_with_exception_native(WARMUP);

    // Actual benchmark
    auto start = high_resolution_clock::now();
    benchmark_with_exception_native(ITERATIONS);
    auto end = high_resolution_clock::now();

    double duration_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    double per_iteration_ns = (duration_ms * 1e6) / ITERATIONS;

    cout << "  Duration: " << duration_ms << " ms" << endl;
    cout << "  Per iteration: " << per_iteration_ns << " ns" << endl;
    cout << "  Status: Native C++ baseline" << endl;
    cout << endl;
}

// ============================================================================
// Benchmark 3: RAII Cleanup During Exception
// ============================================================================

static void benchmark_raii_cleanup_native(int iterations) {
    for (int i = 0; i < iterations; i++) {
        try {
            BenchmarkResource res(i);
            throw BenchmarkException(i);
        } catch (const BenchmarkException& ex) {
            volatile int code = ex.code;
            (void)code;
        }
    }
}

static void run_benchmark_raii_cleanup() {
    const int ITERATIONS = 100000;
    const int WARMUP = 1000;

    cout << "Benchmark 3: RAII cleanup during exception" << endl;
    cout << "  Iterations: " << ITERATIONS << endl;

    // Warm-up
    benchmark_raii_cleanup_native(WARMUP);

    // Actual benchmark
    auto start = high_resolution_clock::now();
    benchmark_raii_cleanup_native(ITERATIONS);
    auto end = high_resolution_clock::now();

    double duration_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    double per_iteration_ns = (duration_ms * 1e6) / ITERATIONS;

    cout << "  Duration: " << duration_ms << " ms" << endl;
    cout << "  Per iteration: " << per_iteration_ns << " ns" << endl;
    cout << "  Status: Native C++ baseline with RAII" << endl;
    cout << endl;
}

// ============================================================================
// Benchmark 4: Multiple Resources
// ============================================================================

static void benchmark_multiple_resources_native(int iterations) {
    for (int i = 0; i < iterations; i++) {
        try {
            BenchmarkResource res1(i * 3 + 0);
            BenchmarkResource res2(i * 3 + 1);
            BenchmarkResource res3(i * 3 + 2);
            throw BenchmarkException(i);
        } catch (const BenchmarkException& ex) {
            volatile int code = ex.code;
            (void)code;
        }
    }
}

static void run_benchmark_multiple_resources() {
    const int ITERATIONS = 100000;
    const int WARMUP = 1000;

    cout << "Benchmark 4: Multiple resources cleanup (3 destructors)" << endl;
    cout << "  Iterations: " << ITERATIONS << endl;

    // Warm-up
    benchmark_multiple_resources_native(WARMUP);

    // Actual benchmark
    auto start = high_resolution_clock::now();
    benchmark_multiple_resources_native(ITERATIONS);
    auto end = high_resolution_clock::now();

    double duration_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    double per_iteration_ns = (duration_ms * 1e6) / ITERATIONS;

    cout << "  Duration: " << duration_ms << " ms" << endl;
    cout << "  Per iteration: " << per_iteration_ns << " ns" << endl;
    cout << "  Status: Native C++ baseline with multiple destructors" << endl;
    cout << endl;
}

// ============================================================================
// Benchmark 5: Nested Try-Catch
// ============================================================================

static void benchmark_nested_trycatch_native(int iterations) {
    for (int i = 0; i < iterations; i++) {
        try {
            try {
                throw BenchmarkException(i);
            } catch (const BenchmarkException& ex) {
                volatile int code = ex.code;
                (void)code;
            }
        } catch (...) {
            cerr << "ERROR: Unexpected outer catch" << endl;
            exit(1);
        }
    }
}

static void run_benchmark_nested_trycatch() {
    const int ITERATIONS = 100000;
    const int WARMUP = 1000;

    cout << "Benchmark 5: Nested try-catch blocks (2 levels)" << endl;
    cout << "  Iterations: " << ITERATIONS << endl;

    // Warm-up
    benchmark_nested_trycatch_native(WARMUP);

    // Actual benchmark
    auto start = high_resolution_clock::now();
    benchmark_nested_trycatch_native(ITERATIONS);
    auto end = high_resolution_clock::now();

    double duration_ms = duration_cast<microseconds>(end - start).count() / 1000.0;
    double per_iteration_ns = (duration_ms * 1e6) / ITERATIONS;

    cout << "  Duration: " << duration_ms << " ms" << endl;
    cout << "  Per iteration: " << per_iteration_ns << " ns" << endl;
    cout << "  Status: Native C++ baseline with nested try-catch" << endl;
    cout << endl;
}

// ============================================================================
// Memory Footprint (for reference)
// ============================================================================

static void run_memory_footprint_analysis() {
    cout << "Memory Footprint Analysis (Native C++)" << endl;
    cout << "  sizeof(BenchmarkException): " << sizeof(BenchmarkException) << " bytes" << endl;
    cout << "  sizeof(BenchmarkResource): " << sizeof(BenchmarkResource) << " bytes" << endl;
    cout << "  Note: Native C++ exceptions have runtime-internal overhead" << endl;
    cout << "  Note: Zero-cost exception handling adds no overhead to happy path" << endl;
    cout << endl;
}

// ============================================================================
// Main
// ============================================================================

int main() {
    cout << endl;
    cout << "=====================================================" << endl;
    cout << "Native C++ Exception Benchmark" << endl;
    cout << "Baseline Performance Measurements" << endl;
    cout << "=====================================================" << endl;
    cout << endl;

    cout << "Compiler: ";
#ifdef __clang__
    cout << "Clang " << __clang_major__ << "." << __clang_minor__ << endl;
#elif defined(__GNUC__)
    cout << "GCC " << __GNUC__ << "." << __GNUC_MINOR__ << endl;
#else
    cout << "Unknown" << endl;
#endif

    cout << "C++ Standard: " << __cplusplus << endl;
    cout << endl;

    cout << "NOTES:" << endl;
    cout << "  - Modern C++ uses zero-cost exception handling (Itanium ABI)" << endl;
    cout << "  - No overhead when exceptions are not thrown (happy path)" << endl;
    cout << "  - Throwing exceptions is expensive (table-based unwinding)" << endl;
    cout << "  - Compare these results with exception_benchmark.c output" << endl;
    cout << endl;

    cout << "=====================================================" << endl;
    cout << "Running Benchmarks..." << endl;
    cout << "=====================================================" << endl;
    cout << endl;

    // Run all benchmarks
    run_benchmark_no_exception();
    run_benchmark_with_exception();
    run_benchmark_raii_cleanup();
    run_benchmark_multiple_resources();
    run_benchmark_nested_trycatch();
    run_memory_footprint_analysis();

    cout << "=====================================================" << endl;
    cout << "Benchmark Complete" << endl;
    cout << "=====================================================" << endl;
    cout << endl;

    cout << "COMPARISON:" << endl;
    cout << "  Use these baseline numbers to calculate overhead of the" << endl;
    cout << "  transpiled C exception runtime (exception_benchmark.c)" << endl;
    cout << endl;
    cout << "  Overhead % = (C_time - CPP_time) / CPP_time * 100" << endl;
    cout << endl;
    cout << "  TARGET OVERHEAD:" << endl;
    cout << "    - No exception: 5-10% (setjmp cost)" << endl;
    cout << "    - With exception: 15-25% (SJLJ vs table-based)" << endl;
    cout << endl;

    return 0;
}

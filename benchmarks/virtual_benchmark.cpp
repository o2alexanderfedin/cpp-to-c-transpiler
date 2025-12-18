/**
 * @file virtual_benchmark.cpp
 * @brief Native C++ Virtual Call Performance Baseline
 *
 * Native C++ virtual function call baseline for comparison with transpiled C runtime.
 * Uses identical test scenarios to measure native performance.
 *
 * BENCHMARK BASELINE:
 * ===================
 * This file provides native C++ performance numbers for comparison.
 * Run both benchmarks and calculate overhead:
 *   overhead = (C_time - CPP_time) / CPP_time * 100%
 *
 * Target: Transpiled C should have 0-2% overhead vs these baselines.
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only benchmarks native C++ virtual calls
 * - Open/Closed: Extensible for new benchmark scenarios
 * - Dependency Inversion: Uses standard C++ virtual functions
 */

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>

// ============================================================================
// High-Resolution Timing Utilities
// ============================================================================

struct BenchmarkTimer {
    std::chrono::high_resolution_clock::time_point start;
    std::chrono::high_resolution_clock::time_point end;

    void Start() {
        start = std::chrono::high_resolution_clock::now();
    }

    uint64_t End() {
        end = std::chrono::high_resolution_clock::now();
        return std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();
    }
};

// ============================================================================
// Single Inheritance Test Classes
// ============================================================================

class Base {
public:
    virtual ~Base() {}
    virtual int method1() { return base_data * 2; }
    virtual int method2(int arg) { return base_data + arg; }

    int base_data;
};

class Derived : public Base {
public:
    virtual int method1() override { return base_data + derived_data; }

    int derived_data;
};

// ============================================================================
// Multiple Inheritance Test Classes
// ============================================================================

class Base1 {
public:
    virtual ~Base1() {}
    virtual int compute() { return data1 * 3; }

    int data1;
};

class Base2 {
public:
    virtual ~Base2() {}
    virtual int calculate() { return data2 * 5; }

    int data2;
};

class Diamond : public Base1, public Base2 {
public:
    virtual int compute() override { return data1 + data2 + diamond_data; }
    virtual int calculate() override { return data1 * data2 + diamond_data; }

    int diamond_data;
};

// ============================================================================
// Deep Hierarchy Test Classes
// ============================================================================

class A {
public:
    virtual ~A() {}
    virtual int process() { return a; }

    int a;
};

class B : public A {
public:
    int b;
};

class C : public B {
public:
    int c;
};

class D : public C {
public:
    int d;
};

class E : public D {
public:
    virtual int process() override { return a + b + c + d + e; }

    int e;
};

// ============================================================================
// Virtual Destructor Test Classes
// ============================================================================

class BaseWithDtor {
public:
    virtual ~BaseWithDtor() { data = 0; }
    virtual int method() { return 42; }

    int data;
};

class DerivedWithDtor : public BaseWithDtor {
public:
    virtual ~DerivedWithDtor() { data = 0; extra_data = 0; }

    int extra_data;
};

// ============================================================================
// Benchmark 1: Single Inheritance Virtual Call
// ============================================================================

void benchmark_single_inheritance_native(int iterations) {
    Derived obj;
    obj.base_data = 42;
    obj.derived_data = 100;

    Base *base_ptr = &obj;

    // Benchmark: Virtual call through base pointer
    volatile int result = 0;
    for (int i = 0; i < iterations; i++) {
        result += base_ptr->method1();
    }

    if (result == 0) std::abort();
}

void test_benchmark_single_inheritance() {
    std::cout << "Benchmark 1: Single inheritance virtual call" << std::endl;

    const int ITERATIONS = 10000000;
    const int WARMUP = 100000;

    // Warm up
    benchmark_single_inheritance_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_single_inheritance_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);

    std::cout << "  Iterations:     " << ITERATIONS << std::endl;
    std::cout << "  Total time:     " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per call:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:     " << 1000.0 / ns_per_op << " M calls/sec" << std::endl;

    std::cout << "  Status:         ";
    if (ns_per_op < 2.0) {
        std::cout << "✓ EXCELLENT (< 2ns - optimal vtable dispatch)" << std::endl;
    } else if (ns_per_op < 5.0) {
        std::cout << "✓ GOOD (< 5ns - efficient dispatch)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Benchmark 2: Multiple Inheritance Virtual Call
// ============================================================================

void benchmark_multiple_inheritance_native(int iterations) {
    Diamond obj;
    obj.data1 = 42;
    obj.data2 = 100;
    obj.diamond_data = 200;

    // Call through Base2 pointer (requires offset adjustment)
    Base2 *base2_ptr = &obj;

    // Benchmark: Virtual call through Base2 pointer
    volatile int result = 0;
    for (int i = 0; i < iterations; i++) {
        result += base2_ptr->calculate();
    }

    if (result == 0) std::abort();
}

void test_benchmark_multiple_inheritance() {
    std::cout << "Benchmark 2: Multiple inheritance virtual call (with offset)" << std::endl;

    const int ITERATIONS = 10000000;
    const int WARMUP = 100000;

    // Warm up
    benchmark_multiple_inheritance_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_multiple_inheritance_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);

    std::cout << "  Iterations:     " << ITERATIONS << std::endl;
    std::cout << "  Total time:     " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per call:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:     " << 1000.0 / ns_per_op << " M calls/sec" << std::endl;

    std::cout << "  Status:         ";
    if (ns_per_op < 3.0) {
        std::cout << "✓ EXCELLENT (< 3ns with offset adjustment)" << std::endl;
    } else if (ns_per_op < 6.0) {
        std::cout << "✓ GOOD (< 6ns with offset adjustment)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Benchmark 3: Deep Hierarchy Virtual Call
// ============================================================================

void benchmark_deep_hierarchy_native(int iterations) {
    E obj;
    obj.a = 1;
    obj.b = 2;
    obj.c = 3;
    obj.d = 4;
    obj.e = 5;

    A *a_ptr = &obj;

    // Benchmark: Virtual call through base pointer (5 levels deep)
    volatile int result = 0;
    for (int i = 0; i < iterations; i++) {
        result += a_ptr->process();
    }

    if (result == 0) std::abort();
}

void test_benchmark_deep_hierarchy() {
    std::cout << "Benchmark 3: Deep hierarchy virtual call (5 levels: A <- B <- C <- D <- E)" << std::endl;

    const int ITERATIONS = 10000000;
    const int WARMUP = 100000;

    // Warm up
    benchmark_deep_hierarchy_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_deep_hierarchy_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);

    std::cout << "  Iterations:     " << ITERATIONS << std::endl;
    std::cout << "  Total time:     " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per call:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:     " << 1000.0 / ns_per_op << " M calls/sec" << std::endl;

    std::cout << "  Status:         ";
    if (ns_per_op < 2.0) {
        std::cout << "✓ EXCELLENT (< 2ns - O(1) dispatch regardless of depth)" << std::endl;
    } else if (ns_per_op < 5.0) {
        std::cout << "✓ GOOD (< 5ns - efficient dispatch)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Benchmark 4: Virtual Destructor Call
// ============================================================================

void benchmark_virtual_destructor_native(int iterations) {
    // Allocate array of objects to avoid repeated allocation overhead
    DerivedWithDtor *objects = new DerivedWithDtor[100];

    for (int j = 0; j < 100; j++) {
        objects[j].data = 42;
        objects[j].extra_data = 100;
    }

    // Benchmark: Virtual destructor calls
    for (int i = 0; i < iterations; i++) {
        BaseWithDtor *base_ptr = &objects[i % 100];
        // Manually call destructor (simulating explicit destruction)
        base_ptr->~BaseWithDtor();
        // Reinitialize for next iteration
        new (&objects[i % 100]) DerivedWithDtor();
        objects[i % 100].data = 42;
        objects[i % 100].extra_data = 100;
    }

    delete[] objects;
}

void test_benchmark_virtual_destructor() {
    std::cout << "Benchmark 4: Virtual destructor call" << std::endl;

    const int ITERATIONS = 10000000;
    const int WARMUP = 100000;

    // Warm up
    benchmark_virtual_destructor_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_virtual_destructor_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);

    std::cout << "  Iterations:     " << ITERATIONS << std::endl;
    std::cout << "  Total time:     " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per call:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:     " << 1000.0 / ns_per_op << " M calls/sec" << std::endl;

    std::cout << "  Status:         ";
    if (ns_per_op < 3.0) {
        std::cout << "✓ EXCELLENT (< 3ns per destructor call)" << std::endl;
    } else if (ns_per_op < 6.0) {
        std::cout << "✓ GOOD (< 6ns per destructor call)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Benchmark 5: Multiple Virtual Calls in Sequence
// ============================================================================

void benchmark_sequential_calls_native(int iterations) {
    Derived obj;
    obj.base_data = 42;
    obj.derived_data = 100;

    Base *base_ptr = &obj;

    // Benchmark: Multiple virtual calls in sequence
    volatile int result = 0;
    for (int i = 0; i < iterations; i++) {
        // Three sequential virtual calls
        result += base_ptr->method1();
        result += base_ptr->method2(10);
        result += base_ptr->method1();
    }

    if (result == 0) std::abort();
}

void test_benchmark_sequential_calls() {
    std::cout << "Benchmark 5: Multiple virtual calls in sequence (3 calls per iteration)" << std::endl;

    const int ITERATIONS = 10000000;
    const int WARMUP = 100000;

    // Warm up
    benchmark_sequential_calls_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_sequential_calls_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    // Calculate time per individual call (3 calls per iteration)
    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS * 3);

    std::cout << "  Iterations:     " << ITERATIONS << " (3 calls each)" << std::endl;
    std::cout << "  Total calls:    " << ITERATIONS * 3 << std::endl;
    std::cout << "  Total time:     " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per call:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:     " << 1000.0 / ns_per_op << " M calls/sec" << std::endl;

    std::cout << "  Status:         ";
    if (ns_per_op < 2.0) {
        std::cout << "✓ EXCELLENT (< 2ns - excellent cache locality)" << std::endl;
    } else if (ns_per_op < 5.0) {
        std::cout << "✓ GOOD (< 5ns - good cache performance)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Main Benchmark Suite
// ============================================================================

int main() {
    std::cout << std::endl;
    std::cout << "=============================================================" << std::endl;
    std::cout << "Native C++ Virtual Call Performance Baseline" << std::endl;
    std::cout << "C++ to C Transpiler - Virtual Function Dispatch" << std::endl;
    std::cout << "=============================================================" << std::endl;
    std::cout << std::endl;
    std::cout << "Baseline: Native C++ virtual call performance" << std::endl;
    std::cout << "Platform: Standard C++ virtual functions (compiler-specific)" << std::endl;
    std::cout << std::endl;
    std::cout << "NOTE: These timings are the baseline for comparison." << std::endl;
    std::cout << "      Compare with virtual_benchmark results to calculate" << std::endl;
    std::cout << "      transpiled runtime overhead percentage." << std::endl;
    std::cout << std::endl;
    std::cout << "=============================================================" << std::endl;
    std::cout << std::endl;

    // Run all benchmarks
    test_benchmark_single_inheritance();
    test_benchmark_multiple_inheritance();
    test_benchmark_deep_hierarchy();
    test_benchmark_virtual_destructor();
    test_benchmark_sequential_calls();

    std::cout << "=============================================================" << std::endl;
    std::cout << "Baseline Benchmark Complete" << std::endl;
    std::cout << "=============================================================" << std::endl;
    std::cout << std::endl;
    std::cout << "COMPARISON GUIDE:" << std::endl;
    std::cout << "----------------" << std::endl;
    std::cout << "To calculate overhead:" << std::endl;
    std::cout << "  1. Run ./virtual_benchmark (C transpiled version)" << std::endl;
    std::cout << "  2. Run ./virtual_benchmark_cpp (this native baseline)" << std::endl;
    std::cout << "  3. For each test, calculate:" << std::endl;
    std::cout << "     overhead = (C_time - CPP_time) / CPP_time * 100%" << std::endl;
    std::cout << std::endl;
    std::cout << "TARGET: Overhead should be 0-2% for all scenarios" << std::endl;
    std::cout << std::endl;
    std::cout << "Example calculation:" << std::endl;
    std::cout << "  C time:   2.04 ns" << std::endl;
    std::cout << "  C++ time: 2.00 ns" << std::endl;
    std::cout << "  Overhead: (2.04 - 2.00) / 2.00 * 100% = 2.0%" << std::endl;
    std::cout << "  Result:   ✓ Within target range" << std::endl;
    std::cout << std::endl;
    std::cout << "Performance Notes:" << std::endl;
    std::cout << "  - Modern compilers optimize virtual calls aggressively" << std::endl;
    std::cout << "  - Branch prediction makes virtual calls very fast" << std::endl;
    std::cout << "  - Cache locality is critical for vtable performance" << std::endl;
    std::cout << "  - Hierarchy depth does NOT affect call speed (O(1))" << std::endl;
    std::cout << std::endl;

    return 0;
}

/**
 * @file rtti_benchmark.cpp
 * @brief Native C++ RTTI Performance Baseline
 *
 * Native C++ dynamic_cast baseline for comparison with transpiled C runtime.
 * Uses identical test scenarios to measure native performance.
 *
 * BENCHMARK BASELINE:
 * ===================
 * This file provides native C++ performance numbers for comparison.
 * Run both benchmarks and calculate overhead:
 *   overhead = (C_time - CPP_time) / CPP_time * 100%
 *
 * Target: Transpiled C should have 10-20% overhead vs these baselines.
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only benchmarks native C++ RTTI
 * - Open/Closed: Extensible for new benchmark scenarios
 * - Dependency Inversion: Uses standard C++ RTTI
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
// Test Data Structures
// ============================================================================

// Simple single inheritance hierarchy: Base <- Derived
class Base {
public:
    virtual ~Base() {}
    int base_data;
};

class Derived : public Base {
public:
    int derived_data;
};

// Deep hierarchy: A <- B <- C <- D <- E
class A {
public:
    virtual ~A() {}
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
    int e;
};

// Multiple inheritance: Base1, Base2 <- Diamond
class Base1 {
public:
    virtual ~Base1() {}
    int data1;
};

class Base2 {
public:
    virtual ~Base2() {}
    int data2;
};

class Diamond : public Base1, public Base2 {
public:
    int diamond_data;
};

// Unrelated classes for failed cast tests
class Unrelated {
public:
    virtual ~Unrelated() {}
    int data;
};

// ============================================================================
// Benchmark 1: Successful Upcast (Base Class Cast)
// ============================================================================

void benchmark_upcast_native(int iterations) {
    Derived obj;
    obj.base_data = 42;
    obj.derived_data = 100;

    Base *base_ptr = &obj;

    // Benchmark: dynamic_cast from Base* to Derived*
    for (int i = 0; i < iterations; i++) {
        Derived *result = dynamic_cast<Derived *>(base_ptr);
        // Prevent optimization
        if (result == nullptr) std::abort();
    }
}

void test_benchmark_upcast() {
    std::cout << "Benchmark 1: Successful upcast (dynamic_cast<Derived*>(Base*))" << std::endl;

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_upcast_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_upcast_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);

    std::cout << "  Iterations:     " << ITERATIONS << std::endl;
    std::cout << "  Total time:     " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per cast:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:     " << 1000.0 / ns_per_op << " M ops/sec" << std::endl;

    std::cout << "  Status:         ";
    if (ns_per_op < 50.0) {
        std::cout << "✓ EXCELLENT (< 50ns per cast)" << std::endl;
    } else if (ns_per_op < 100.0) {
        std::cout << "✓ GOOD (< 100ns per cast)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Benchmark 2: Failed Cast (Unrelated Types)
// ============================================================================

void benchmark_failed_cast_native(int iterations) {
    Derived obj;
    obj.base_data = 42;
    obj.derived_data = 100;

    Base *base_ptr = &obj;

    // Benchmark: dynamic_cast to unrelated type (should fail)
    for (int i = 0; i < iterations; i++) {
        Unrelated *result = dynamic_cast<Unrelated *>(base_ptr);
        // Should always return nullptr
        if (result != nullptr) std::abort();
    }
}

void test_benchmark_failed_cast() {
    std::cout << "Benchmark 2: Failed cast (unrelated types)" << std::endl;

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_failed_cast_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_failed_cast_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);

    std::cout << "  Iterations:     " << ITERATIONS << std::endl;
    std::cout << "  Total time:     " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per cast:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:     " << 1000.0 / ns_per_op << " M ops/sec" << std::endl;

    std::cout << "  Status:         ";
    if (ns_per_op < 30.0) {
        std::cout << "✓ EXCELLENT (< 30ns - fast rejection)" << std::endl;
    } else if (ns_per_op < 60.0) {
        std::cout << "✓ GOOD (< 60ns - fast rejection)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Benchmark 3: Cross-Cast (Sibling Classes)
// ============================================================================

void benchmark_cross_cast_native(int iterations) {
    Diamond obj;
    obj.data1 = 42;
    obj.data2 = 100;
    obj.diamond_data = 200;

    Base1 *base1_ptr = &obj;

    // Benchmark: Base1* -> Base2* via Diamond
    for (int i = 0; i < iterations; i++) {
        Base2 *result = dynamic_cast<Base2 *>(base1_ptr);
        // Should succeed
        if (result == nullptr) std::abort();
    }
}

void test_benchmark_cross_cast() {
    std::cout << "Benchmark 3: Cross-cast (Base1* -> Base2* via Diamond)" << std::endl;

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_cross_cast_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_cross_cast_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);

    std::cout << "  Iterations:     " << ITERATIONS << std::endl;
    std::cout << "  Total time:     " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per cast:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:     " << 1000.0 / ns_per_op << " M ops/sec" << std::endl;

    std::cout << "  Status:         ";
    if (ns_per_op < 80.0) {
        std::cout << "✓ EXCELLENT (< 80ns for cross-cast)" << std::endl;
    } else if (ns_per_op < 150.0) {
        std::cout << "✓ GOOD (< 150ns for cross-cast)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Benchmark 4: Deep Hierarchy Traversal
// ============================================================================

void benchmark_deep_hierarchy_native(int iterations) {
    E obj;
    obj.a = 1;
    obj.b = 2;
    obj.c = 3;
    obj.d = 4;
    obj.e = 5;

    A *a_ptr = &obj;

    // Benchmark: A* -> E* (traverse 4 levels)
    for (int i = 0; i < iterations; i++) {
        E *result = dynamic_cast<E *>(a_ptr);
        if (result == nullptr) std::abort();
    }
}

void test_benchmark_deep_hierarchy() {
    std::cout << "Benchmark 4: Deep hierarchy traversal (5 levels: A* -> E*)" << std::endl;

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

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
    std::cout << "  Time per cast:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:     " << 1000.0 / ns_per_op << " M ops/sec" << std::endl;

    std::cout << "  Status:         ";
    if (ns_per_op < 100.0) {
        std::cout << "✓ EXCELLENT (< 100ns for 5-level traversal)" << std::endl;
    } else if (ns_per_op < 200.0) {
        std::cout << "✓ GOOD (< 200ns for 5-level traversal)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Benchmark 5: Multiple Inheritance Cast with Offset
// ============================================================================

void benchmark_multiple_inheritance_native(int iterations) {
    Diamond obj;
    obj.data1 = 42;
    obj.data2 = 100;
    obj.diamond_data = 200;

    Diamond *diamond_ptr = &obj;

    // Benchmark: Diamond* -> Base2* (with offset)
    for (int i = 0; i < iterations; i++) {
        Base2 *result = dynamic_cast<Base2 *>(diamond_ptr);
        if (result == nullptr) std::abort();
    }
}

void test_benchmark_multiple_inheritance() {
    std::cout << "Benchmark 5: Multiple inheritance with offset (Diamond* -> Base2*)" << std::endl;

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

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
    std::cout << "  Time per cast:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:     " << 1000.0 / ns_per_op << " M ops/sec" << std::endl;

    std::cout << "  Status:         ";
    if (ns_per_op < 60.0) {
        std::cout << "✓ EXCELLENT (< 60ns with offset)" << std::endl;
    } else if (ns_per_op < 120.0) {
        std::cout << "✓ GOOD (< 120ns with offset)" << std::endl;
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
    std::cout << "Native C++ RTTI Performance Baseline" << std::endl;
    std::cout << "C++ to C Transpiler - Story #86 & #87" << std::endl;
    std::cout << "=============================================================" << std::endl;
    std::cout << std::endl;
    std::cout << "Baseline: Native C++ dynamic_cast performance" << std::endl;
    std::cout << "Platform: Standard C++ RTTI (compiler-specific)" << std::endl;
    std::cout << std::endl;
    std::cout << "NOTE: These timings are the baseline for comparison." << std::endl;
    std::cout << "      Compare with rtti_benchmark.c results to calculate" << std::endl;
    std::cout << "      transpiled runtime overhead percentage." << std::endl;
    std::cout << std::endl;
    std::cout << "=============================================================" << std::endl;
    std::cout << std::endl;

    // Run all benchmarks
    test_benchmark_upcast();
    test_benchmark_failed_cast();
    test_benchmark_cross_cast();
    test_benchmark_deep_hierarchy();
    test_benchmark_multiple_inheritance();

    std::cout << "=============================================================" << std::endl;
    std::cout << "Baseline Benchmark Complete" << std::endl;
    std::cout << "=============================================================" << std::endl;
    std::cout << std::endl;
    std::cout << "COMPARISON GUIDE:" << std::endl;
    std::cout << "----------------" << std::endl;
    std::cout << "To calculate overhead:" << std::endl;
    std::cout << "  1. Run ./rtti_benchmark (C transpiled version)" << std::endl;
    std::cout << "  2. Run ./rtti_benchmark_cpp (this native baseline)" << std::endl;
    std::cout << "  3. For each test, calculate:" << std::endl;
    std::cout << "     overhead = (C_time - CPP_time) / CPP_time * 100%" << std::endl;
    std::cout << std::endl;
    std::cout << "TARGET: Overhead should be 10-20% for all scenarios" << std::endl;
    std::cout << std::endl;
    std::cout << "Example calculation:" << std::endl;
    std::cout << "  C time:   60 ns" << std::endl;
    std::cout << "  C++ time: 50 ns" << std::endl;
    std::cout << "  Overhead: (60 - 50) / 50 * 100% = 20%" << std::endl;
    std::cout << "  Result:   ✓ Within target range" << std::endl;
    std::cout << std::endl;

    return 0;
}

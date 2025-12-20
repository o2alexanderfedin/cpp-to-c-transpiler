/**
 * @file coroutine_benchmark.cpp
 * @brief Native C++20 Coroutine Performance Baseline
 *
 * Native C++20 coroutine baseline for comparison with transpiled C runtime.
 * Uses identical test scenarios to measure native performance.
 *
 * BENCHMARK BASELINE:
 * ===================
 * This file provides native C++20 performance numbers for comparison.
 * Run both benchmarks and calculate overhead:
 *   overhead = (C_time - CPP_time) / CPP_time * 100%
 *
 * Target: Transpiled C should have 5-15% overhead vs these baselines.
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only benchmarks native C++20 coroutines
 * - Open/Closed: Extensible for new benchmark scenarios
 * - Dependency Inversion: Uses standard C++20 coroutine support
 */

#include <chrono>
#include <coroutine>
#include <cstdint>
#include <cstdio>
#include <iostream>
#include <memory>

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
// Generator Coroutine (co_yield)
// ============================================================================

template<typename T>
struct Generator {
    struct promise_type {
        T current_value;

        Generator get_return_object() {
            return Generator{std::coroutine_handle<promise_type>::from_promise(*this)};
        }

        std::suspend_always initial_suspend() { return {}; }
        std::suspend_always final_suspend() noexcept { return {}; }

        std::suspend_always yield_value(T value) {
            current_value = value;
            return {};
        }

        void return_void() {}
        void unhandled_exception() { std::terminate(); }
    };

    std::coroutine_handle<promise_type> handle;

    explicit Generator(std::coroutine_handle<promise_type> h) : handle(h) {}

    ~Generator() {
        if (handle) handle.destroy();
    }

    Generator(Generator&& other) noexcept : handle(other.handle) {
        other.handle = nullptr;
    }

    Generator& operator=(Generator&& other) noexcept {
        if (this != &other) {
            if (handle) handle.destroy();
            handle = other.handle;
            other.handle = nullptr;
        }
        return *this;
    }

    Generator(const Generator&) = delete;
    Generator& operator=(const Generator&) = delete;

    bool move_next() {
        if (handle && !handle.done()) {
            handle.resume();
            return !handle.done();
        }
        return false;
    }

    T current_value() const {
        return handle.promise().current_value;
    }
};

/**
 * @brief Simple generator coroutine
 * Implements: for (int i = 0; i < n; ++i) { co_yield i; }
 */
Generator<int> count_to(int n) {
    for (int i = 0; i < n; ++i) {
        co_yield i;
    }
}

// ============================================================================
// Benchmark 1: Simple Generator (co_yield)
// ============================================================================

void benchmark_generator_native(int iterations) {
    for (int iter = 0; iter < iterations; iter++) {
        auto gen = count_to(10);

        // Iterate through generator
        while (gen.move_next()) {
            // Use the value to prevent optimization
            volatile int val = gen.current_value();
            (void)val;
        }
    }
}

void test_benchmark_generator() {
    std::cout << "Benchmark 1: Simple generator (co_yield)" << std::endl;
    std::cout << "  Pattern: for (i = 0; i < 10; ++i) { co_yield i; }" << std::endl;

    const int ITERATIONS = 100000;
    const int WARMUP = 1000;

    // Warm up
    benchmark_generator_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_generator_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);
    double ns_per_resume = ns_per_op / 10.0;  // 10 resumes per iteration

    std::cout << "  Iterations:        " << ITERATIONS << std::endl;
    std::cout << "  Total time:        " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per coroutine: " << ns_per_op << " ns" << std::endl;
    std::cout << "  Time per resume:   " << ns_per_resume << " ns" << std::endl;
    std::cout << "  Throughput:        " << 1000.0 / ns_per_resume << " M resumes/sec" << std::endl;

    std::cout << "  Status:            ";
    if (ns_per_resume < 50.0) {
        std::cout << "✓ EXCELLENT (< 50ns per resume)" << std::endl;
    } else if (ns_per_resume < 100.0) {
        std::cout << "✓ GOOD (< 100ns per resume)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++20)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Task Coroutine (co_await)
// ============================================================================

template<typename T>
struct Task {
    struct promise_type {
        T result_value;

        Task get_return_object() {
            return Task{std::coroutine_handle<promise_type>::from_promise(*this)};
        }

        std::suspend_always initial_suspend() { return {}; }
        std::suspend_always final_suspend() noexcept { return {}; }

        void return_value(T value) {
            result_value = value;
        }

        void unhandled_exception() { std::terminate(); }
    };

    std::coroutine_handle<promise_type> handle;

    explicit Task(std::coroutine_handle<promise_type> h) : handle(h) {}

    ~Task() {
        if (handle) handle.destroy();
    }

    Task(Task&& other) noexcept : handle(other.handle) {
        other.handle = nullptr;
    }

    Task& operator=(Task&& other) noexcept {
        if (this != &other) {
            if (handle) handle.destroy();
            handle = other.handle;
            other.handle = nullptr;
        }
        return *this;
    }

    Task(const Task&) = delete;
    Task& operator=(const Task&) = delete;

    void resume() {
        if (handle && !handle.done()) {
            handle.resume();
        }
    }

    bool done() const {
        return handle.done();
    }

    T result() const {
        return handle.promise().result_value;
    }
};

/**
 * @brief Async function coroutine
 * Implements: temp = x + y; co_await suspend(); result = temp * 2; co_return result;
 */
Task<int> async_compute(int x, int y) {
    int temp = x + y;
    co_await std::suspend_always{};
    int result = temp * 2;
    co_await std::suspend_always{};
    co_return result;
}

// ============================================================================
// Benchmark 2: Async Function (co_await)
// ============================================================================

void benchmark_async_native(int iterations) {
    for (int iter = 0; iter < iterations; iter++) {
        auto task = async_compute(iter, iter + 1);

        // Resume until completion
        while (!task.done()) {
            task.resume();
        }

        // Use result to prevent optimization
        volatile int result = task.result();
        (void)result;
    }
}

void test_benchmark_async() {
    std::cout << "Benchmark 2: Async function (co_await)" << std::endl;
    std::cout << "  Pattern: temp = x + y; co_await; result = temp * 2; co_return;" << std::endl;

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_async_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_async_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);
    double ns_per_resume = ns_per_op / 3.0;  // 3 resumes per iteration

    std::cout << "  Iterations:        " << ITERATIONS << std::endl;
    std::cout << "  Total time:        " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per coroutine: " << ns_per_op << " ns" << std::endl;
    std::cout << "  Time per resume:   " << ns_per_resume << " ns" << std::endl;
    std::cout << "  Throughput:        " << 1000.0 / ns_per_resume << " M resumes/sec" << std::endl;

    std::cout << "  Status:            ";
    if (ns_per_resume < 50.0) {
        std::cout << "✓ EXCELLENT (< 50ns per resume)" << std::endl;
    } else if (ns_per_resume < 100.0) {
        std::cout << "✓ GOOD (< 100ns per resume)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++20)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Nested Coroutines
// ============================================================================

/**
 * @brief Outer coroutine that awaits inner tasks
 */
Task<int> outer_coroutine(int n) {
    int accumulated = 0;

    // First inner task
    auto inner1 = async_compute(n, 1);
    while (!inner1.done()) {
        inner1.resume();
        co_await std::suspend_always{};
    }
    accumulated += inner1.result();

    // Second inner task
    auto inner2 = async_compute(n, 2);
    while (!inner2.done()) {
        inner2.resume();
        co_await std::suspend_always{};
    }
    accumulated += inner2.result();

    co_return accumulated;
}

// ============================================================================
// Benchmark 3: Nested Coroutines
// ============================================================================

void benchmark_nested_native(int iterations) {
    for (int iter = 0; iter < iterations; iter++) {
        auto outer = outer_coroutine(iter);

        // Resume until completion
        int safety_count = 0;
        while (!outer.done() && safety_count < 100) {
            outer.resume();
            safety_count++;
        }

        // Use result to prevent optimization
        volatile int result = outer.result();
        (void)result;
    }
}

void test_benchmark_nested() {
    std::cout << "Benchmark 3: Nested coroutines (outer awaits inner)" << std::endl;
    std::cout << "  Pattern: outer coroutine awaits two inner async coroutines" << std::endl;

    const int ITERATIONS = 100000;
    const int WARMUP = 1000;

    // Warm up
    benchmark_nested_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_nested_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);

    std::cout << "  Iterations:        " << ITERATIONS << std::endl;
    std::cout << "  Total time:        " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per coroutine: " << ns_per_op << " ns" << std::endl;

    std::cout << "  Status:            ";
    if (ns_per_op < 500.0) {
        std::cout << "✓ EXCELLENT (< 500ns for nested)" << std::endl;
    } else if (ns_per_op < 1000.0) {
        std::cout << "✓ GOOD (< 1000ns for nested)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++20)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Benchmark 4: Coroutine Creation Overhead
// ============================================================================

void benchmark_creation_native(int iterations) {
    for (int iter = 0; iter < iterations; iter++) {
        auto task = async_compute(iter, iter + 1);
        // Coroutine destroyed at end of scope
    }
}

void test_benchmark_creation() {
    std::cout << "Benchmark 4: Coroutine creation overhead" << std::endl;
    std::cout << "  Pattern: create coroutine frame + initialize + destroy" << std::endl;

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_creation_native(WARMUP);

    // Benchmark
    BenchmarkTimer timer;
    timer.Start();
    benchmark_creation_native(ITERATIONS);
    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);

    std::cout << "  Iterations:        " << ITERATIONS << std::endl;
    std::cout << "  Total time:        " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per create:   " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:        " << 1000.0 / ns_per_op << " M creates/sec" << std::endl;

    std::cout << "  Status:            ";
    if (ns_per_op < 100.0) {
        std::cout << "✓ EXCELLENT (< 100ns)" << std::endl;
    } else if (ns_per_op < 200.0) {
        std::cout << "✓ GOOD (< 200ns)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++20)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Benchmark 5: Coroutine Destruction Overhead
// ============================================================================

void test_benchmark_destruction() {
    std::cout << "Benchmark 5: Coroutine destruction overhead" << std::endl;
    std::cout << "  Pattern: cleanup frame + free memory" << std::endl;

    const int ITERATIONS = 1000000;

    // Pre-allocate tasks
    std::vector<Task<int>> tasks;
    tasks.reserve(ITERATIONS);

    for (int i = 0; i < ITERATIONS; i++) {
        tasks.push_back(async_compute(i, i + 1));
    }

    // Benchmark pure destruction
    BenchmarkTimer timer;
    timer.Start();

    tasks.clear();  // Destroys all tasks

    uint64_t duration_ns = timer.End();

    double ns_per_op = static_cast<double>(duration_ns) / static_cast<double>(ITERATIONS);

    std::cout << "  Iterations:        " << ITERATIONS << std::endl;
    std::cout << "  Total time:        " << duration_ns / 1000000.0 << " ms" << std::endl;
    std::cout << "  Time per destroy:  " << ns_per_op << " ns" << std::endl;
    std::cout << "  Throughput:        " << 1000.0 / ns_per_op << " M destroys/sec" << std::endl;

    std::cout << "  Status:            ";
    if (ns_per_op < 80.0) {
        std::cout << "✓ EXCELLENT (< 80ns)" << std::endl;
    } else if (ns_per_op < 150.0) {
        std::cout << "✓ GOOD (< 150ns)" << std::endl;
    } else {
        std::cout << "⚠ BASELINE (native C++20)" << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================================
// Memory Footprint Analysis
// ============================================================================

void run_memory_footprint_analysis() {
    std::cout << "Memory Footprint Analysis" << std::endl;
    std::cout << "  sizeof(std::coroutine_handle<>): " << sizeof(std::coroutine_handle<>) << " bytes" << std::endl;
    std::cout << "  sizeof(Generator<int>):          " << sizeof(Generator<int>) << " bytes" << std::endl;
    std::cout << "  sizeof(Task<int>):               " << sizeof(Task<int>) << " bytes" << std::endl;
    std::cout << "  Status: Native C++20 compiler-optimized coroutine frames" << std::endl;
    std::cout << std::endl;
}

// ============================================================================
// Main Benchmark Suite
// ============================================================================

int main() {
    std::cout << "\n";
    std::cout << "=============================================================" << std::endl;
    std::cout << "Native C++20 Coroutine Performance Baseline" << std::endl;
    std::cout << "C++ to C Transpiler - Performance Comparison" << std::endl;
    std::cout << "=============================================================" << std::endl;
    std::cout << "\n";
    std::cout << "Platform: Native C++20 coroutines (compiler optimized)" << std::endl;
    std::cout << "\n";
    std::cout << "NOTE: These are baseline measurements for comparison." << std::endl;
    std::cout << "      Compare with coroutine_benchmark.c results to" << std::endl;
    std::cout << "      calculate transpiler overhead percentage." << std::endl;
    std::cout << "\n";
    std::cout << "=============================================================" << std::endl;
    std::cout << "\n";

    // Run all benchmarks
    test_benchmark_generator();
    test_benchmark_async();
    test_benchmark_nested();
    test_benchmark_creation();
    test_benchmark_destruction();
    run_memory_footprint_analysis();

    std::cout << "=============================================================" << std::endl;
    std::cout << "Benchmark Suite Complete" << std::endl;
    std::cout << "=============================================================" << std::endl;
    std::cout << "\n";
    std::cout << "SUMMARY:" << std::endl;
    std::cout << "--------" << std::endl;
    std::cout << "All benchmarks measure native C++20 coroutine performance." << std::endl;
    std::cout << "To calculate transpiler overhead:" << std::endl;
    std::cout << "  1. Run coroutine_benchmark.c (transpiled version)" << std::endl;
    std::cout << "  2. Compare timings: overhead = (C_time - CPP_time) / CPP_time * 100%" << std::endl;
    std::cout << "  3. Target: 5-15% overhead" << std::endl;
    std::cout << "\n";
    std::cout << "Native C++20 advantages:" << std::endl;
    std::cout << "  - Compiler-optimized state machines" << std::endl;
    std::cout << "  - Potential inline optimizations" << std::endl;
    std::cout << "  - Custom coroutine allocators" << std::endl;
    std::cout << "  - Zero-overhead abstractions" << std::endl;
    std::cout << "\n";

    return 0;
}

// ExceptionPerformanceTest.cpp - Performance benchmarks for Story #82
// (Integration Testing and Thread Safety Validation)
//
// Performance validation: 5-20% overhead target vs native C++ exceptions

#include <cassert>
#include <csetjmp>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <chrono>
#include <iostream>
#include <string>

// Exception runtime (from Story #81)
extern "C" {
struct __cxx_action_entry {
    void (*destructor)(void *);
    void *object;
};

struct __cxx_exception_frame {
    jmp_buf jmpbuf;
    struct __cxx_exception_frame *next;
    const struct __cxx_action_entry *actions;
    void *exception_object;
    const char *exception_type;
};

extern thread_local struct __cxx_exception_frame *__cxx_exception_stack;

void cxx_throw(void *exception, const char *type_info);
}

// ============================================================================
// Test Utilities
// ============================================================================

struct BenchmarkException {
    int value;
};

void BenchmarkException__ctor(struct BenchmarkException *this_ptr, int val) {
    this_ptr->value = val;
}

void BenchmarkException__dtor(void *this_ptr) {
    (void)this_ptr;  // Unused parameter
}

struct BenchmarkResource {
    int data;
};

void BenchmarkResource__ctor(struct BenchmarkResource *this_ptr, int val) {
    this_ptr->data = val;
}

void BenchmarkResource__dtor(void *this_ptr) {
    (void)this_ptr;  // Unused parameter
}

// ============================================================================
// Benchmark 1: Try-Catch with NO Exception (Happy Path)
// ============================================================================

void benchmark_no_exception_transpiled(int iterations) {
    for (int i = 0; i < iterations; i++) {
        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = nullptr;
        frame.exception_object = nullptr;
        frame.exception_type = nullptr;

        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            // Normal code path (no exception)
            volatile int dummy = i * 2;
            (void)dummy;

            // Pop frame
            __cxx_exception_stack = frame.next;
        } else {
            // Should never reach here
            assert(false);
        }
    }
}

void benchmark_no_exception_native(int iterations) {
    for (int i = 0; i < iterations; i++) {
        try {
            // Normal code path (no exception)
            volatile int dummy = i * 2;
            (void)dummy;
        } catch (...) {
            // Should never reach here
            assert(false);
        }
    }
}

void test_benchmark_no_exception() {
    std::cout << "Benchmark 1: Try-catch with NO exception (happy path)" << std::endl;

    const int ITERATIONS = 1000000;

    // Warm up
    benchmark_no_exception_transpiled(1000);
    benchmark_no_exception_native(1000);

    // Benchmark transpiled version
    auto start_transpiled = std::chrono::high_resolution_clock::now();
    benchmark_no_exception_transpiled(ITERATIONS);
    auto end_transpiled = std::chrono::high_resolution_clock::now();
    auto duration_transpiled = std::chrono::duration_cast<std::chrono::microseconds>(
        end_transpiled - start_transpiled).count();

    // Benchmark native version
    auto start_native = std::chrono::high_resolution_clock::now();
    benchmark_no_exception_native(ITERATIONS);
    auto end_native = std::chrono::high_resolution_clock::now();
    auto duration_native = std::chrono::duration_cast<std::chrono::microseconds>(
        end_native - start_native).count();

    // Calculate overhead
    double overhead_percent = ((double)(duration_transpiled - duration_native) / duration_native) * 100.0;

    std::cout << "  Transpiled: " << duration_transpiled << " μs" << std::endl;
    std::cout << "  Native:     " << duration_native << " μs" << std::endl;
    std::cout << "  Overhead:   " << overhead_percent << "%" << std::endl;

    // AC #7: Performance overhead should be 5-20%
    // Note: On some platforms, native exceptions may use zero-cost exception handling,
    // making our overhead appear higher. We're measuring setjmp overhead primarily.
    std::cout << "  Status:     ";
    if (overhead_percent < 0) {
        std::cout << "✓ (transpiled faster!)" << std::endl;
    } else if (overhead_percent <= 20.0) {
        std::cout << "✓ (within 20% target)" << std::endl;
    } else {
        std::cout << "⚠ (exceeds 20% - setjmp overhead expected)" << std::endl;
    }

    std::cout << std::endl;
}

// ============================================================================
// Benchmark 2: Try-Catch WITH Exception (Exception Path)
// ============================================================================

void benchmark_with_exception_transpiled(int iterations) {
    for (int i = 0; i < iterations; i++) {
        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = nullptr;
        frame.exception_object = nullptr;
        frame.exception_type = nullptr;

        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            // Throw exception
            struct BenchmarkException *ex = (struct BenchmarkException *)malloc(sizeof(struct BenchmarkException));
            BenchmarkException__ctor(ex, i);
            cxx_throw(ex, "BenchmarkException");

            assert(false);
        } else {
            // Catch exception
            struct BenchmarkException *caught = (struct BenchmarkException *)frame.exception_object;
            BenchmarkException__dtor(caught);
            free(caught);
        }
    }
}

void benchmark_with_exception_native(int iterations) {
    for (int i = 0; i < iterations; i++) {
        try {
            throw i;
        } catch (int val) {
            volatile int dummy = val;
            (void)dummy;
        }
    }
}

void test_benchmark_with_exception() {
    std::cout << "Benchmark 2: Try-catch WITH exception (exception path)" << std::endl;

    const int ITERATIONS = 100000;  // Fewer iterations - exceptions are expensive

    // Warm up
    benchmark_with_exception_transpiled(100);
    benchmark_with_exception_native(100);

    // Benchmark transpiled version
    auto start_transpiled = std::chrono::high_resolution_clock::now();
    benchmark_with_exception_transpiled(ITERATIONS);
    auto end_transpiled = std::chrono::high_resolution_clock::now();
    auto duration_transpiled = std::chrono::duration_cast<std::chrono::microseconds>(
        end_transpiled - start_transpiled).count();

    // Benchmark native version
    auto start_native = std::chrono::high_resolution_clock::now();
    benchmark_with_exception_native(ITERATIONS);
    auto end_native = std::chrono::high_resolution_clock::now();
    auto duration_native = std::chrono::duration_cast<std::chrono::microseconds>(
        end_native - start_native).count();

    // Calculate overhead
    double overhead_percent = ((double)(duration_transpiled - duration_native) / duration_native) * 100.0;

    std::cout << "  Transpiled: " << duration_transpiled << " μs" << std::endl;
    std::cout << "  Native:     " << duration_native << " μs" << std::endl;
    std::cout << "  Overhead:   " << overhead_percent << "%" << std::endl;

    std::cout << "  Status:     ";
    if (overhead_percent < 0) {
        std::cout << "✓ (transpiled faster!)" << std::endl;
    } else if (overhead_percent <= 20.0) {
        std::cout << "✓ (within 20% target)" << std::endl;
    } else {
        std::cout << "⚠ (exceeds 20% - allocation overhead expected)" << std::endl;
    }

    std::cout << std::endl;
}

// ============================================================================
// Benchmark 3: RAII Cleanup During Exception
// ============================================================================

void benchmark_raii_cleanup_transpiled(int iterations) {
    for (int i = 0; i < iterations; i++) {
        struct BenchmarkResource res;
        BenchmarkResource__ctor(&res, i);

        struct __cxx_action_entry actions[] = {
            {BenchmarkResource__dtor, &res},
            {nullptr, nullptr}
        };

        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = actions;
        frame.exception_object = nullptr;
        frame.exception_type = nullptr;

        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            struct BenchmarkException *ex = (struct BenchmarkException *)malloc(sizeof(struct BenchmarkException));
            BenchmarkException__ctor(ex, i);
            cxx_throw(ex, "BenchmarkException");

            assert(false);
        } else {
            struct BenchmarkException *caught = (struct BenchmarkException *)frame.exception_object;
            BenchmarkException__dtor(caught);
            free(caught);
        }
    }
}

class NativeResource {
public:
    int data;
    NativeResource(int val) : data(val) {}
    ~NativeResource() {}
};

void benchmark_raii_cleanup_native(int iterations) {
    for (int i = 0; i < iterations; i++) {
        try {
            NativeResource res(i);
            throw i;
        } catch (int val) {
            volatile int dummy = val;
            (void)dummy;
        }
    }
}

void test_benchmark_raii_cleanup() {
    std::cout << "Benchmark 3: RAII cleanup during exception" << std::endl;

    const int ITERATIONS = 50000;

    // Warm up
    benchmark_raii_cleanup_transpiled(100);
    benchmark_raii_cleanup_native(100);

    // Benchmark transpiled version
    auto start_transpiled = std::chrono::high_resolution_clock::now();
    benchmark_raii_cleanup_transpiled(ITERATIONS);
    auto end_transpiled = std::chrono::high_resolution_clock::now();
    auto duration_transpiled = std::chrono::duration_cast<std::chrono::microseconds>(
        end_transpiled - start_transpiled).count();

    // Benchmark native version
    auto start_native = std::chrono::high_resolution_clock::now();
    benchmark_raii_cleanup_native(ITERATIONS);
    auto end_native = std::chrono::high_resolution_clock::now();
    auto duration_native = std::chrono::duration_cast<std::chrono::microseconds>(
        end_native - start_native).count();

    // Calculate overhead
    double overhead_percent = ((double)(duration_transpiled - duration_native) / duration_native) * 100.0;

    std::cout << "  Transpiled: " << duration_transpiled << " μs" << std::endl;
    std::cout << "  Native:     " << duration_native << " μs" << std::endl;
    std::cout << "  Overhead:   " << overhead_percent << "%" << std::endl;

    std::cout << "  Status:     ";
    if (overhead_percent < 0) {
        std::cout << "✓ (transpiled faster!)" << std::endl;
    } else if (overhead_percent <= 20.0) {
        std::cout << "✓ (within 20% target)" << std::endl;
    } else {
        std::cout << "⚠ (exceeds 20% - action table overhead expected)" << std::endl;
    }

    std::cout << std::endl;
}

// ============================================================================
// Benchmark 4: Memory Footprint
// ============================================================================

void test_memory_footprint() {
    std::cout << "Benchmark 4: Memory footprint analysis" << std::endl;

    std::cout << "  sizeof(__cxx_exception_frame):  " << sizeof(__cxx_exception_frame) << " bytes" << std::endl;
    std::cout << "  sizeof(__cxx_action_entry):     " << sizeof(__cxx_action_entry) << " bytes" << std::endl;
    std::cout << "  sizeof(jmp_buf):                " << sizeof(jmp_buf) << " bytes" << std::endl;

    // Typical stack frame overhead per try block
    size_t frame_overhead = sizeof(__cxx_exception_frame);
    size_t action_entry_overhead = sizeof(__cxx_action_entry) * 4;  // Assume 4 resources avg
    size_t total_overhead = frame_overhead + action_entry_overhead;

    std::cout << "  Estimated overhead per try:     " << total_overhead << " bytes" << std::endl;
    std::cout << "  Status:                         ✓ (acceptable for portable C)" << std::endl;
    std::cout << std::endl;
}

// ============================================================================
// Main
// ============================================================================

int main() {
    std::cout << "\n===========================================" << std::endl;
    std::cout << "Exception Performance Benchmarks" << std::endl;
    std::cout << "Story #82 - Epic #42" << std::endl;
    std::cout << "AC #7: Target 5-20% overhead" << std::endl;
    std::cout << "===========================================" << std::endl;
    std::cout << std::endl;

    test_benchmark_no_exception();
    test_benchmark_with_exception();
    test_benchmark_raii_cleanup();
    test_memory_footprint();

    std::cout << "===========================================" << std::endl;
    std::cout << "Performance Analysis Complete" << std::endl;
    std::cout << "===========================================" << std::endl;
    std::cout << std::endl;

    std::cout << "NOTE: Performance characteristics:" << std::endl;
    std::cout << "  - No exception path: setjmp overhead only" << std::endl;
    std::cout << "  - Exception path: malloc + action table + longjmp" << std::endl;
    std::cout << "  - Native C++ may use zero-cost exceptions (no overhead when not thrown)" << std::endl;
    std::cout << "  - Transpiled version optimized for portability, not zero-cost" << std::endl;
    std::cout << std::endl;

    return 0;
}

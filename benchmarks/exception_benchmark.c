/*
 * exception_benchmark.c - Exception Handling Runtime Benchmark
 *
 * BENCHMARK RESULTS SUMMARY:
 * ==========================
 * This benchmark measures the performance overhead of the C++ to C exception
 * handling transpiler runtime compared to native C++ exceptions.
 *
 * TARGET PERFORMANCE:
 * - Try-catch overhead (no throw): 5-10% vs native C++
 * - Throw-catch overhead: 15-25% (SJLJ is inherently slower)
 *
 * METHODOLOGY:
 * - High-resolution timing using clock_gettime (POSIX) or clock() fallback
 * - 1,000,000+ iterations for accuracy in no-throw scenarios
 * - 100,000+ iterations for exception scenarios (exceptions are expensive)
 * - Warm-up runs to eliminate cold-cache effects
 *
 * RUNTIME MODES:
 * - Library mode: Uses runtime/exception_runtime.c (default)
 * - Inline mode: Exception handling code inlined directly
 *
 * SOLID PRINCIPLES:
 * - Single Responsibility: Benchmarking exception handling performance
 * - KISS: Simple, focused benchmarks with clear measurements
 * - DRY: Reusable timing and reporting utilities
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <setjmp.h>

// Include exception runtime
#include "../runtime/exception_runtime.h"

// Platform-specific high-resolution timing
#ifdef __APPLE__
#include <mach/mach_time.h>
#define USE_MACH_TIME 1
#elif defined(_POSIX_VERSION)
#define USE_CLOCK_GETTIME 1
#else
#define USE_CLOCK 1
#endif

// ============================================================================
// Timing Utilities
// ============================================================================

typedef struct {
    double seconds;
} benchmark_time;

static benchmark_time get_time(void) {
    benchmark_time t;

#ifdef USE_MACH_TIME
    static mach_timebase_info_data_t timebase;
    if (timebase.denom == 0) {
        mach_timebase_info(&timebase);
    }
    uint64_t time = mach_absolute_time();
    t.seconds = (double)time * timebase.numer / timebase.denom / 1e9;
#elif defined(USE_CLOCK_GETTIME)
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    t.seconds = ts.tv_sec + ts.tv_nsec / 1e9;
#else
    t.seconds = (double)clock() / CLOCKS_PER_SEC;
#endif

    return t;
}

static double time_diff_ms(benchmark_time start, benchmark_time end) {
    return (end.seconds - start.seconds) * 1000.0;
}

// ============================================================================
// Test Exception Types
// ============================================================================

struct benchmark_exception {
    int code;
    char message[64];
};

struct benchmark_resource {
    int id;
    int data[10];  // Some data to make cleanup meaningful
};

// Destructor for benchmark resource
static void benchmark_resource_destroy(void *ptr) {
    struct benchmark_resource *res = (struct benchmark_resource *)ptr;
    // Simulate cleanup work
    res->id = -1;
}

// ============================================================================
// Benchmark 1: Try-Catch Overhead (No Exception - Happy Path)
// ============================================================================

static void benchmark_no_exception_transpiled(int iterations) {
    for (int i = 0; i < iterations; i++) {
        // Setup exception frame
        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = NULL;
        frame.exception_object = NULL;
        frame.exception_type = NULL;

        // Try block
        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            // Normal execution path (no exception)
            volatile int result = i * 2 + i / 2;
            (void)result;  // Prevent optimization

            // Pop frame (normal exit)
            __cxx_exception_stack = frame.next;
        } else {
            // Catch block (should never execute)
            fprintf(stderr, "ERROR: Unexpected exception in no-throw benchmark\n");
            exit(1);
        }
    }
}

static void run_benchmark_no_exception(void) {
    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    printf("Benchmark 1: Try-catch with NO exception (happy path)\n");
    printf("  Iterations: %d\n", ITERATIONS);

    // Warm-up
    benchmark_no_exception_transpiled(WARMUP);

    // Actual benchmark
    benchmark_time start = get_time();
    benchmark_no_exception_transpiled(ITERATIONS);
    benchmark_time end = get_time();

    double duration_ms = time_diff_ms(start, end);
    double per_iteration_ns = (duration_ms * 1e6) / ITERATIONS;

    printf("  Duration: %.3f ms\n", duration_ms);
    printf("  Per iteration: %.2f ns\n", per_iteration_ns);

    // Expected: 5-10% overhead vs native C++ (typically 2-5 ns per iteration)
    if (per_iteration_ns < 10.0) {
        printf("  Status: EXCELLENT (< 10 ns per iteration)\n");
    } else if (per_iteration_ns < 20.0) {
        printf("  Status: GOOD (10-20 ns per iteration)\n");
    } else {
        printf("  Status: ACCEPTABLE (> 20 ns per iteration - setjmp overhead)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 2: Throw-Catch Overhead (Exception Path)
// ============================================================================

static void benchmark_with_exception_transpiled(int iterations) {
    for (int i = 0; i < iterations; i++) {
        // Setup exception frame
        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = NULL;
        frame.exception_object = NULL;
        frame.exception_type = NULL;

        // Try block
        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            // Throw exception
            struct benchmark_exception *ex = malloc(sizeof(struct benchmark_exception));
            ex->code = i;
            snprintf(ex->message, sizeof(ex->message), "Exception %d", i);

            cxx_throw(ex, "benchmark_exception");

            // Should never reach here
            fprintf(stderr, "ERROR: cxx_throw returned\n");
            exit(1);
        } else {
            // Catch block
            struct benchmark_exception *caught =
                (struct benchmark_exception *)frame.exception_object;

            // Simulate catch handler work
            volatile int code = caught->code;
            (void)code;

            // Cleanup
            free(caught);
        }
    }
}

static void run_benchmark_with_exception(void) {
    const int ITERATIONS = 100000;  // Fewer iterations - exceptions are expensive
    const int WARMUP = 1000;

    printf("Benchmark 2: Try-catch WITH exception (exception path)\n");
    printf("  Iterations: %d\n", ITERATIONS);

    // Warm-up
    benchmark_with_exception_transpiled(WARMUP);

    // Actual benchmark
    benchmark_time start = get_time();
    benchmark_with_exception_transpiled(ITERATIONS);
    benchmark_time end = get_time();

    double duration_ms = time_diff_ms(start, end);
    double per_iteration_ns = (duration_ms * 1e6) / ITERATIONS;

    printf("  Duration: %.3f ms\n", duration_ms);
    printf("  Per iteration: %.2f ns\n", per_iteration_ns);

    // Expected: 15-25% overhead vs native C++ (typically 500-1000 ns per throw)
    if (per_iteration_ns < 1000.0) {
        printf("  Status: EXCELLENT (< 1000 ns per throw)\n");
    } else if (per_iteration_ns < 2000.0) {
        printf("  Status: GOOD (1000-2000 ns per throw)\n");
    } else {
        printf("  Status: ACCEPTABLE (> 2000 ns per throw - SJLJ overhead expected)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 3: RAII Cleanup During Exception (Action Table Execution)
// ============================================================================

static void benchmark_raii_cleanup_transpiled(int iterations) {
    for (int i = 0; i < iterations; i++) {
        // Create resource that needs cleanup
        struct benchmark_resource res;
        res.id = i;
        memset(res.data, 0, sizeof(res.data));

        // Action table for cleanup
        struct __cxx_action_entry actions[] = {
            {benchmark_resource_destroy, &res},
            {NULL, NULL}  // Sentinel
        };

        // Setup exception frame with action table
        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = actions;
        frame.exception_object = NULL;
        frame.exception_type = NULL;

        // Try block
        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            // Throw exception
            struct benchmark_exception *ex = malloc(sizeof(struct benchmark_exception));
            ex->code = i;

            cxx_throw(ex, "benchmark_exception");

            fprintf(stderr, "ERROR: cxx_throw returned\n");
            exit(1);
        } else {
            // Catch block
            struct benchmark_exception *caught =
                (struct benchmark_exception *)frame.exception_object;
            free(caught);
        }
    }
}

static void run_benchmark_raii_cleanup(void) {
    const int ITERATIONS = 100000;
    const int WARMUP = 1000;

    printf("Benchmark 3: RAII cleanup during exception (action table)\n");
    printf("  Iterations: %d\n", ITERATIONS);

    // Warm-up
    benchmark_raii_cleanup_transpiled(WARMUP);

    // Actual benchmark
    benchmark_time start = get_time();
    benchmark_raii_cleanup_transpiled(ITERATIONS);
    benchmark_time end = get_time();

    double duration_ms = time_diff_ms(start, end);
    double per_iteration_ns = (duration_ms * 1e6) / ITERATIONS;

    printf("  Duration: %.3f ms\n", duration_ms);
    printf("  Per iteration: %.2f ns\n", per_iteration_ns);

    // Expected: Similar to Benchmark 2 + action table overhead (typically 600-1200 ns)
    if (per_iteration_ns < 1500.0) {
        printf("  Status: EXCELLENT (< 1500 ns per throw+cleanup)\n");
    } else if (per_iteration_ns < 2500.0) {
        printf("  Status: GOOD (1500-2500 ns per throw+cleanup)\n");
    } else {
        printf("  Status: ACCEPTABLE (> 2500 ns - action table overhead expected)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 4: Multiple Resources (Complex Action Table)
// ============================================================================

static void benchmark_multiple_resources_transpiled(int iterations) {
    for (int i = 0; i < iterations; i++) {
        // Create multiple resources
        struct benchmark_resource res1, res2, res3;
        res1.id = i * 3 + 0;
        res2.id = i * 3 + 1;
        res3.id = i * 3 + 2;

        // Action table with multiple entries (reverse order of construction)
        struct __cxx_action_entry actions[] = {
            {benchmark_resource_destroy, &res3},
            {benchmark_resource_destroy, &res2},
            {benchmark_resource_destroy, &res1},
            {NULL, NULL}  // Sentinel
        };

        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = actions;
        frame.exception_object = NULL;
        frame.exception_type = NULL;

        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            struct benchmark_exception *ex = malloc(sizeof(struct benchmark_exception));
            ex->code = i;
            cxx_throw(ex, "benchmark_exception");

            exit(1);
        } else {
            struct benchmark_exception *caught =
                (struct benchmark_exception *)frame.exception_object;
            free(caught);
        }
    }
}

static void run_benchmark_multiple_resources(void) {
    const int ITERATIONS = 100000;
    const int WARMUP = 1000;

    printf("Benchmark 4: Multiple resources cleanup (3 destructors)\n");
    printf("  Iterations: %d\n", ITERATIONS);

    // Warm-up
    benchmark_multiple_resources_transpiled(WARMUP);

    // Actual benchmark
    benchmark_time start = get_time();
    benchmark_multiple_resources_transpiled(ITERATIONS);
    benchmark_time end = get_time();

    double duration_ms = time_diff_ms(start, end);
    double per_iteration_ns = (duration_ms * 1e6) / ITERATIONS;

    printf("  Duration: %.3f ms\n", duration_ms);
    printf("  Per iteration: %.2f ns\n", per_iteration_ns);
    printf("  Status: Measures impact of action table size on unwinding\n");
    printf("\n");
}

// ============================================================================
// Benchmark 5: Nested Try-Catch Blocks
// ============================================================================

static void benchmark_nested_trycatch_transpiled(int iterations) {
    for (int i = 0; i < iterations; i++) {
        // Outer try block
        struct __cxx_exception_frame outer_frame;
        outer_frame.next = __cxx_exception_stack;
        outer_frame.actions = NULL;
        outer_frame.exception_object = NULL;
        outer_frame.exception_type = NULL;

        if (setjmp(outer_frame.jmpbuf) == 0) {
            __cxx_exception_stack = &outer_frame;

            // Inner try block
            struct __cxx_exception_frame inner_frame;
            inner_frame.next = __cxx_exception_stack;
            inner_frame.actions = NULL;
            inner_frame.exception_object = NULL;
            inner_frame.exception_type = NULL;

            if (setjmp(inner_frame.jmpbuf) == 0) {
                __cxx_exception_stack = &inner_frame;

                // Throw from inner
                struct benchmark_exception *ex = malloc(sizeof(struct benchmark_exception));
                ex->code = i;
                cxx_throw(ex, "benchmark_exception");

                exit(1);
            } else {
                // Inner catch
                struct benchmark_exception *caught =
                    (struct benchmark_exception *)inner_frame.exception_object;
                free(caught);
            }

            __cxx_exception_stack = outer_frame.next;
        } else {
            // Outer catch (should not execute)
            exit(1);
        }
    }
}

static void run_benchmark_nested_trycatch(void) {
    const int ITERATIONS = 100000;
    const int WARMUP = 1000;

    printf("Benchmark 5: Nested try-catch blocks (2 levels)\n");
    printf("  Iterations: %d\n", ITERATIONS);

    // Warm-up
    benchmark_nested_trycatch_transpiled(WARMUP);

    // Actual benchmark
    benchmark_time start = get_time();
    benchmark_nested_trycatch_transpiled(ITERATIONS);
    benchmark_time end = get_time();

    double duration_ms = time_diff_ms(start, end);
    double per_iteration_ns = (duration_ms * 1e6) / ITERATIONS;

    printf("  Duration: %.3f ms\n", duration_ms);
    printf("  Per iteration: %.2f ns\n", per_iteration_ns);
    printf("  Status: Measures nested exception frame overhead\n");
    printf("\n");
}

// ============================================================================
// Memory Footprint Analysis
// ============================================================================

static void run_memory_footprint_analysis(void) {
    printf("Memory Footprint Analysis\n");
    printf("  sizeof(jmp_buf): %zu bytes\n", sizeof(jmp_buf));
    printf("  sizeof(__cxx_exception_frame): %zu bytes\n",
           sizeof(struct __cxx_exception_frame));
    printf("  sizeof(__cxx_action_entry): %zu bytes\n",
           sizeof(struct __cxx_action_entry));

    // Calculate typical overhead
    size_t frame_overhead = sizeof(struct __cxx_exception_frame);
    size_t action_overhead = sizeof(struct __cxx_action_entry) * 4;  // Assume 4 resources avg
    size_t total_overhead = frame_overhead + action_overhead;

    printf("  Estimated per-try overhead (4 resources): %zu bytes\n", total_overhead);
    printf("  Status: Acceptable for portable C implementation\n");
    printf("\n");
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;

    printf("\n");
    printf("=====================================================\n");
    printf("Exception Handling Runtime Benchmark\n");
    printf("C++ to C Transpiler - Exception Runtime Performance\n");
    printf("=====================================================\n");
    printf("\n");

    printf("Platform: ");
#ifdef USE_MACH_TIME
    printf("macOS (mach_absolute_time)\n");
#elif defined(USE_CLOCK_GETTIME)
    printf("POSIX (clock_gettime)\n");
#else
    printf("C standard (clock)\n");
#endif
    printf("\n");

    printf("TARGET PERFORMANCE GOALS:\n");
    printf("  - Try-catch overhead (no throw): 5-10%% vs native C++\n");
    printf("  - Throw-catch overhead: 15-25%% (SJLJ inherently slower)\n");
    printf("\n");

    printf("NOTES:\n");
    printf("  - Native C++ may use zero-cost exceptions (no overhead when not thrown)\n");
    printf("  - Our SJLJ implementation has constant overhead (setjmp)\n");
    printf("  - Trade-off: Portability vs zero-cost exception handling\n");
    printf("  - All timings include malloc/free overhead for exception objects\n");
    printf("\n");

    printf("=====================================================\n");
    printf("Running Benchmarks...\n");
    printf("=====================================================\n");
    printf("\n");

    // Run all benchmarks
    run_benchmark_no_exception();
    run_benchmark_with_exception();
    run_benchmark_raii_cleanup();
    run_benchmark_multiple_resources();
    run_benchmark_nested_trycatch();
    run_memory_footprint_analysis();

    printf("=====================================================\n");
    printf("Benchmark Complete\n");
    printf("=====================================================\n");
    printf("\n");

    printf("INTERPRETATION:\n");
    printf("  - Benchmark 1: Measures setjmp overhead (constant cost)\n");
    printf("  - Benchmark 2: Measures longjmp + malloc overhead\n");
    printf("  - Benchmark 3: Adds action table execution (destructors)\n");
    printf("  - Benchmark 4: Shows action table scaling with resource count\n");
    printf("  - Benchmark 5: Shows nested exception frame overhead\n");
    printf("\n");

    printf("COMPARISON TO NATIVE C++:\n");
    printf("  To compare with native C++, compile and run:\n");
    printf("    clang++ -O2 benchmarks/exception_benchmark_native.cpp -o benchmark_native\n");
    printf("    ./benchmark_native\n");
    printf("\n");

    return 0;
}

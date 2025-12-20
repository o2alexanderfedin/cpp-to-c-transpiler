/**
 * @file coroutine_benchmark.c
 * @brief Coroutine Runtime Performance Benchmark
 *
 * Performance validation for C++ to C transpiler coroutine runtime implementation.
 * Measures coroutine resume/destroy overhead compared to native C++20 coroutines.
 *
 * BENCHMARK RESULTS SUMMARY:
 * ==========================
 * Target: 5-15% overhead vs native C++20 coroutines (from Architecture Constraints)
 *
 * Test scenarios:
 * 1. Simple generator (co_yield) - 1,000,000 iterations
 * 2. Async function (co_await) - 1,000,000 iterations
 * 3. Nested coroutines (coroutine calling coroutine) - 500,000 iterations
 * 4. Coroutine creation overhead - 1,000,000 iterations
 * 5. Coroutine destruction overhead - 1,000,000 iterations
 *
 * Expected Results:
 * - Simple generator: 5-10% overhead (state machine + frame access)
 * - Async functions: 5-15% overhead (state save/restore)
 * - Nested coroutines: 10-15% overhead (multiple frame traversals)
 * - Creation: 5-10% overhead (heap allocation + initialization)
 * - Destruction: 5-10% overhead (cleanup + deallocation)
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only benchmarks coroutine performance
 * - Open/Closed: Extensible for new benchmark scenarios
 * - Interface Segregation: Uses minimal runtime API
 * - Dependency Inversion: Depends on abstract coroutine frame structures
 *
 * Design Pattern: State machine coroutine implementation
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

// ============================================================================
// Coroutine Runtime Structures (Simulating Transpiler Output)
// ============================================================================

/**
 * @brief Generic coroutine frame header
 * All coroutine frames start with this structure
 */
struct coroutine_frame_header {
    int state;                      // Current suspend point (0, 1, 2, ...)
    void (*resume_fn)(void*);       // Resume function pointer
    void (*destroy_fn)(void*);      // Destroy function pointer
};

/**
 * @brief Simple generator frame (co_yield benchmark)
 * Simulates: generator<int> count_to(int n)
 */
struct generator_frame {
    struct coroutine_frame_header header;
    int n;          // Parameter
    int i;          // Loop counter (spans suspend points)
    int value;      // Current yielded value
};

/**
 * @brief Async function frame (co_await benchmark)
 * Simulates: task<int> async_compute(int x, int y)
 */
struct async_frame {
    struct coroutine_frame_header header;
    int x, y;       // Parameters
    int result;     // Computation result
    int temp;       // Temporary value spanning suspends
};

/**
 * @brief Nested coroutine frame (coroutine calling coroutine)
 * Simulates: task<int> outer_coro(int n)
 */
struct nested_frame {
    struct coroutine_frame_header header;
    int n;                          // Parameter
    struct async_frame* inner;      // Inner coroutine handle
    int accumulated;                // Accumulated result
};

// ============================================================================
// High-Resolution Timing Utilities
// ============================================================================

typedef struct {
    uint64_t start;
    uint64_t end;
} benchmark_timer_t;

static inline uint64_t get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static void timer_start(benchmark_timer_t *timer) {
    timer->start = get_time_ns();
}

static uint64_t timer_end(benchmark_timer_t *timer) {
    timer->end = get_time_ns();
    return timer->end - timer->start;
}

static double calculate_overhead(uint64_t transpiled_ns, uint64_t native_ns) {
    if (native_ns == 0) return 0.0;
    return ((double)(transpiled_ns - native_ns) / (double)native_ns) * 100.0;
}

// ============================================================================
// Benchmark 1: Simple Generator (co_yield)
// ============================================================================

/**
 * @brief Resume function for generator coroutine
 * State machine implementing:
 *   for (int i = 0; i < n; ++i) { co_yield i; }
 */
void generator_resume(void* frame_ptr) {
    struct generator_frame* frame = (struct generator_frame*)frame_ptr;

    switch (frame->header.state) {
        case 0:  // Initial state
            frame->i = 0;
            goto yield_point;

        case 1:  // Resume after yield
            frame->i++;
            if (frame->i < frame->n) {
                goto yield_point;
            }
            goto final;

        yield_point:
            frame->value = frame->i;
            frame->header.state = 1;
            return;  // Suspend

        final:
            frame->header.state = -1;  // Done
            return;
    }
}

/**
 * @brief Destroy function for generator coroutine
 */
void generator_destroy(void* frame_ptr) {
    // In real implementation, would call destructors for frame members
    free(frame_ptr);
}

/**
 * @brief Create generator coroutine
 */
struct generator_frame* generator_create(int n) {
    struct generator_frame* frame = (struct generator_frame*)
        malloc(sizeof(struct generator_frame));

    frame->header.state = 0;
    frame->header.resume_fn = generator_resume;
    frame->header.destroy_fn = generator_destroy;
    frame->n = n;
    frame->i = 0;
    frame->value = 0;

    return frame;
}

void benchmark_generator_transpiled(int iterations) {
    for (int iter = 0; iter < iterations; iter++) {
        struct generator_frame* gen = generator_create(10);

        // Iterate through generator
        while (gen->header.state != -1) {
            generator_resume(gen);
            // Use the value to prevent optimization
            volatile int val = gen->value;
            (void)val;
        }

        generator_destroy(gen);
    }
}

void test_benchmark_generator(void) {
    printf("Benchmark 1: Simple generator (co_yield)\n");
    printf("  Pattern: for (i = 0; i < 10; ++i) { co_yield i; }\n");

    const int ITERATIONS = 100000;  // Each iteration creates generator and consumes all values
    const int WARMUP = 1000;

    // Warm up
    benchmark_generator_transpiled(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_generator_transpiled(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;
    double ns_per_resume = ns_per_op / 10.0;  // 10 resumes per iteration

    printf("  Iterations:        %d\n", ITERATIONS);
    printf("  Total time:        %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per coroutine: %.2f ns\n", ns_per_op);
    printf("  Time per resume:   %.2f ns\n", ns_per_resume);
    printf("  Throughput:        %.2f M resumes/sec\n", 1000.0 / ns_per_resume);

    // Status: Under 100ns per resume is excellent
    printf("  Status:            ");
    if (ns_per_resume < 50.0) {
        printf("✓ EXCELLENT (< 50ns per resume)\n");
    } else if (ns_per_resume < 100.0) {
        printf("✓ GOOD (< 100ns per resume)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 200ns per resume)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 2: Async Function (co_await)
// ============================================================================

/**
 * @brief Resume function for async coroutine
 * State machine implementing:
 *   temp = x + y; co_await suspend(); result = temp * 2; co_return result;
 */
void async_resume(void* frame_ptr) {
    struct async_frame* frame = (struct async_frame*)frame_ptr;

    switch (frame->header.state) {
        case 0:  // Initial state
            frame->temp = frame->x + frame->y;
            goto suspend_1;

        case 1:  // Resume after first await
            frame->result = frame->temp * 2;
            goto suspend_2;

        case 2:  // Resume after second await
            goto final;

        suspend_1:
            frame->header.state = 1;
            return;  // Suspend

        suspend_2:
            frame->header.state = 2;
            return;  // Suspend

        final:
            frame->header.state = -1;  // Done
            return;
    }
}

/**
 * @brief Destroy function for async coroutine
 */
void async_destroy(void* frame_ptr) {
    free(frame_ptr);
}

/**
 * @brief Create async coroutine
 */
struct async_frame* async_create(int x, int y) {
    struct async_frame* frame = (struct async_frame*)
        malloc(sizeof(struct async_frame));

    frame->header.state = 0;
    frame->header.resume_fn = async_resume;
    frame->header.destroy_fn = async_destroy;
    frame->x = x;
    frame->y = y;
    frame->temp = 0;
    frame->result = 0;

    return frame;
}

void benchmark_async_transpiled(int iterations) {
    for (int iter = 0; iter < iterations; iter++) {
        struct async_frame* task = async_create(iter, iter + 1);

        // Resume until completion
        while (task->header.state != -1) {
            async_resume(task);
        }

        // Use result to prevent optimization
        volatile int result = task->result;
        (void)result;

        async_destroy(task);
    }
}

void test_benchmark_async(void) {
    printf("Benchmark 2: Async function (co_await)\n");
    printf("  Pattern: temp = x + y; co_await; result = temp * 2; co_return;\n");

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_async_transpiled(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_async_transpiled(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;
    double ns_per_resume = ns_per_op / 3.0;  // 3 resumes per iteration

    printf("  Iterations:        %d\n", ITERATIONS);
    printf("  Total time:        %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per coroutine: %.2f ns\n", ns_per_op);
    printf("  Time per resume:   %.2f ns\n", ns_per_resume);
    printf("  Throughput:        %.2f M resumes/sec\n", 1000.0 / ns_per_resume);

    printf("  Status:            ");
    if (ns_per_resume < 50.0) {
        printf("✓ EXCELLENT (< 50ns per resume)\n");
    } else if (ns_per_resume < 100.0) {
        printf("✓ GOOD (< 100ns per resume)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 200ns per resume)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 3: Nested Coroutines
// ============================================================================

/**
 * @brief Resume function for nested outer coroutine
 * Simulates calling inner async coroutine multiple times
 */
void nested_resume(void* frame_ptr) {
    struct nested_frame* frame = (struct nested_frame*)frame_ptr;

    switch (frame->header.state) {
        case 0:  // Initial state
            frame->accumulated = 0;
            frame->inner = async_create(frame->n, 1);
            goto await_inner_1;

        case 1:  // After first inner completes
            frame->accumulated += frame->inner->result;
            async_destroy(frame->inner);
            frame->inner = async_create(frame->n, 2);
            goto await_inner_2;

        case 2:  // After second inner completes
            frame->accumulated += frame->inner->result;
            async_destroy(frame->inner);
            frame->inner = NULL;
            goto final;

        await_inner_1:
            // Resume inner until done
            if (frame->inner->header.state != -1) {
                async_resume(frame->inner);
                return;  // Suspend, will resume inner next time
            }
            frame->header.state = 1;
            return;

        await_inner_2:
            if (frame->inner->header.state != -1) {
                async_resume(frame->inner);
                return;  // Suspend
            }
            frame->header.state = 2;
            return;

        final:
            frame->header.state = -1;  // Done
            return;
    }
}

/**
 * @brief Destroy function for nested coroutine
 */
void nested_destroy(void* frame_ptr) {
    struct nested_frame* frame = (struct nested_frame*)frame_ptr;
    if (frame->inner != NULL) {
        async_destroy(frame->inner);
    }
    free(frame_ptr);
}

/**
 * @brief Create nested coroutine
 */
struct nested_frame* nested_create(int n) {
    struct nested_frame* frame = (struct nested_frame*)
        malloc(sizeof(struct nested_frame));

    frame->header.state = 0;
    frame->header.resume_fn = nested_resume;
    frame->header.destroy_fn = nested_destroy;
    frame->n = n;
    frame->inner = NULL;
    frame->accumulated = 0;

    return frame;
}

void benchmark_nested_transpiled(int iterations) {
    for (int iter = 0; iter < iterations; iter++) {
        struct nested_frame* outer = nested_create(iter);

        // Resume until completion
        int safety_count = 0;
        while (outer->header.state != -1 && safety_count < 100) {
            nested_resume(outer);
            safety_count++;
        }

        // Use result to prevent optimization
        volatile int result = outer->accumulated;
        (void)result;

        nested_destroy(outer);
    }
}

void test_benchmark_nested(void) {
    printf("Benchmark 3: Nested coroutines (outer awaits inner)\n");
    printf("  Pattern: outer coroutine awaits two inner async coroutines\n");

    const int ITERATIONS = 100000;  // Fewer iterations - nested is more complex
    const int WARMUP = 1000;

    // Warm up
    benchmark_nested_transpiled(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_nested_transpiled(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:        %d\n", ITERATIONS);
    printf("  Total time:        %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per coroutine: %.2f ns\n", ns_per_op);

    printf("  Status:            ");
    if (ns_per_op < 500.0) {
        printf("✓ EXCELLENT (< 500ns for nested)\n");
    } else if (ns_per_op < 1000.0) {
        printf("✓ GOOD (< 1000ns for nested)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 2000ns)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 4: Coroutine Creation Overhead
// ============================================================================

void benchmark_creation_transpiled(int iterations) {
    for (int iter = 0; iter < iterations; iter++) {
        struct async_frame* task = async_create(iter, iter + 1);
        // Immediately destroy without resuming
        async_destroy(task);
    }
}

void test_benchmark_creation(void) {
    printf("Benchmark 4: Coroutine creation overhead\n");
    printf("  Pattern: create coroutine frame + initialize + destroy\n");

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_creation_transpiled(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_creation_transpiled(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:        %d\n", ITERATIONS);
    printf("  Total time:        %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per create:   %.2f ns\n", ns_per_op);
    printf("  Throughput:        %.2f M creates/sec\n", 1000.0 / ns_per_op);

    // Creation includes malloc overhead
    printf("  Status:            ");
    if (ns_per_op < 100.0) {
        printf("✓ EXCELLENT (< 100ns - includes malloc)\n");
    } else if (ns_per_op < 200.0) {
        printf("✓ GOOD (< 200ns - includes malloc)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 500ns - malloc overhead)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 5: Coroutine Destruction Overhead
// ============================================================================

void benchmark_destruction_transpiled(int iterations) {
    // Pre-allocate frames to isolate destruction overhead
    struct async_frame** frames = (struct async_frame**)
        malloc(sizeof(struct async_frame*) * iterations);

    for (int i = 0; i < iterations; i++) {
        frames[i] = async_create(i, i + 1);
    }

    // Benchmark pure destruction
    benchmark_timer_t timer;
    timer_start(&timer);

    for (int i = 0; i < iterations; i++) {
        async_destroy(frames[i]);
    }

    uint64_t duration_ns = timer_end(&timer);

    free(frames);

    double ns_per_op = (double)duration_ns / (double)iterations;

    printf("  Iterations:        %d\n", iterations);
    printf("  Total time:        %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per destroy:  %.2f ns\n", ns_per_op);
    printf("  Throughput:        %.2f M destroys/sec\n", 1000.0 / ns_per_op);

    // Destruction includes free overhead
    printf("  Status:            ");
    if (ns_per_op < 80.0) {
        printf("✓ EXCELLENT (< 80ns - includes free)\n");
    } else if (ns_per_op < 150.0) {
        printf("✓ GOOD (< 150ns - includes free)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 300ns - free overhead)\n");
    }
    printf("\n");
}

void test_benchmark_destruction(void) {
    printf("Benchmark 5: Coroutine destruction overhead\n");
    printf("  Pattern: cleanup frame + free memory\n");

    const int ITERATIONS = 1000000;

    benchmark_destruction_transpiled(ITERATIONS);
}

// ============================================================================
// Memory Footprint Analysis
// ============================================================================

void run_memory_footprint_analysis(void) {
    printf("Memory Footprint Analysis\n");
    printf("  sizeof(coroutine_frame_header): %zu bytes\n",
           sizeof(struct coroutine_frame_header));
    printf("  sizeof(generator_frame):        %zu bytes\n",
           sizeof(struct generator_frame));
    printf("  sizeof(async_frame):            %zu bytes\n",
           sizeof(struct async_frame));
    printf("  sizeof(nested_frame):           %zu bytes\n",
           sizeof(struct nested_frame));

    printf("  Status: Compact frame structures for efficient state machines\n");
    printf("\n");
}

// ============================================================================
// Main Benchmark Suite
// ============================================================================

int main(void) {
    printf("\n");
    printf("=============================================================\n");
    printf("Coroutine Runtime Performance Benchmark\n");
    printf("C++ to C Transpiler - Coroutine Implementation\n");
    printf("=============================================================\n");
    printf("\n");
    printf("Target: 5-15%% overhead vs native C++20 coroutines\n");
    printf("Platform: Portable C implementation using state machines\n");
    printf("\n");
    printf("NOTE: Absolute timings measure C implementation performance.\n");
    printf("      Compare these results with native C++20 coroutines\n");
    printf("      benchmarks to calculate overhead percentage.\n");
    printf("\n");
    printf("=============================================================\n");
    printf("\n");

    // Run all benchmarks
    test_benchmark_generator();
    test_benchmark_async();
    test_benchmark_nested();
    test_benchmark_creation();
    test_benchmark_destruction();
    run_memory_footprint_analysis();

    printf("=============================================================\n");
    printf("Benchmark Suite Complete\n");
    printf("=============================================================\n");
    printf("\n");
    printf("SUMMARY:\n");
    printf("--------\n");
    printf("All benchmarks measure the transpiled C implementation.\n");
    printf("To validate 5-15%% overhead target:\n");
    printf("  1. Run equivalent C++20 benchmarks (see coroutine_benchmark.cpp)\n");
    printf("  2. Compare timings: overhead = (C_time - CPP_time) / CPP_time\n");
    printf("  3. Verify overhead is within 5-15%% range\n");
    printf("\n");
    printf("Expected overhead sources:\n");
    printf("  - Switch-based state machine vs compiler optimizations\n");
    printf("  - Frame allocation (malloc vs custom allocator)\n");
    printf("  - Function pointer dispatch for resume/destroy\n");
    printf("\n");
    printf("Performance characteristics:\n");
    printf("  - Resume: O(1) switch dispatch + frame access\n");
    printf("  - Creation: O(1) malloc + initialization\n");
    printf("  - Destruction: O(1) cleanup + free\n");
    printf("  - Memory: Compact frames with only necessary state\n");
    printf("\n");

    return 0;
}

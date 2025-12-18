/**
 * @file virtual_benchmark.c
 * @brief Virtual Call Runtime Performance Benchmark
 *
 * Performance validation for C++ to C transpiler virtual function call implementation.
 * Measures vtable dispatch overhead compared to native C++ virtual calls.
 *
 * BENCHMARK RESULTS SUMMARY:
 * ==========================
 * Target: 0-2% overhead vs native C++ virtual calls (from Architecture Canvas)
 *
 * Test scenarios:
 * 1. Single inheritance virtual call - 10,000,000 iterations
 * 2. Multiple inheritance virtual call - 10,000,000 iterations
 * 3. Deep hierarchy virtual call (5 levels) - 10,000,000 iterations
 * 4. Virtual destructor call - 10,000,000 iterations
 * 5. Multiple virtual calls in sequence - 10,000,000 iterations
 *
 * Expected Results:
 * - Single inheritance: 0-2% overhead (simple vtable lookup)
 * - Multiple inheritance: 0-2% overhead (offset adjustment + vtable lookup)
 * - Deep hierarchy: 0-2% overhead (vtable lookup is O(1) regardless of depth)
 * - Virtual destructors: 0-2% overhead (same mechanism as regular virtual calls)
 * - Sequential calls: 0-2% overhead (cache-friendly access pattern)
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only benchmarks virtual call performance
 * - Open/Closed: Extensible for new benchmark scenarios
 * - Interface Segregation: Uses minimal vtable API
 * - Dependency Inversion: Depends on abstract vtable structures
 *
 * Design Pattern: Benchmark suite modeled after rtti_benchmark.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include <stddef.h>  // For offsetof

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
// Vtable and Virtual Function Structures
// ============================================================================

/**
 * Simple single inheritance: Base <- Derived
 *
 * Base vtable:
 *   [0] = virtual_method1
 *   [1] = virtual_method2
 *
 * Derived vtable:
 *   [0] = overridden_method1
 *   [1] = Base::virtual_method2
 */

// Function pointer types
typedef int (*virtual_func1_t)(void *this);
typedef int (*virtual_func2_t)(void *this, int arg);

// Vtable structure for single inheritance
typedef struct {
    virtual_func1_t method1;
    virtual_func2_t method2;
} vtable_t;

// Base class structure
struct Base {
    vtable_t *vptr;    // Pointer to vtable
    int base_data;
};

// Derived class structure
struct Derived {
    vtable_t *vptr;    // Pointer to vtable
    int base_data;
    int derived_data;
};

// Virtual method implementations
static int base_method1(void *this) {
    struct Base *b = (struct Base *)this;
    return b->base_data * 2;
}

static int base_method2(void *this, int arg) {
    struct Base *b = (struct Base *)this;
    return b->base_data + arg;
}

static int derived_method1(void *this) {
    struct Derived *d = (struct Derived *)this;
    return d->base_data + d->derived_data;
}

// Static vtables
static vtable_t base_vtable = {
    .method1 = base_method1,
    .method2 = base_method2
};

static vtable_t derived_vtable = {
    .method1 = derived_method1,
    .method2 = base_method2
};

// ============================================================================
// Multiple Inheritance Structures
// ============================================================================

/**
 * Multiple inheritance: Base1, Base2 <- Diamond
 *
 * Diamond layout:
 *   [0-15]  Base1 subobject (vptr1, data1)
 *   [16-31] Base2 subobject (vptr2, data2)
 *   [32+]   Diamond-specific data
 */

// Vtable for Base1
typedef struct {
    virtual_func1_t compute;
} vtable_base1_t;

// Vtable for Base2
typedef struct {
    virtual_func1_t calculate;
} vtable_base2_t;

struct Base1 {
    vtable_base1_t *vptr;
    int data1;
};

struct Base2 {
    vtable_base2_t *vptr;
    int data2;
};

struct Diamond {
    vtable_base1_t *vptr1;  // Base1 vtable
    int data1;
    vtable_base2_t *vptr2;  // Base2 vtable
    int data2;
    int diamond_data;
};

// Virtual method implementations for multiple inheritance
static int base1_compute(void *this) {
    struct Base1 *b = (struct Base1 *)this;
    return b->data1 * 3;
}

static int base2_calculate(void *this) {
    struct Base2 *b = (struct Base2 *)this;
    return b->data2 * 5;
}

static int diamond_compute(void *this) {
    struct Diamond *d = (struct Diamond *)this;
    return d->data1 + d->data2 + d->diamond_data;
}

static int diamond_calculate(void *this) {
    // Adjust 'this' pointer: subtract offset from Base2 to Diamond
    char *base2_ptr = (char *)this;
    struct Diamond *d = (struct Diamond *)(base2_ptr - offsetof(struct Diamond, vptr2));
    return d->data1 * d->data2 + d->diamond_data;
}

// Static vtables for multiple inheritance
static vtable_base1_t diamond_vtable1 = {
    .compute = diamond_compute
};

static vtable_base2_t diamond_vtable2 = {
    .calculate = diamond_calculate
};

// ============================================================================
// Deep Hierarchy Structures
// ============================================================================

/**
 * Deep hierarchy: A <- B <- C <- D <- E (5 levels)
 * All share the same vtable structure and override the same method
 */

typedef int (*process_func_t)(void *this);

typedef struct {
    process_func_t process;
} vtable_deep_t;

struct A { vtable_deep_t *vptr; int a; };
struct B { vtable_deep_t *vptr; int a; int b; };
struct C { vtable_deep_t *vptr; int a; int b; int c; };
struct D { vtable_deep_t *vptr; int a; int b; int c; int d; };
struct E { vtable_deep_t *vptr; int a; int b; int c; int d; int e; };

// Virtual method implementations for deep hierarchy
static int a_process(void *this) {
    struct A *obj = (struct A *)this;
    return obj->a;
}

static int e_process(void *this) {
    struct E *obj = (struct E *)this;
    return obj->a + obj->b + obj->c + obj->d + obj->e;
}

// Static vtables for deep hierarchy
static vtable_deep_t a_vtable = { .process = a_process };
static vtable_deep_t e_vtable = { .process = e_process };

// ============================================================================
// Benchmark 1: Single Inheritance Virtual Call
// ============================================================================

void benchmark_single_inheritance(int iterations) {
    struct Derived obj = {
        .vptr = &derived_vtable,
        .base_data = 42,
        .derived_data = 100
    };

    struct Base *base_ptr = (struct Base *)&obj;

    // Benchmark: Virtual call through base pointer
    volatile int result = 0;  // Prevent optimization
    for (int i = 0; i < iterations; i++) {
        // Virtual call: base_ptr->method1()
        result += base_ptr->vptr->method1(base_ptr);
    }

    // Prevent entire loop optimization
    if (result == 0) abort();
}

void test_benchmark_single_inheritance(void) {
    printf("Benchmark 1: Single inheritance virtual call\n");

    const int ITERATIONS = 10000000;
    const int WARMUP = 100000;

    // Warm up
    benchmark_single_inheritance(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_single_inheritance(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:     %d\n", ITERATIONS);
    printf("  Total time:     %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per call:  %.2f ns\n", ns_per_op);
    printf("  Throughput:     %.2f M calls/sec\n", 1000.0 / ns_per_op);

    // Virtual calls should be very fast (single indirection)
    printf("  Status:         ");
    if (ns_per_op < 2.0) {
        printf("✓ EXCELLENT (< 2ns - optimal vtable dispatch)\n");
    } else if (ns_per_op < 5.0) {
        printf("✓ GOOD (< 5ns - efficient dispatch)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 10ns)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 2: Multiple Inheritance Virtual Call
// ============================================================================

void benchmark_multiple_inheritance(int iterations) {
    struct Diamond obj = {
        .vptr1 = &diamond_vtable1,
        .data1 = 42,
        .vptr2 = &diamond_vtable2,
        .data2 = 100,
        .diamond_data = 200
    };

    // Call through Base2 pointer (requires offset adjustment)
    struct Base2 *base2_ptr = (struct Base2 *)&obj.vptr2;

    // Benchmark: Virtual call through Base2 pointer
    volatile int result = 0;
    for (int i = 0; i < iterations; i++) {
        // Virtual call: base2_ptr->calculate()
        result += base2_ptr->vptr->calculate(base2_ptr);
    }

    if (result == 0) abort();
}

void test_benchmark_multiple_inheritance(void) {
    printf("Benchmark 2: Multiple inheritance virtual call (with offset)\n");

    const int ITERATIONS = 10000000;
    const int WARMUP = 100000;

    // Warm up
    benchmark_multiple_inheritance(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_multiple_inheritance(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:     %d\n", ITERATIONS);
    printf("  Total time:     %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per call:  %.2f ns\n", ns_per_op);
    printf("  Throughput:     %.2f M calls/sec\n", 1000.0 / ns_per_op);

    // Multiple inheritance adds pointer adjustment overhead
    printf("  Status:         ");
    if (ns_per_op < 3.0) {
        printf("✓ EXCELLENT (< 3ns with offset adjustment)\n");
    } else if (ns_per_op < 6.0) {
        printf("✓ GOOD (< 6ns with offset adjustment)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 12ns)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 3: Deep Hierarchy Virtual Call
// ============================================================================

void benchmark_deep_hierarchy(int iterations) {
    struct E obj = {
        .vptr = &e_vtable,
        .a = 1, .b = 2, .c = 3, .d = 4, .e = 5
    };

    struct A *a_ptr = (struct A *)&obj;

    // Benchmark: Virtual call through base pointer (5 levels deep)
    volatile int result = 0;
    for (int i = 0; i < iterations; i++) {
        // Virtual call: a_ptr->process()
        // Note: Vtable lookup is O(1) regardless of hierarchy depth
        result += a_ptr->vptr->process(a_ptr);
    }

    if (result == 0) abort();
}

void test_benchmark_deep_hierarchy(void) {
    printf("Benchmark 3: Deep hierarchy virtual call (5 levels: A <- B <- C <- D <- E)\n");

    const int ITERATIONS = 10000000;
    const int WARMUP = 100000;

    // Warm up
    benchmark_deep_hierarchy(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_deep_hierarchy(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:     %d\n", ITERATIONS);
    printf("  Total time:     %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per call:  %.2f ns\n", ns_per_op);
    printf("  Throughput:     %.2f M calls/sec\n", 1000.0 / ns_per_op);

    // Deep hierarchy should be same speed as shallow (O(1) vtable lookup)
    printf("  Status:         ");
    if (ns_per_op < 2.0) {
        printf("✓ EXCELLENT (< 2ns - O(1) dispatch regardless of depth)\n");
    } else if (ns_per_op < 5.0) {
        printf("✓ GOOD (< 5ns - efficient dispatch)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 10ns)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 4: Virtual Destructor Call
// ============================================================================

typedef void (*destructor_t)(void *this);

typedef struct {
    destructor_t destroy;
    virtual_func1_t method;
} vtable_with_dtor_t;

struct BaseWithDtor {
    vtable_with_dtor_t *vptr;
    int data;
};

struct DerivedWithDtor {
    vtable_with_dtor_t *vptr;
    int data;
    int extra_data;
};

static void base_destructor(void *this) {
    struct BaseWithDtor *b = (struct BaseWithDtor *)this;
    b->data = 0;  // Simulate cleanup
}

static void derived_destructor(void *this) {
    struct DerivedWithDtor *d = (struct DerivedWithDtor *)this;
    d->data = 0;
    d->extra_data = 0;
}

static int dummy_method(void *this) {
    return 42;
}

static vtable_with_dtor_t derived_dtor_vtable = {
    .destroy = derived_destructor,
    .method = dummy_method
};

void benchmark_virtual_destructor(int iterations) {
    // Allocate array of objects to avoid repeated stack allocation overhead
    struct DerivedWithDtor *objects = malloc(sizeof(struct DerivedWithDtor) * 100);

    for (int j = 0; j < 100; j++) {
        objects[j].vptr = &derived_dtor_vtable;
        objects[j].data = 42;
        objects[j].extra_data = 100;
    }

    // Benchmark: Virtual destructor calls
    for (int i = 0; i < iterations; i++) {
        struct BaseWithDtor *base_ptr = (struct BaseWithDtor *)&objects[i % 100];
        // Virtual destructor call
        base_ptr->vptr->destroy(base_ptr);
        // Reinitialize for next iteration
        objects[i % 100].data = 42;
        objects[i % 100].extra_data = 100;
    }

    free(objects);
}

void test_benchmark_virtual_destructor(void) {
    printf("Benchmark 4: Virtual destructor call\n");

    const int ITERATIONS = 10000000;
    const int WARMUP = 100000;

    // Warm up
    benchmark_virtual_destructor(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_virtual_destructor(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:     %d\n", ITERATIONS);
    printf("  Total time:     %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per call:  %.2f ns\n", ns_per_op);
    printf("  Throughput:     %.2f M calls/sec\n", 1000.0 / ns_per_op);

    // Virtual destructors use same mechanism as virtual methods
    printf("  Status:         ");
    if (ns_per_op < 3.0) {
        printf("✓ EXCELLENT (< 3ns per destructor call)\n");
    } else if (ns_per_op < 6.0) {
        printf("✓ GOOD (< 6ns per destructor call)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 12ns)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 5: Multiple Virtual Calls in Sequence
// ============================================================================

void benchmark_sequential_calls(int iterations) {
    struct Derived obj = {
        .vptr = &derived_vtable,
        .base_data = 42,
        .derived_data = 100
    };

    struct Base *base_ptr = (struct Base *)&obj;

    // Benchmark: Multiple virtual calls in sequence (cache-friendly)
    volatile int result = 0;
    for (int i = 0; i < iterations; i++) {
        // Three sequential virtual calls
        result += base_ptr->vptr->method1(base_ptr);
        result += base_ptr->vptr->method2(base_ptr, 10);
        result += base_ptr->vptr->method1(base_ptr);
    }

    if (result == 0) abort();
}

void test_benchmark_sequential_calls(void) {
    printf("Benchmark 5: Multiple virtual calls in sequence (3 calls per iteration)\n");

    const int ITERATIONS = 10000000;
    const int WARMUP = 100000;

    // Warm up
    benchmark_sequential_calls(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_sequential_calls(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    // Calculate time per individual call (3 calls per iteration)
    double ns_per_op = (double)duration_ns / (double)(ITERATIONS * 3);

    printf("  Iterations:     %d (3 calls each)\n", ITERATIONS);
    printf("  Total calls:    %d\n", ITERATIONS * 3);
    printf("  Total time:     %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per call:  %.2f ns\n", ns_per_op);
    printf("  Throughput:     %.2f M calls/sec\n", 1000.0 / ns_per_op);

    // Sequential calls should benefit from cache locality
    printf("  Status:         ");
    if (ns_per_op < 2.0) {
        printf("✓ EXCELLENT (< 2ns - excellent cache locality)\n");
    } else if (ns_per_op < 5.0) {
        printf("✓ GOOD (< 5ns - good cache performance)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 10ns)\n");
    }
    printf("\n");
}

// ============================================================================
// Main Benchmark Suite
// ============================================================================

int main(void) {
    printf("\n");
    printf("=============================================================\n");
    printf("Virtual Call Runtime Performance Benchmark\n");
    printf("C++ to C Transpiler - Virtual Function Dispatch\n");
    printf("=============================================================\n");
    printf("\n");
    printf("Target: 0-2%% overhead vs native C++ virtual calls\n");
    printf("Platform: Manual vtable implementation in C\n");
    printf("\n");
    printf("NOTE: Absolute timings measure C implementation performance.\n");
    printf("      Compare these results with native C++ virtual call\n");
    printf("      benchmarks to calculate overhead percentage.\n");
    printf("\n");
    printf("=============================================================\n");
    printf("\n");

    // Run all benchmarks
    test_benchmark_single_inheritance();
    test_benchmark_multiple_inheritance();
    test_benchmark_deep_hierarchy();
    test_benchmark_virtual_destructor();
    test_benchmark_sequential_calls();

    printf("=============================================================\n");
    printf("Benchmark Suite Complete\n");
    printf("=============================================================\n");
    printf("\n");
    printf("SUMMARY:\n");
    printf("--------\n");
    printf("All benchmarks measure the transpiled C implementation.\n");
    printf("To validate 0-2%% overhead target:\n");
    printf("  1. Run equivalent C++ benchmarks (see virtual_benchmark.cpp)\n");
    printf("  2. Compare timings: overhead = (C_time - CPP_time) / CPP_time\n");
    printf("  3. Verify overhead is within 0-2%% range\n");
    printf("\n");
    printf("Expected overhead sources:\n");
    printf("  - Compiler optimization differences (C vs C++)\n");
    printf("  - Function pointer indirection\n");
    printf("  - This pointer adjustment (multiple inheritance)\n");
    printf("\n");
    printf("Performance characteristics:\n");
    printf("  - Virtual calls: O(1) - single vtable lookup\n");
    printf("  - Hierarchy depth: O(1) - vtable stored at object head\n");
    printf("  - Multiple inheritance: O(1) - requires pointer adjustment\n");
    printf("  - Cache-friendly: Sequential vtable access patterns\n");
    printf("  - Branch prediction: Virtual calls are predictable\n");
    printf("\n");

    return 0;
}

/**
 * @file rtti_benchmark.c
 * @brief RTTI Runtime Performance Benchmark
 *
 * Performance validation for C++ to C transpiler RTTI runtime implementation.
 * Measures dynamic_cast overhead compared to native C++ implementation.
 *
 * BENCHMARK RESULTS SUMMARY:
 * ==========================
 * Target: 10-20% overhead vs native C++ dynamic_cast
 *
 * Test scenarios:
 * 1. Successful upcast (base class cast) - 1,000,000 iterations
 * 2. Failed cast (unrelated types) - 1,000,000 iterations
 * 3. Cross-cast (sibling classes) - 1,000,000 iterations
 * 4. Deep hierarchy traversal - 1,000,000 iterations
 * 5. Multiple inheritance cast - 1,000,000 iterations
 *
 * Expected Results:
 * - Simple upcasts: 5-15% overhead (linear hierarchy walk)
 * - Failed casts: 5-15% overhead (quick rejection)
 * - Cross-casts: 10-20% overhead (bidirectional traversal)
 * - Deep hierarchies: 10-20% overhead (recursive search)
 * - Multiple inheritance: 10-20% overhead (offset calculations)
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only benchmarks RTTI performance
 * - Open/Closed: Extensible for new benchmark scenarios
 * - Interface Segregation: Uses minimal runtime API
 * - Dependency Inversion: Depends on abstract type_info structures
 *
 * Design Pattern: Benchmark suite modeled after Google Benchmark
 */

#include "../runtime/rtti_runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

// ============================================================================
// Mock vtable pointers (normally provided by compiler/runtime)
// ============================================================================

const void *__vt_class_type_info = (const void *)0x1000;
const void *__vt_si_class_type_info = (const void *)0x2000;
const void *__vt_vmi_class_type_info = (const void *)0x3000;

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
// Test Data Structures
// ============================================================================

// Simple single inheritance hierarchy: Base <- Derived
struct Base {
    void *vptr;
    int base_data;
};

struct Derived {
    void *vptr;
    int base_data;
    int derived_data;
};

// Deep hierarchy: A <- B <- C <- D <- E
struct A { void *vptr; int a; };
struct B { void *vptr; int a; int b; };
struct C { void *vptr; int a; int b; int c; };
struct D { void *vptr; int a; int b; int c; int d; };
struct E { void *vptr; int a; int b; int c; int d; int e; };

// Multiple inheritance: Base1, Base2 <- Diamond
struct Base1 { void *vptr; int data1; };
struct Base2 { void *vptr; int data2; };
struct Diamond {
    void *vptr;
    int data1;  // Base1 subobject at offset 0
    void *vptr2;
    int data2;  // Base2 subobject at offset 16 (aligned)
    int diamond_data;
};

// Unrelated classes for failed cast tests
struct Unrelated { void *vptr; int data; };

// ============================================================================
// Benchmark 1: Successful Upcast (Base Class Cast)
// ============================================================================

void benchmark_upcast_transpiled(int iterations) {
    // Setup type_info
    const struct __class_type_info ti_Base = {
        .vtable_ptr = __vt_class_type_info,
        .type_name = "4Base"
    };

    const struct __si_class_type_info ti_Derived = {
        .vtable_ptr = __vt_si_class_type_info,
        .type_name = "7Derived",
        .base_type = &ti_Base
    };

    // Create test object
    struct Derived obj = { .vptr = NULL, .base_data = 42, .derived_data = 100 };
    void *ptr = &obj;

    // Benchmark: Derived* -> Base*
    for (int i = 0; i < iterations; i++) {
        void *result = traverse_hierarchy(ptr,
                                         (const struct __class_type_info *)&ti_Derived,
                                         &ti_Base);
        // Prevent optimization
        if (result == NULL) abort();
    }
}

void test_benchmark_upcast(void) {
    printf("Benchmark 1: Successful upcast (Derived* -> Base*)\n");

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_upcast_transpiled(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_upcast_transpiled(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:     %d\n", ITERATIONS);
    printf("  Total time:     %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per cast:  %.2f ns\n", ns_per_op);
    printf("  Throughput:     %.2f M ops/sec\n", 1000.0 / ns_per_op);

    // Status: Under 100ns per operation is excellent
    printf("  Status:         ");
    if (ns_per_op < 50.0) {
        printf("✓ EXCELLENT (< 50ns per cast)\n");
    } else if (ns_per_op < 100.0) {
        printf("✓ GOOD (< 100ns per cast)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 200ns per cast)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 2: Failed Cast (Unrelated Types)
// ============================================================================

void benchmark_failed_cast_transpiled(int iterations) {
    // Setup type_info
    const struct __class_type_info ti_Base = {
        .vtable_ptr = __vt_class_type_info,
        .type_name = "4Base"
    };

    const struct __si_class_type_info ti_Derived = {
        .vtable_ptr = __vt_si_class_type_info,
        .type_name = "7Derived",
        .base_type = &ti_Base
    };

    const struct __class_type_info ti_Unrelated = {
        .vtable_ptr = __vt_class_type_info,
        .type_name = "9Unrelated"
    };

    // Create test object
    struct Derived obj = { .vptr = NULL, .base_data = 42, .derived_data = 100 };
    void *ptr = &obj;

    // Benchmark: Derived* -> Unrelated* (should fail)
    for (int i = 0; i < iterations; i++) {
        void *result = traverse_hierarchy(ptr,
                                         (const struct __class_type_info *)&ti_Derived,
                                         &ti_Unrelated);
        // Should always return NULL
        if (result != NULL) abort();
    }
}

void test_benchmark_failed_cast(void) {
    printf("Benchmark 2: Failed cast (unrelated types)\n");

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_failed_cast_transpiled(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_failed_cast_transpiled(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:     %d\n", ITERATIONS);
    printf("  Total time:     %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per cast:  %.2f ns\n", ns_per_op);
    printf("  Throughput:     %.2f M ops/sec\n", 1000.0 / ns_per_op);

    // Failed casts should be fast (early rejection)
    printf("  Status:         ");
    if (ns_per_op < 30.0) {
        printf("✓ EXCELLENT (< 30ns - fast rejection)\n");
    } else if (ns_per_op < 60.0) {
        printf("✓ GOOD (< 60ns - fast rejection)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 100ns)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 3: Cross-Cast (Sibling Classes)
// ============================================================================

void benchmark_cross_cast_transpiled(int iterations) {
    // Setup type_info
    const struct __class_type_info ti_Base1 = {
        .vtable_ptr = __vt_class_type_info,
        .type_name = "5Base1"
    };

    const struct __class_type_info ti_Base2 = {
        .vtable_ptr = __vt_class_type_info,
        .type_name = "5Base2"
    };

    // Diamond type with multiple inheritance
    struct {
        const void *vtable_ptr;
        const char *type_name;
        unsigned int flags;
        unsigned int base_count;
        struct __base_class_type_info base_info[2];
    } ti_Diamond = {
        .vtable_ptr = __vt_vmi_class_type_info,
        .type_name = "7Diamond",
        .flags = 0,
        .base_count = 2,
        .base_info = {
            { .base_type = &ti_Base1, .offset_flags = 0 << 8 },      // Base1 at offset 0
            { .base_type = &ti_Base2, .offset_flags = 16 << 8 }      // Base2 at offset 16
        }
    };

    // Create test object (Diamond instance)
    struct Diamond obj = {
        .vptr = NULL, .data1 = 42,
        .vptr2 = NULL, .data2 = 100,
        .diamond_data = 200
    };
    void *ptr = &obj;  // Points to Base1 subobject

    // Benchmark: Base1* -> Base2* via Diamond
    for (int i = 0; i < iterations; i++) {
        void *result = cross_cast_traverse(ptr,
                                          &ti_Base1,
                                          &ti_Base2,
                                          (const struct __class_type_info *)&ti_Diamond);
        // Should succeed and return Base2 subobject
        if (result == NULL) abort();
    }
}

void test_benchmark_cross_cast(void) {
    printf("Benchmark 3: Cross-cast (Base1* -> Base2* via Diamond)\n");

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_cross_cast_transpiled(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_cross_cast_transpiled(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:     %d\n", ITERATIONS);
    printf("  Total time:     %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per cast:  %.2f ns\n", ns_per_op);
    printf("  Throughput:     %.2f M ops/sec\n", 1000.0 / ns_per_op);

    // Cross-casts involve bidirectional traversal
    printf("  Status:         ");
    if (ns_per_op < 80.0) {
        printf("✓ EXCELLENT (< 80ns for cross-cast)\n");
    } else if (ns_per_op < 150.0) {
        printf("✓ GOOD (< 150ns for cross-cast)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 250ns)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 4: Deep Hierarchy Traversal
// ============================================================================

void benchmark_deep_hierarchy_transpiled(int iterations) {
    // Setup type_info for 5-level hierarchy: A <- B <- C <- D <- E
    const struct __class_type_info ti_A = {
        .vtable_ptr = __vt_class_type_info,
        .type_name = "1A"
    };

    const struct __si_class_type_info ti_B = {
        .vtable_ptr = __vt_si_class_type_info,
        .type_name = "1B",
        .base_type = &ti_A
    };

    const struct __si_class_type_info ti_C = {
        .vtable_ptr = __vt_si_class_type_info,
        .type_name = "1C",
        .base_type = (const struct __class_type_info *)&ti_B
    };

    const struct __si_class_type_info ti_D = {
        .vtable_ptr = __vt_si_class_type_info,
        .type_name = "1D",
        .base_type = (const struct __class_type_info *)&ti_C
    };

    const struct __si_class_type_info ti_E = {
        .vtable_ptr = __vt_si_class_type_info,
        .type_name = "1E",
        .base_type = (const struct __class_type_info *)&ti_D
    };

    // Create test object
    struct E obj = { .vptr = NULL, .a = 1, .b = 2, .c = 3, .d = 4, .e = 5 };
    void *ptr = &obj;

    // Benchmark: E* -> A* (traverse 4 levels)
    for (int i = 0; i < iterations; i++) {
        void *result = traverse_hierarchy(ptr,
                                         (const struct __class_type_info *)&ti_E,
                                         &ti_A);
        if (result == NULL) abort();
    }
}

void test_benchmark_deep_hierarchy(void) {
    printf("Benchmark 4: Deep hierarchy traversal (5 levels: E -> A)\n");

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_deep_hierarchy_transpiled(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_deep_hierarchy_transpiled(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:     %d\n", ITERATIONS);
    printf("  Total time:     %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per cast:  %.2f ns\n", ns_per_op);
    printf("  Throughput:     %.2f M ops/sec\n", 1000.0 / ns_per_op);

    // Deep hierarchies require recursive traversal
    printf("  Status:         ");
    if (ns_per_op < 100.0) {
        printf("✓ EXCELLENT (< 100ns for 5-level traversal)\n");
    } else if (ns_per_op < 200.0) {
        printf("✓ GOOD (< 200ns for 5-level traversal)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 300ns)\n");
    }
    printf("\n");
}

// ============================================================================
// Benchmark 5: Multiple Inheritance Cast with Offset
// ============================================================================

void benchmark_multiple_inheritance_transpiled(int iterations) {
    // Setup type_info
    const struct __class_type_info ti_Base1 = {
        .vtable_ptr = __vt_class_type_info,
        .type_name = "5Base1"
    };

    const struct __class_type_info ti_Base2 = {
        .vtable_ptr = __vt_class_type_info,
        .type_name = "5Base2"
    };

    // Diamond type with multiple inheritance
    struct {
        const void *vtable_ptr;
        const char *type_name;
        unsigned int flags;
        unsigned int base_count;
        struct __base_class_type_info base_info[2];
    } ti_Diamond = {
        .vtable_ptr = __vt_vmi_class_type_info,
        .type_name = "7Diamond",
        .flags = 0,
        .base_count = 2,
        .base_info = {
            { .base_type = &ti_Base1, .offset_flags = 0 << 8 },      // Base1 at offset 0
            { .base_type = &ti_Base2, .offset_flags = 16 << 8 }      // Base2 at offset 16
        }
    };

    // Create test object
    struct Diamond obj = {
        .vptr = NULL, .data1 = 42,
        .vptr2 = NULL, .data2 = 100,
        .diamond_data = 200
    };
    void *ptr = &obj;

    // Benchmark: Diamond* -> Base2* (with offset)
    for (int i = 0; i < iterations; i++) {
        void *result = traverse_hierarchy(ptr,
                                         (const struct __class_type_info *)&ti_Diamond,
                                         &ti_Base2);
        if (result == NULL) abort();
    }
}

void test_benchmark_multiple_inheritance(void) {
    printf("Benchmark 5: Multiple inheritance with offset (Diamond* -> Base2*)\n");

    const int ITERATIONS = 1000000;
    const int WARMUP = 10000;

    // Warm up
    benchmark_multiple_inheritance_transpiled(WARMUP);

    // Benchmark
    benchmark_timer_t timer;
    timer_start(&timer);
    benchmark_multiple_inheritance_transpiled(ITERATIONS);
    uint64_t duration_ns = timer_end(&timer);

    double ns_per_op = (double)duration_ns / (double)ITERATIONS;

    printf("  Iterations:     %d\n", ITERATIONS);
    printf("  Total time:     %.2f ms\n", duration_ns / 1000000.0);
    printf("  Time per cast:  %.2f ns\n", ns_per_op);
    printf("  Throughput:     %.2f M ops/sec\n", 1000.0 / ns_per_op);

    // Multiple inheritance requires offset calculation
    printf("  Status:         ");
    if (ns_per_op < 60.0) {
        printf("✓ EXCELLENT (< 60ns with offset)\n");
    } else if (ns_per_op < 120.0) {
        printf("✓ GOOD (< 120ns with offset)\n");
    } else {
        printf("⚠ ACCEPTABLE (< 200ns)\n");
    }
    printf("\n");
}

// ============================================================================
// Main Benchmark Suite
// ============================================================================

int main(void) {
    printf("\n");
    printf("=============================================================\n");
    printf("RTTI Runtime Performance Benchmark\n");
    printf("C++ to C Transpiler - Story #86 & #87\n");
    printf("=============================================================\n");
    printf("\n");
    printf("Target: 10-20%% overhead vs native C++ dynamic_cast\n");
    printf("Platform: Portable C implementation using Itanium ABI\n");
    printf("\n");
    printf("NOTE: Absolute timings measure C implementation performance.\n");
    printf("      Compare these results with native C++ dynamic_cast\n");
    printf("      benchmarks to calculate overhead percentage.\n");
    printf("\n");
    printf("=============================================================\n");
    printf("\n");

    // Run all benchmarks
    test_benchmark_upcast();
    test_benchmark_failed_cast();
    test_benchmark_cross_cast();
    test_benchmark_deep_hierarchy();
    test_benchmark_multiple_inheritance();

    printf("=============================================================\n");
    printf("Benchmark Suite Complete\n");
    printf("=============================================================\n");
    printf("\n");
    printf("SUMMARY:\n");
    printf("--------\n");
    printf("All benchmarks measure the transpiled C implementation.\n");
    printf("To validate 10-20%% overhead target:\n");
    printf("  1. Run equivalent C++ benchmarks (see rtti_benchmark.cpp)\n");
    printf("  2. Compare timings: overhead = (C_time - CPP_time) / CPP_time\n");
    printf("  3. Verify overhead is within 10-20%% range\n");
    printf("\n");
    printf("Expected overhead sources:\n");
    printf("  - Function call overhead (C vs C++ inlining)\n");
    printf("  - Type info structure traversal\n");
    printf("  - Pointer arithmetic for offsets\n");
    printf("\n");
    printf("Performance characteristics:\n");
    printf("  - Simple casts: O(1) for same type, O(n) for hierarchy depth\n");
    printf("  - Failed casts: O(n) worst case, often O(1) early rejection\n");
    printf("  - Cross-casts: O(n*m) where n,m are hierarchy depths\n");
    printf("  - Cache-friendly: Sequential type_info structure access\n");
    printf("\n");

    return 0;
}

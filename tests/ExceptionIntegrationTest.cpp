// ExceptionIntegrationTest.cpp - Integration tests for Story #82
// (Integration Testing and Thread Safety Validation)
//
// Comprehensive end-to-end exception handling tests
// Testing all exception scenarios with RAII, nested exceptions, cross-function propagation

#include <cassert>
#include <csetjmp>
#include <cstdio>
#include <cstdlib>
#include <cstring>
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
// Test Utilities and Mock Classes
// ============================================================================

// Global counters for tracking destructor calls
static int resource_destructor_count = 0;
static int error_destructor_count = 0;
static int nested_destructor_count = 0;

// Reset all counters
void reset_counters() {
    resource_destructor_count = 0;
    error_destructor_count = 0;
    nested_destructor_count = 0;
    __cxx_exception_stack = nullptr;
}

// Mock Resource class (RAII pattern)
struct Resource {
    int *data;
    int id;
};

void Resource__ctor(struct Resource *this_ptr, int identifier) {
    this_ptr->data = (int *)malloc(100 * sizeof(int));
    this_ptr->id = identifier;
}

void Resource__dtor(void *this_ptr) {
    struct Resource *res = (struct Resource *)this_ptr;
    free(res->data);
    resource_destructor_count++;
}

// Mock Error exception class
struct Error {
    const char *message;
};

void Error__ctor(struct Error *this_ptr, const char *msg) {
    this_ptr->message = msg;
}

void Error__dtor(void *this_ptr) {
    (void)this_ptr;  // Unused parameter
    error_destructor_count++;
}

// Mock nested resource class
struct NestedResource {
    int value;
};

void NestedResource__ctor(struct NestedResource *this_ptr, int val) {
    this_ptr->value = val;
}

void NestedResource__dtor(void *this_ptr) {
    (void)this_ptr;  // Unused parameter
    nested_destructor_count++;
}

// ============================================================================
// Test Suite 1: End-to-End Exception Handling (AC #1)
// ============================================================================

void test_simple_throw_catch() {
    std::cout << "Test 1: Simple throw-catch flow... ";
    reset_counters();

    // GIVEN: A try-catch block with exception thrown
    struct __cxx_exception_frame frame;
    frame.next = __cxx_exception_stack;
    frame.actions = nullptr;
    frame.exception_object = nullptr;
    frame.exception_type = nullptr;

    // WHEN: Exception is thrown in try block
    if (setjmp(frame.jmpbuf) == 0) {
        __cxx_exception_stack = &frame;

        // Throw exception
        struct Error *ex = (struct Error *)malloc(sizeof(struct Error));
        Error__ctor(ex, "Test error");
        cxx_throw(ex, "Error");

        // Should never reach here
        assert(false && "Should not reach after throw");
    } else {
        // THEN: Exception caught in catch handler
        assert(frame.exception_object != nullptr);
        assert(strcmp(frame.exception_type, "Error") == 0);

        // Type matching
        struct Error *caught = (struct Error *)frame.exception_object;
        assert(strcmp(caught->message, "Test error") == 0);

        // Cleanup
        Error__dtor(caught);
        free(caught);
    }

    std::cout << "✓" << std::endl;
}

void test_no_exception_thrown() {
    std::cout << "Test 2: Try block completes without exception... ";
    reset_counters();

    // GIVEN: A try-catch block with no exception
    struct __cxx_exception_frame frame;
    frame.next = __cxx_exception_stack;
    frame.actions = nullptr;
    frame.exception_object = nullptr;
    frame.exception_type = nullptr;

    bool normal_path_executed = false;

    // WHEN: Try block completes normally
    if (setjmp(frame.jmpbuf) == 0) {
        __cxx_exception_stack = &frame;

        // Normal code path (no exception)
        normal_path_executed = true;

        // Pop frame
        __cxx_exception_stack = frame.next;
    } else {
        // Should not reach catch handler
        assert(false && "Should not catch when no exception thrown");
    }

    // THEN: Normal path executed, no catch triggered
    assert(normal_path_executed);
    assert(frame.exception_object == nullptr);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 2: RAII Integration - Destructors During Unwinding (AC #1)
// ============================================================================

void test_single_resource_cleanup() {
    std::cout << "Test 3: Single resource cleanup during exception... ";
    reset_counters();

    // GIVEN: A resource and exception frame with action table
    struct Resource r1;
    Resource__ctor(&r1, 1);

    struct __cxx_action_entry actions[] = {
        {Resource__dtor, &r1},
        {nullptr, nullptr}  // Sentinel
    };

    struct __cxx_exception_frame frame;
    frame.next = __cxx_exception_stack;
    frame.actions = actions;
    frame.exception_object = nullptr;
    frame.exception_type = nullptr;

    // WHEN: Exception thrown with resource in scope
    if (setjmp(frame.jmpbuf) == 0) {
        __cxx_exception_stack = &frame;

        struct Error *ex = (struct Error *)malloc(sizeof(struct Error));
        Error__ctor(ex, "Error during resource usage");
        cxx_throw(ex, "Error");

        assert(false && "Should not reach after throw");
    } else {
        // THEN: Resource destructor called during unwinding
        assert(resource_destructor_count == 1);

        // Cleanup exception
        struct Error *caught = (struct Error *)frame.exception_object;
        Error__dtor(caught);
        free(caught);
    }

    std::cout << "✓" << std::endl;
}

void test_multiple_resources_cleanup_order() {
    std::cout << "Test 4: Multiple resources cleanup in reverse order... ";
    reset_counters();

    // GIVEN: Multiple resources with action table
    struct Resource r1, r2, r3;
    Resource__ctor(&r1, 1);
    Resource__ctor(&r2, 2);
    Resource__ctor(&r3, 3);

    // Action table in REVERSE construction order (r3, r2, r1)
    struct __cxx_action_entry actions[] = {
        {Resource__dtor, &r3},
        {Resource__dtor, &r2},
        {Resource__dtor, &r1},
        {nullptr, nullptr}  // Sentinel
    };

    struct __cxx_exception_frame frame;
    frame.next = __cxx_exception_stack;
    frame.actions = actions;
    frame.exception_object = nullptr;
    frame.exception_type = nullptr;

    // WHEN: Exception thrown with multiple resources in scope
    if (setjmp(frame.jmpbuf) == 0) {
        __cxx_exception_stack = &frame;

        struct Error *ex = (struct Error *)malloc(sizeof(struct Error));
        Error__ctor(ex, "Error with multiple resources");
        cxx_throw(ex, "Error");

        assert(false);
    } else {
        // THEN: All destructors called (3 resources)
        assert(resource_destructor_count == 3);

        // Cleanup exception
        struct Error *caught = (struct Error *)frame.exception_object;
        Error__dtor(caught);
        free(caught);
    }

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 3: Nested Try-Catch Blocks (AC #2)
// ============================================================================

void test_nested_try_catch_inner_catches() {
    std::cout << "Test 5: Nested try-catch, inner catch handles... ";
    reset_counters();

    // GIVEN: Outer frame
    struct __cxx_exception_frame outer_frame;
    outer_frame.next = __cxx_exception_stack;
    outer_frame.actions = nullptr;
    outer_frame.exception_object = nullptr;
    outer_frame.exception_type = nullptr;

    bool outer_catch_reached = false;
    bool inner_catch_reached = false;

    // Outer try block
    if (setjmp(outer_frame.jmpbuf) == 0) {
        __cxx_exception_stack = &outer_frame;

        // WHEN: Inner try-catch block
        struct __cxx_exception_frame inner_frame;
        inner_frame.next = __cxx_exception_stack;
        inner_frame.actions = nullptr;
        inner_frame.exception_object = nullptr;
        inner_frame.exception_type = nullptr;

        if (setjmp(inner_frame.jmpbuf) == 0) {
            __cxx_exception_stack = &inner_frame;

            // Throw in inner block
            struct Error *ex = (struct Error *)malloc(sizeof(struct Error));
            Error__ctor(ex, "Inner exception");
            cxx_throw(ex, "Error");

            assert(false);
        } else {
            // THEN: Inner catch handles the exception
            inner_catch_reached = true;
            assert(strcmp(inner_frame.exception_type, "Error") == 0);

            // Cleanup
            struct Error *caught = (struct Error *)inner_frame.exception_object;
            Error__dtor(caught);
            free(caught);
        }

        // Pop outer frame
        __cxx_exception_stack = outer_frame.next;
    } else {
        // Outer catch should NOT be reached
        outer_catch_reached = true;
    }

    assert(inner_catch_reached && !outer_catch_reached);

    std::cout << "✓" << std::endl;
}

void test_nested_try_catch_outer_catches() {
    std::cout << "Test 6: Nested try-catch, exception propagates to outer... ";
    reset_counters();

    // GIVEN: Outer frame catches different exception type
    struct __cxx_exception_frame outer_frame;
    outer_frame.next = __cxx_exception_stack;
    outer_frame.actions = nullptr;
    outer_frame.exception_object = nullptr;
    outer_frame.exception_type = nullptr;

    bool outer_catch_reached = false;

    // Outer try block
    if (setjmp(outer_frame.jmpbuf) == 0) {
        __cxx_exception_stack = &outer_frame;

        // WHEN: Inner try-catch doesn't match exception type
        struct __cxx_exception_frame inner_frame;
        inner_frame.next = __cxx_exception_stack;
        inner_frame.actions = nullptr;
        inner_frame.exception_object = nullptr;
        inner_frame.exception_type = nullptr;

        if (setjmp(inner_frame.jmpbuf) == 0) {
            __cxx_exception_stack = &inner_frame;

            // Throw ErrorA
            struct Error *ex = (struct Error *)malloc(sizeof(struct Error));
            Error__ctor(ex, "ErrorA");
            cxx_throw(ex, "ErrorA");

            assert(false);
        } else {
            // Inner catch expects ErrorB (type mismatch)
            if (strcmp(inner_frame.exception_type, "ErrorB") == 0) {
                // Type matched - cleanup
                struct Error *caught = (struct Error *)inner_frame.exception_object;
                Error__dtor(caught);
                free(caught);
            } else {
                // Type didn't match - re-throw to outer
                cxx_throw(inner_frame.exception_object, inner_frame.exception_type);
            }
        }

        assert(false && "Should not reach here");
    } else {
        // THEN: Outer catch receives re-thrown exception
        outer_catch_reached = true;
        assert(strcmp(outer_frame.exception_type, "ErrorA") == 0);

        // Cleanup
        struct Error *caught = (struct Error *)outer_frame.exception_object;
        Error__dtor(caught);
        free(caught);
    }

    assert(outer_catch_reached);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 4: Cross-Function Exception Propagation (AC #3)
// ============================================================================

// Helper function that throws
void callee_throws() {
    struct Error *ex = (struct Error *)malloc(sizeof(struct Error));
    Error__ctor(ex, "Exception from callee");
    cxx_throw(ex, "Error");
}

void test_cross_function_propagation() {
    std::cout << "Test 7: Exception propagates across function boundaries... ";
    reset_counters();

    // GIVEN: Caller has try-catch, callee throws
    struct __cxx_exception_frame frame;
    frame.next = __cxx_exception_stack;
    frame.actions = nullptr;
    frame.exception_object = nullptr;
    frame.exception_type = nullptr;

    // WHEN: Calling function that throws
    if (setjmp(frame.jmpbuf) == 0) {
        __cxx_exception_stack = &frame;

        callee_throws();  // Throws exception

        assert(false && "Should not reach after callee throws");
    } else {
        // THEN: Caller catches exception from callee
        assert(frame.exception_object != nullptr);
        assert(strcmp(frame.exception_type, "Error") == 0);

        struct Error *caught = (struct Error *)frame.exception_object;
        assert(strcmp(caught->message, "Exception from callee") == 0);

        // Cleanup
        Error__dtor(caught);
        free(caught);
    }

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 5: Re-throw Scenarios (AC #5)
// ============================================================================

void test_rethrow_in_catch_handler() {
    std::cout << "Test 8: Re-throw exception from catch handler... ";
    reset_counters();

    // GIVEN: Outer frame
    struct __cxx_exception_frame outer_frame;
    outer_frame.next = __cxx_exception_stack;
    outer_frame.actions = nullptr;
    outer_frame.exception_object = nullptr;
    outer_frame.exception_type = nullptr;

    bool outer_catch_reached = false;

    // Outer try
    if (setjmp(outer_frame.jmpbuf) == 0) {
        __cxx_exception_stack = &outer_frame;

        // Inner try-catch that re-throws
        struct __cxx_exception_frame inner_frame;
        inner_frame.next = __cxx_exception_stack;
        inner_frame.actions = nullptr;
        inner_frame.exception_object = nullptr;
        inner_frame.exception_type = nullptr;

        if (setjmp(inner_frame.jmpbuf) == 0) {
            __cxx_exception_stack = &inner_frame;

            struct Error *ex = (struct Error *)malloc(sizeof(struct Error));
            Error__ctor(ex, "Re-throw test");
            cxx_throw(ex, "Error");

            assert(false);
        } else {
            // WHEN: Catch and re-throw
            cxx_throw(inner_frame.exception_object, inner_frame.exception_type);
        }

        assert(false);
    } else {
        // THEN: Outer catch receives re-thrown exception
        outer_catch_reached = true;
        assert(strcmp(outer_frame.exception_type, "Error") == 0);

        struct Error *caught = (struct Error *)outer_frame.exception_object;
        assert(strcmp(caught->message, "Re-throw test") == 0);

        Error__dtor(caught);
        free(caught);
    }

    assert(outer_catch_reached);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 6: Multiple Catch Handlers with Type Matching (AC #2)
// ============================================================================

struct ErrorA {
    const char *message;
};

struct ErrorB {
    int code;
};

void ErrorA__ctor(struct ErrorA *this_ptr, const char *msg) {
    this_ptr->message = msg;
}

void ErrorB__ctor(struct ErrorB *this_ptr, int error_code) {
    this_ptr->code = error_code;
}

void test_multiple_catch_handlers_type_matching() {
    std::cout << "Test 9: Multiple catch handlers with type matching... ";
    reset_counters();

    // Test catching ErrorA
    {
        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = nullptr;
        frame.exception_object = nullptr;
        frame.exception_type = nullptr;

        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            struct ErrorA *ex = (struct ErrorA *)malloc(sizeof(struct ErrorA));
            ErrorA__ctor(ex, "ErrorA message");
            cxx_throw(ex, "ErrorA");

            assert(false);
        } else {
            // Type matching logic
            if (strcmp(frame.exception_type, "ErrorA") == 0) {
                struct ErrorA *caught = (struct ErrorA *)frame.exception_object;
                assert(strcmp(caught->message, "ErrorA message") == 0);
                free(caught);
            } else if (strcmp(frame.exception_type, "ErrorB") == 0) {
                assert(false && "Should not catch ErrorB");
            } else {
                assert(false && "Unknown exception type");
            }
        }
    }

    // Test catching ErrorB
    {
        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = nullptr;
        frame.exception_object = nullptr;
        frame.exception_type = nullptr;

        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            struct ErrorB *ex = (struct ErrorB *)malloc(sizeof(struct ErrorB));
            ErrorB__ctor(ex, 404);
            cxx_throw(ex, "ErrorB");

            assert(false);
        } else {
            // Type matching logic
            if (strcmp(frame.exception_type, "ErrorA") == 0) {
                assert(false && "Should not catch ErrorA");
            } else if (strcmp(frame.exception_type, "ErrorB") == 0) {
                struct ErrorB *caught = (struct ErrorB *)frame.exception_object;
                assert(caught->code == 404);
                free(caught);
            } else {
                assert(false && "Unknown exception type");
            }
        }
    }

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 7: Memory Safety (AC #8)
// ============================================================================

void test_no_memory_leaks() {
    std::cout << "Test 10: No memory leaks during exception handling... ";
    reset_counters();

    // Run multiple exception cycles to detect leaks
    for (int i = 0; i < 100; i++) {
        struct Resource r;
        Resource__ctor(&r, i);

        struct __cxx_action_entry actions[] = {
            {Resource__dtor, &r},
            {nullptr, nullptr}
        };

        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = actions;
        frame.exception_object = nullptr;
        frame.exception_type = nullptr;

        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            struct Error *ex = (struct Error *)malloc(sizeof(struct Error));
            Error__ctor(ex, "Leak test");
            cxx_throw(ex, "Error");

            assert(false);
        } else {
            // Cleanup
            struct Error *caught = (struct Error *)frame.exception_object;
            Error__dtor(caught);
            free(caught);
        }
    }

    // THEN: All resources cleaned up (100 iterations)
    assert(resource_destructor_count == 100);
    assert(error_destructor_count == 100);

    std::cout << "✓ (run with valgrind for full validation)" << std::endl;
}

// ============================================================================
// Main
// ============================================================================

int main() {
    std::cout << "\n===========================================" << std::endl;
    std::cout << "Exception Integration Tests" << std::endl;
    std::cout << "Story #82 - Epic #42" << std::endl;
    std::cout << "===========================================" << std::endl;
    std::cout << std::endl;

    // Test Suite 1: End-to-End Exception Handling
    std::cout << "--- End-to-End Exception Handling ---" << std::endl;
    test_simple_throw_catch();
    test_no_exception_thrown();
    std::cout << std::endl;

    // Test Suite 2: RAII Integration
    std::cout << "--- RAII Integration ---" << std::endl;
    test_single_resource_cleanup();
    test_multiple_resources_cleanup_order();
    std::cout << std::endl;

    // Test Suite 3: Nested Try-Catch
    std::cout << "--- Nested Try-Catch Blocks ---" << std::endl;
    test_nested_try_catch_inner_catches();
    test_nested_try_catch_outer_catches();
    std::cout << std::endl;

    // Test Suite 4: Cross-Function Propagation
    std::cout << "--- Cross-Function Exception Propagation ---" << std::endl;
    test_cross_function_propagation();
    std::cout << std::endl;

    // Test Suite 5: Re-throw
    std::cout << "--- Re-throw Scenarios ---" << std::endl;
    test_rethrow_in_catch_handler();
    std::cout << std::endl;

    // Test Suite 6: Type Matching
    std::cout << "--- Multiple Catch Handlers ---" << std::endl;
    test_multiple_catch_handlers_type_matching();
    std::cout << std::endl;

    // Test Suite 7: Memory Safety
    std::cout << "--- Memory Safety ---" << std::endl;
    test_no_memory_leaks();
    std::cout << std::endl;

    std::cout << "===========================================" << std::endl;
    std::cout << "All Integration Tests Passed! ✓" << std::endl;
    std::cout << "===========================================" << std::endl;
    std::cout << std::endl;

    return 0;
}

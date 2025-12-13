// ExceptionThreadSafetyTest.cpp - Thread safety tests for Story #82
// (Integration Testing and Thread Safety Validation)
//
// Multi-threaded exception handling validation
// Testing that thread-local exception stacks work correctly

#include <cassert>
#include <csetjmp>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <pthread.h>
#include <string>
#include <atomic>
#include <chrono>
#include <thread>

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

// Atomic counters for thread-safe tracking
static std::atomic<int> total_exceptions_thrown{0};
static std::atomic<int> total_exceptions_caught{0};
static std::atomic<int> total_destructors_called{0};

void reset_atomic_counters() {
    total_exceptions_thrown = 0;
    total_exceptions_caught = 0;
    total_destructors_called = 0;
}

// Mock exception class
struct ThreadException {
    int thread_id;
    const char *message;
};

void ThreadException__ctor(struct ThreadException *this_ptr, int tid, const char *msg) {
    this_ptr->thread_id = tid;
    this_ptr->message = msg;
}

void ThreadException__dtor(void *this_ptr) {
    (void)this_ptr;  // Unused parameter
    total_destructors_called++;
}

// Mock resource class
struct ThreadResource {
    int thread_id;
    int *data;
};

void ThreadResource__ctor(struct ThreadResource *this_ptr, int tid) {
    this_ptr->thread_id = tid;
    this_ptr->data = (int *)malloc(100 * sizeof(int));
}

void ThreadResource__dtor(void *this_ptr) {
    struct ThreadResource *res = (struct ThreadResource *)this_ptr;
    free(res->data);
    total_destructors_called++;
}

// ============================================================================
// Test Suite 1: Basic Thread Safety (AC #4)
// ============================================================================

void *thread_simple_exception(void *arg) {
    int thread_id = *(int *)arg;

    // Each thread has its own exception stack
    assert(__cxx_exception_stack == nullptr);

    struct __cxx_exception_frame frame;
    frame.next = __cxx_exception_stack;
    frame.actions = nullptr;
    frame.exception_object = nullptr;
    frame.exception_type = nullptr;

    if (setjmp(frame.jmpbuf) == 0) {
        __cxx_exception_stack = &frame;

        // Throw exception
        struct ThreadException *ex = (struct ThreadException *)malloc(sizeof(struct ThreadException));
        ThreadException__ctor(ex, thread_id, "Thread exception");
        total_exceptions_thrown++;
        cxx_throw(ex, "ThreadException");

        assert(false);
    } else {
        // Catch exception
        assert(frame.exception_object != nullptr);
        assert(strcmp(frame.exception_type, "ThreadException") == 0);

        struct ThreadException *caught = (struct ThreadException *)frame.exception_object;
        assert(caught->thread_id == thread_id);

        total_exceptions_caught++;

        ThreadException__dtor(caught);
        free(caught);
    }

    // Exception stack should be clean after catch
    assert(__cxx_exception_stack == nullptr);

    return nullptr;
}

void test_multiple_threads_independent_exceptions() {
    std::cout << "Test 1: Multiple threads with independent exceptions... ";
    reset_atomic_counters();

    const int NUM_THREADS = 10;
    pthread_t threads[NUM_THREADS];
    int thread_ids[NUM_THREADS];

    // Create threads
    for (int i = 0; i < NUM_THREADS; i++) {
        thread_ids[i] = i;
        int rc = pthread_create(&threads[i], nullptr, thread_simple_exception, &thread_ids[i]);
        assert(rc == 0);
    }

    // Wait for all threads
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], nullptr);
    }

    // THEN: All exceptions thrown and caught independently
    assert(total_exceptions_thrown == NUM_THREADS);
    assert(total_exceptions_caught == NUM_THREADS);
    assert(total_destructors_called == NUM_THREADS);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 2: Thread-Local Stack Isolation (AC #4)
// ============================================================================

void *thread_with_resource_cleanup(void *arg) {
    int thread_id = *(int *)arg;

    // Resource with destructor
    struct ThreadResource res;
    ThreadResource__ctor(&res, thread_id);

    struct __cxx_action_entry actions[] = {
        {ThreadResource__dtor, &res},
        {nullptr, nullptr}
    };

    struct __cxx_exception_frame frame;
    frame.next = __cxx_exception_stack;
    frame.actions = actions;
    frame.exception_object = nullptr;
    frame.exception_type = nullptr;

    if (setjmp(frame.jmpbuf) == 0) {
        __cxx_exception_stack = &frame;

        // Throw exception
        struct ThreadException *ex = (struct ThreadException *)malloc(sizeof(struct ThreadException));
        ThreadException__ctor(ex, thread_id, "Resource cleanup test");
        total_exceptions_thrown++;
        cxx_throw(ex, "ThreadException");

        assert(false);
    } else {
        // Catch exception
        total_exceptions_caught++;

        struct ThreadException *caught = (struct ThreadException *)frame.exception_object;
        ThreadException__dtor(caught);
        free(caught);
    }

    return nullptr;
}

void test_thread_local_stack_isolation() {
    std::cout << "Test 2: Thread-local stack isolation with RAII... ";
    reset_atomic_counters();

    const int NUM_THREADS = 8;
    pthread_t threads[NUM_THREADS];
    int thread_ids[NUM_THREADS];

    // Create threads
    for (int i = 0; i < NUM_THREADS; i++) {
        thread_ids[i] = i;
        int rc = pthread_create(&threads[i], nullptr, thread_with_resource_cleanup, &thread_ids[i]);
        assert(rc == 0);
    }

    // Wait for all threads
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], nullptr);
    }

    // THEN: All resources cleaned up independently
    // Each thread: 1 resource destructor + 1 exception destructor = 2
    assert(total_destructors_called == NUM_THREADS * 2);
    assert(total_exceptions_thrown == NUM_THREADS);
    assert(total_exceptions_caught == NUM_THREADS);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 3: Concurrent Exception Handling (AC #4)
// ============================================================================

void *thread_concurrent_exceptions(void *arg) {
    int thread_id = *(int *)arg;

    // Simulate multiple exception cycles per thread
    for (int i = 0; i < 10; i++) {
        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = nullptr;
        frame.exception_object = nullptr;
        frame.exception_type = nullptr;

        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            struct ThreadException *ex = (struct ThreadException *)malloc(sizeof(struct ThreadException));
            ThreadException__ctor(ex, thread_id, "Concurrent test");
            total_exceptions_thrown++;
            cxx_throw(ex, "ThreadException");

            assert(false);
        } else {
            total_exceptions_caught++;

            struct ThreadException *caught = (struct ThreadException *)frame.exception_object;
            ThreadException__dtor(caught);
            free(caught);
        }
    }

    return nullptr;
}

void test_concurrent_exception_handling() {
    std::cout << "Test 3: Concurrent exception handling stress test... ";
    reset_atomic_counters();

    const int NUM_THREADS = 20;
    const int EXCEPTIONS_PER_THREAD = 10;
    pthread_t threads[NUM_THREADS];
    int thread_ids[NUM_THREADS];

    // Create threads
    for (int i = 0; i < NUM_THREADS; i++) {
        thread_ids[i] = i;
        int rc = pthread_create(&threads[i], nullptr, thread_concurrent_exceptions, &thread_ids[i]);
        assert(rc == 0);
    }

    // Wait for all threads
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], nullptr);
    }

    // THEN: All exceptions handled correctly
    int expected_total = NUM_THREADS * EXCEPTIONS_PER_THREAD;
    assert(total_exceptions_thrown == expected_total);
    assert(total_exceptions_caught == expected_total);
    assert(total_destructors_called == expected_total);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 4: Nested Try-Catch in Threads (AC #4)
// ============================================================================

void *thread_nested_exceptions(void *arg) {
    int thread_id = *(int *)arg;

    // Outer frame
    struct __cxx_exception_frame outer_frame;
    outer_frame.next = __cxx_exception_stack;
    outer_frame.actions = nullptr;
    outer_frame.exception_object = nullptr;
    outer_frame.exception_type = nullptr;

    if (setjmp(outer_frame.jmpbuf) == 0) {
        __cxx_exception_stack = &outer_frame;

        // Inner frame
        struct __cxx_exception_frame inner_frame;
        inner_frame.next = __cxx_exception_stack;
        inner_frame.actions = nullptr;
        inner_frame.exception_object = nullptr;
        inner_frame.exception_type = nullptr;

        if (setjmp(inner_frame.jmpbuf) == 0) {
            __cxx_exception_stack = &inner_frame;

            struct ThreadException *ex = (struct ThreadException *)malloc(sizeof(struct ThreadException));
            ThreadException__ctor(ex, thread_id, "Nested thread exception");
            total_exceptions_thrown++;
            cxx_throw(ex, "ThreadException");

            assert(false);
        } else {
            // Inner catch
            total_exceptions_caught++;

            struct ThreadException *caught = (struct ThreadException *)inner_frame.exception_object;
            ThreadException__dtor(caught);
            free(caught);
        }

        __cxx_exception_stack = outer_frame.next;
    } else {
        // Outer catch should not be reached
        assert(false);
    }

    return nullptr;
}

void test_nested_exceptions_in_threads() {
    std::cout << "Test 4: Nested exceptions in multiple threads... ";
    reset_atomic_counters();

    const int NUM_THREADS = 5;
    pthread_t threads[NUM_THREADS];
    int thread_ids[NUM_THREADS];

    for (int i = 0; i < NUM_THREADS; i++) {
        thread_ids[i] = i;
        int rc = pthread_create(&threads[i], nullptr, thread_nested_exceptions, &thread_ids[i]);
        assert(rc == 0);
    }

    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], nullptr);
    }

    assert(total_exceptions_thrown == NUM_THREADS);
    assert(total_exceptions_caught == NUM_THREADS);
    assert(total_destructors_called == NUM_THREADS);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 5: Thread Safety with Main Thread (AC #4)
// ============================================================================

void *thread_worker(void *arg) {
    int thread_id = *(int *)arg;

    struct __cxx_exception_frame frame;
    frame.next = __cxx_exception_stack;
    frame.actions = nullptr;
    frame.exception_object = nullptr;
    frame.exception_type = nullptr;

    if (setjmp(frame.jmpbuf) == 0) {
        __cxx_exception_stack = &frame;

        struct ThreadException *ex = (struct ThreadException *)malloc(sizeof(struct ThreadException));
        ThreadException__ctor(ex, thread_id, "Worker thread");
        total_exceptions_thrown++;
        cxx_throw(ex, "ThreadException");

        assert(false);
    } else {
        total_exceptions_caught++;

        struct ThreadException *caught = (struct ThreadException *)frame.exception_object;
        ThreadException__dtor(caught);
        free(caught);
    }

    return nullptr;
}

void test_main_thread_and_workers() {
    std::cout << "Test 5: Main thread + worker threads exception handling... ";
    reset_atomic_counters();

    const int NUM_WORKERS = 4;
    pthread_t workers[NUM_WORKERS];
    int worker_ids[NUM_WORKERS];

    // Start worker threads
    for (int i = 0; i < NUM_WORKERS; i++) {
        worker_ids[i] = i + 1;  // IDs 1-4
        int rc = pthread_create(&workers[i], nullptr, thread_worker, &worker_ids[i]);
        assert(rc == 0);
    }

    // Main thread also throws/catches
    {
        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = nullptr;
        frame.exception_object = nullptr;
        frame.exception_type = nullptr;

        if (setjmp(frame.jmpbuf) == 0) {
            __cxx_exception_stack = &frame;

            struct ThreadException *ex = (struct ThreadException *)malloc(sizeof(struct ThreadException));
            ThreadException__ctor(ex, 0, "Main thread");  // ID 0
            total_exceptions_thrown++;
            cxx_throw(ex, "ThreadException");

            assert(false);
        } else {
            total_exceptions_caught++;

            struct ThreadException *caught = (struct ThreadException *)frame.exception_object;
            assert(caught->thread_id == 0);
            ThreadException__dtor(caught);
            free(caught);
        }
    }

    // Wait for workers
    for (int i = 0; i < NUM_WORKERS; i++) {
        pthread_join(workers[i], nullptr);
    }

    // All threads (main + workers) handled exceptions
    assert(total_exceptions_thrown == NUM_WORKERS + 1);
    assert(total_exceptions_caught == NUM_WORKERS + 1);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Main
// ============================================================================

int main() {
    std::cout << "\n===========================================" << std::endl;
    std::cout << "Exception Thread Safety Tests" << std::endl;
    std::cout << "Story #82 - Epic #42" << std::endl;
    std::cout << "===========================================" << std::endl;
    std::cout << std::endl;

    std::cout << "--- Thread Safety Validation ---" << std::endl;
    test_multiple_threads_independent_exceptions();
    test_thread_local_stack_isolation();
    std::cout << std::endl;

    std::cout << "--- Concurrent Exception Handling ---" << std::endl;
    test_concurrent_exception_handling();
    test_nested_exceptions_in_threads();
    std::cout << std::endl;

    std::cout << "--- Main Thread + Workers ---" << std::endl;
    test_main_thread_and_workers();
    std::cout << std::endl;

    std::cout << "===========================================" << std::endl;
    std::cout << "All Thread Safety Tests Passed! ✓" << std::endl;
    std::cout << "===========================================" << std::endl;
    std::cout << std::endl;

    return 0;
}

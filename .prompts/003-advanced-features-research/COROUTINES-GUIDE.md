# Coroutines Implementation Guide for C++ to C Converter

**Document Version:** 1.0
**Created:** 2025-12-08
**Purpose:** Actionable implementation guidance for C++20 coroutines

---

## Executive Summary

**VERDICT: IMPLEMENTABLE with PROVEN PATTERN**

C++20 coroutines can be successfully implemented in C using state machine transformation patterns. This approach is well-proven in LLVM's coroutine passes, protothreads, and async/await implementations in other languages.

**Key Findings:**
- ✅ LLVM CoroSplit pass demonstrates complete transformation to state machines
- ✅ Protothreads provide proven C implementation pattern (Duff's device)
- ✅ Coroutine frame can be represented as heap-allocated C struct
- ✅ Suspend points become switch-case labels in state machine
- ✅ Local variables hoisted to frame structure
- ✅ No fundamental blockers identified

**Implementation Effort:** 5-6 weeks
**Technical Risk:** MEDIUM
**Complexity:** MEDIUM-HIGH
**Confidence:** HIGH

---

## What are Coroutines?

### Traditional Functions vs Coroutines

**Traditional Function:**
- Runs to completion
- Returns once
- Local variables on stack
- Cannot be paused/resumed

**Coroutine:**
- Can suspend execution
- Can be resumed later
- Preserves state across suspensions
- Returns multiple times (generators)

### C++20 Coroutine Keywords

1. **`co_await`** - Suspend execution until awaitable is ready
2. **`co_yield`** - Suspend and produce a value (generators)
3. **`co_return`** - Return final value and complete coroutine

**Presence of any keyword makes function a coroutine.**

---

## Core Concepts

### 1. Coroutine Frame

All coroutine state (parameters, local variables, temporaries, bookkeeping) is stored in a **coroutine frame** - typically heap-allocated.

**Contents:**
- Current suspend point (state machine state)
- Function parameters (copied)
- Local variables spanning suspend points
- Promise object
- Resume/destroy function pointers

### 2. Promise Object

The **promise** customizes coroutine behavior:
- `get_return_object()` - Returns coroutine handle to caller
- `initial_suspend()` - Controls eager vs lazy start
- `final_suspend()` - Controls completion behavior
- `return_value(v)` / `return_void()` - Handles `co_return`
- `unhandled_exception()` - Exception handling

### 3. Awaitable / Awaiter

An **awaitable** controls suspension behavior:
- `await_ready()` - Can we skip suspension?
- `await_suspend(handle)` - What to do when suspending?
- `await_resume()` - Returns result when resumed

### 4. Coroutine Handle

A **handle** is a pointer to the coroutine frame, allowing resumption/destruction:
```cpp
std::coroutine_handle<Promise> handle = /* ... */;
handle.resume();   // Resume execution
handle.destroy();  // Destroy frame
```

---

## State Machine Transformation

The key insight: **Transform coroutine into state machine.**

### Simple Example

**C++ Coroutine:**
```cpp
generator<int> count_to(int n) {
    for (int i = 0; i < n; i++) {
        co_yield i;
    }
}
```

**State Machine Concept:**
```
States:
- START: Begin execution
- SUSPENDED_AT_YIELD: After co_yield, before loop continues
- DONE: Coroutine completed

Transitions:
- START -> resume() -> execute loop, co_yield -> SUSPENDED_AT_YIELD
- SUSPENDED_AT_YIELD -> resume() -> continue loop, co_yield -> SUSPENDED_AT_YIELD
- SUSPENDED_AT_YIELD -> resume() -> loop ends -> DONE
```

---

## C Implementation Pattern

### Coroutine Frame Structure

**C++ Coroutine:**
```cpp
generator<int> count_to(int n) {
    for (int i = 0; i < n; i++) {
        co_yield i;
    }
}
```

**Generated C Frame:**
```c
// Coroutine states
enum __coro_state {
    CORO_STATE_START = 0,
    CORO_STATE_SUSPENDED_1 = 1,
    CORO_STATE_DONE = 2
};

// Coroutine frame (heap-allocated)
struct count_to_frame {
    // Bookkeeping
    enum __coro_state state;           // Current suspend point
    void (*resume_fn)(void*);          // Resume function pointer
    void (*destroy_fn)(void*);         // Destroy function pointer

    // Promise object
    struct generator_int_promise promise;

    // Parameters (copied from call site)
    int n;

    // Local variables that span suspend points
    int i;

    // Current yielded value
    int current_value;
};
```

### Resume Function (State Machine)

**Generated C Resume Function:**
```c
void count_to_resume(struct count_to_frame* frame) {
    // State machine dispatch
    switch (frame->state) {
        case CORO_STATE_START:
            goto label_start;

        case CORO_STATE_SUSPENDED_1:
            goto label_resume_1;

        case CORO_STATE_DONE:
            return;  // Already done
    }

label_start:
    // Initialize loop variable
    frame->i = 0;

label_loop:
    // Loop condition check
    if (frame->i < frame->n) {
        // co_yield i;
        frame->current_value = frame->i;
        frame->i++;  // Increment for next iteration

        // Suspend at this point
        frame->state = CORO_STATE_SUSPENDED_1;
        return;  // Suspend

label_resume_1:
        // Resume here after co_yield
        goto label_loop;  // Continue loop
    }

    // Loop ended, coroutine done
    frame->state = CORO_STATE_DONE;
}
```

### Destroy Function

**Generated C Destroy Function:**
```c
void count_to_destroy(struct count_to_frame* frame) {
    // Run destructors for any objects still alive
    // (In this simple example, none)

    // Call promise destructor
    generator_int_promise__dtor(&frame->promise);

    // Free frame memory
    free(frame);
}
```

### Initial Creation Function

**Generated C Creation Function:**
```c
struct generator_int count_to(int n) {
    // Allocate coroutine frame
    struct count_to_frame* frame = (struct count_to_frame*)
        malloc(sizeof(struct count_to_frame));

    // Initialize frame
    frame->state = CORO_STATE_START;
    frame->resume_fn = (void(*)(void*))count_to_resume;
    frame->destroy_fn = (void(*)(void*))count_to_destroy;

    // Copy parameters
    frame->n = n;

    // Initialize promise
    generator_int_promise__ctor(&frame->promise);

    // Call promise.get_return_object()
    struct generator_int result = generator_int_promise__get_return_object(
        &frame->promise, frame
    );

    // Check initial_suspend()
    if (generator_int_promise__initial_suspend(&frame->promise)) {
        // Lazy start - don't run yet
    } else {
        // Eager start - run until first suspend
        count_to_resume(frame);
    }

    return result;
}
```

### Generator Type

**C Generator Wrapper:**
```c
// Generator type (returned to caller)
struct generator_int {
    struct count_to_frame* frame;  // Pointer to coroutine frame
};

// Generator operations
int generator_int__next(struct generator_int* gen, int* value_out) {
    if (gen->frame->state == CORO_STATE_DONE) {
        return 0;  // No more values
    }

    // Resume coroutine
    count_to_resume(gen->frame);

    if (gen->frame->state == CORO_STATE_DONE) {
        return 0;  // Just finished
    }

    // Get yielded value
    *value_out = gen->frame->current_value;
    return 1;  // Success
}

void generator_int__destroy(struct generator_int* gen) {
    if (gen->frame) {
        count_to_destroy(gen->frame);
        gen->frame = NULL;
    }
}
```

### Usage Example

**Generated C Usage:**
```c
// Create generator
struct generator_int gen = count_to(5);

// Iterate through values
int value;
while (generator_int__next(&gen, &value)) {
    printf("%d\n", value);  // Prints 0, 1, 2, 3, 4
}

// Cleanup
generator_int__destroy(&gen);
```

---

## Promise Type Implementation

The promise customizes coroutine behavior. Different coroutine types have different promises.

### Generator Promise

**C++ Promise (Conceptual):**
```cpp
template<typename T>
struct generator_promise {
    T current_value;

    generator<T> get_return_object() {
        return generator<T>{this};
    }

    std::suspend_always initial_suspend() { return {}; }  // Lazy
    std::suspend_always final_suspend() noexcept { return {}; }
    void return_void() {}
    void unhandled_exception() { std::terminate(); }

    std::suspend_always yield_value(T value) {
        current_value = value;
        return {};
    }
};
```

**Generated C Promise:**
```c
struct generator_int_promise {
    int current_value;  // Last yielded value
};

void generator_int_promise__ctor(struct generator_int_promise* p) {
    p->current_value = 0;
}

void generator_int_promise__dtor(struct generator_int_promise* p) {
    // No cleanup needed for int
}

struct generator_int generator_int_promise__get_return_object(
    struct generator_int_promise* p,
    struct count_to_frame* frame)
{
    struct generator_int gen = { .frame = frame };
    return gen;
}

int generator_int_promise__initial_suspend(struct generator_int_promise* p) {
    return 1;  // true = suspend (lazy start)
}

int generator_int_promise__final_suspend(struct generator_int_promise* p) {
    return 1;  // true = suspend (don't auto-destroy)
}

void generator_int_promise__return_void(struct generator_int_promise* p) {
    // No-op for generators
}

void generator_int_promise__yield_value(struct generator_int_promise* p, int value) {
    p->current_value = value;
}
```

---

## Awaitable Implementation

Awaitables control `co_await` behavior.

### Simple Suspend Always/Never

**C++ Awaitables:**
```cpp
struct suspend_always {
    bool await_ready() const noexcept { return false; }  // Always suspend
    void await_suspend(coroutine_handle<>) const noexcept {}
    void await_resume() const noexcept {}
};

struct suspend_never {
    bool await_ready() const noexcept { return true; }  // Never suspend
    void await_suspend(coroutine_handle<>) const noexcept {}
    void await_resume() const noexcept {}
};
```

**Generated C:**
```c
// suspend_always
int suspend_always__await_ready() { return 0; }  // false
void suspend_always__await_suspend(void* handle) {}
void suspend_always__await_resume() {}

// suspend_never
int suspend_never__await_ready() { return 1; }  // true
void suspend_never__await_suspend(void* handle) {}
void suspend_never__await_resume() {}
```

### Complex Awaitable Example

**C++ Async Read:**
```cpp
struct async_read_awaitable {
    int fd;
    char* buffer;
    size_t size;
    ssize_t result;

    bool await_ready() {
        // Check if data is immediately available
        return check_ready(fd);
    }

    void await_suspend(coroutine_handle<> handle) {
        // Start async read, resume handle when done
        async_read_start(fd, buffer, size, handle);
    }

    ssize_t await_resume() {
        // Return result of async operation
        return result;
    }
};
```

**Generated C:**
```c
struct async_read_awaitable {
    int fd;
    char* buffer;
    size_t size;
    ssize_t result;
};

int async_read_awaitable__await_ready(struct async_read_awaitable* self) {
    return check_ready(self->fd);
}

void async_read_awaitable__await_suspend(
    struct async_read_awaitable* self,
    void* handle)
{
    async_read_start(self->fd, self->buffer, self->size, handle);
}

ssize_t async_read_awaitable__await_resume(struct async_read_awaitable* self) {
    return self->result;
}
```

---

## `co_await` Transformation

**C++ Code:**
```cpp
task<void> read_file(int fd) {
    char buffer[1024];
    ssize_t n = co_await async_read(fd, buffer, sizeof(buffer));
    printf("Read %zd bytes\n", n);
}
```

**Generated C (Simplified):**
```c
struct read_file_frame {
    enum __coro_state state;
    void (*resume_fn)(void*);
    void (*destroy_fn)(void*);
    struct task_void_promise promise;

    // Parameters
    int fd;

    // Locals
    char buffer[1024];
    ssize_t n;

    // Temporary awaitable
    struct async_read_awaitable __await_temp;
};

void read_file_resume(struct read_file_frame* frame) {
    switch (frame->state) {
        case CORO_STATE_START:
            goto label_start;
        case CORO_STATE_SUSPENDED_1:
            goto label_resume_1;
        case CORO_STATE_DONE:
            return;
    }

label_start:
    // Setup co_await async_read(...)
    async_read_awaitable__init(&frame->__await_temp,
                                frame->fd,
                                frame->buffer,
                                sizeof(frame->buffer));

    // Check await_ready()
    if (async_read_awaitable__await_ready(&frame->__await_temp)) {
        // Don't suspend, get result immediately
        frame->n = async_read_awaitable__await_resume(&frame->__await_temp);
        goto label_after_await;
    }

    // Need to suspend
    frame->state = CORO_STATE_SUSPENDED_1;
    async_read_awaitable__await_suspend(&frame->__await_temp, frame);
    return;  // Suspend here

label_resume_1:
    // Resumed after await
    frame->n = async_read_awaitable__await_resume(&frame->__await_temp);

label_after_await:
    // Continue after co_await
    printf("Read %zd bytes\n", frame->n);

    // Coroutine done
    frame->state = CORO_STATE_DONE;
}
```

---

## `co_yield` Transformation

`co_yield value` is syntactic sugar for `co_await promise.yield_value(value)`.

**C++ Code:**
```cpp
generator<int> fibonacci() {
    int a = 0, b = 1;
    while (true) {
        co_yield a;
        int next = a + b;
        a = b;
        b = next;
    }
}
```

**Generated C:**
```c
struct fibonacci_frame {
    enum __coro_state state;
    void (*resume_fn)(void*);
    void (*destroy_fn)(void*);
    struct generator_int_promise promise;

    // Locals
    int a;
    int b;
    int next;
};

void fibonacci_resume(struct fibonacci_frame* frame) {
    switch (frame->state) {
        case CORO_STATE_START:
            goto label_start;
        case CORO_STATE_SUSPENDED_1:
            goto label_resume_1;
        case CORO_STATE_DONE:
            return;
    }

label_start:
    // Initialize
    frame->a = 0;
    frame->b = 1;

label_loop:
    // co_yield a; => co_await promise.yield_value(a);
    generator_int_promise__yield_value(&frame->promise, frame->a);

    // yield_value returns suspend_always, so always suspend
    frame->state = CORO_STATE_SUSPENDED_1;
    return;  // Suspend

label_resume_1:
    // Compute next value
    frame->next = frame->a + frame->b;
    frame->a = frame->b;
    frame->b = frame->next;

    goto label_loop;  // Continue infinite loop
}
```

---

## `co_return` Transformation

**C++ Code:**
```cpp
task<int> compute() {
    int result = 42;
    co_return result;
}
```

**Generated C:**
```c
void compute_resume(struct compute_frame* frame) {
    switch (frame->state) {
        case CORO_STATE_START:
            goto label_start;
        case CORO_STATE_DONE:
            return;
    }

label_start:
    // int result = 42;
    frame->result = 42;

    // co_return result; => promise.return_value(result);
    task_int_promise__return_value(&frame->promise, frame->result);

    // Then co_await promise.final_suspend();
    // (Simplified: assume final_suspend returns suspend_always)
    frame->state = CORO_STATE_DONE;
    return;
}
```

---

## Frame Allocation and Deallocation

### Heap Allocation (Default)

**Allocation:**
```c
struct coroutine_frame* frame = (struct coroutine_frame*)
    malloc(sizeof(struct coroutine_frame));
```

**Deallocation:**
```c
void coroutine_destroy(struct coroutine_frame* frame) {
    // Run destructors
    // ...

    // Free frame
    free(frame);
}
```

### Optimization: Inline Frames (HALO)

LLVM's Heap Allocation eLision Optimization (HALO) can eliminate heap allocation if:
- Coroutine lifetime is fully enclosed by caller
- Frame doesn't escape
- All suspend points are known

**Optimized (No Heap):**
```c
void caller() {
    // Allocate frame on stack
    struct coroutine_frame frame;

    // Initialize and run
    coroutine_init(&frame);
    coroutine_resume(&frame);

    // Cleanup
    coroutine_cleanup(&frame);
}
```

**Not implemented initially - heap allocation is simpler.**

---

## Protothreads Pattern (Duff's Device)

Historical C implementation using Duff's device - very compact but limited.

### Pattern

**Protothread Macro-Based:**
```c
#define PT_BEGIN(pt) switch((pt)->state) { case 0:
#define PT_YIELD(pt) \
    do { \
        (pt)->state = __LINE__; \
        return; \
        case __LINE__:; \
    } while(0)
#define PT_END(pt) }

struct pt {
    int state;  // Actually line number!
};

int protothread_example(struct pt* pt) {
    PT_BEGIN(pt);

    printf("Before yield\n");
    PT_YIELD(pt);

    printf("After yield\n");
    PT_YIELD(pt);

    PT_END(pt);
    return 0;
}
```

**Limitations:**
- Can't use local variables (lost between yields)
- Can't nest switch statements
- Line number hack is fragile

**Our Approach:** Explicit state enum + manual labels (more robust).

---

## LLVM Coroutine Lowering

LLVM implements coroutines with multiple passes:

### CoroEarly Pass
- Lowers coroutine intrinsics
- Prepares for splitting

### CoroSplit Pass
**Key transformation:** Splits coroutine into:
1. **Ramp function** - Entry point, allocates frame, runs until first suspend
2. **Resume function(s)** - Continues from suspend point
3. **Destroy function** - Cleanup and deallocation

**CoroFrame sub-pass:**
- Identifies variables that span suspend points
- Hoists them into coroutine frame struct
- Rewrites references to use frame

### CoroElide Pass
- Eliminates heap allocation when safe
- Inlines coroutine calls

### CoroCleanup Pass
- Removes coroutine intrinsics
- Final cleanup

**Our Strategy:** Implement similar transformation at AST level, generate C directly.

---

## Code Generation Strategy

### Phase 1: Coroutine Detection

**Identify Coroutines:**
- Scan function body for `co_await`, `co_yield`, `co_return`
- Mark function as coroutine

### Phase 2: Frame Analysis

**Identify Frame Contents:**
1. **Parameters** - Copy all parameters to frame
2. **Locals spanning suspends** - Hoist to frame
3. **Temporaries** - Hoist if alive across suspend
4. **Promise** - Always in frame
5. **State** - Suspend point tracking

**Algorithm:**
- Build control flow graph (CFG)
- Identify suspend points
- Perform liveness analysis
- Hoist live-across-suspend variables

### Phase 3: State Machine Generation

**Assign State Numbers:**
```c
enum __coro_state {
    CORO_STATE_START = 0,
    CORO_STATE_SUSPENDED_1 = 1,
    CORO_STATE_SUSPENDED_2 = 2,
    // ... one per suspend point
    CORO_STATE_DONE = N
};
```

**Generate Switch Dispatch:**
```c
void coro_resume(struct frame* f) {
    switch (f->state) {
        case CORO_STATE_START: goto label_start;
        case CORO_STATE_SUSPENDED_1: goto label_resume_1;
        // ...
        case CORO_STATE_DONE: return;
    }
    // Unreachable
}
```

### Phase 4: Transform Suspend Points

**For Each `co_yield`:**
```c
// Before:
co_yield value;

// After:
promise__yield_value(&frame->promise, value);
frame->state = CORO_STATE_SUSPENDED_N;
return;  // Suspend
label_resume_N:
// Continue here
```

**For Each `co_await`:**
```c
// Before:
result = co_await awaitable;

// After:
awaitable__init(&frame->__await_temp, ...);
if (!awaitable__await_ready(&frame->__await_temp)) {
    frame->state = CORO_STATE_SUSPENDED_N;
    awaitable__await_suspend(&frame->__await_temp, frame);
    return;  // Suspend
    label_resume_N:;
}
result = awaitable__await_resume(&frame->__await_temp);
```

**For Each `co_return`:**
```c
// Before:
co_return value;

// After:
promise__return_value(&frame->promise, value);
// (final_suspend handling)
frame->state = CORO_STATE_DONE;
return;
```

### Phase 5: Generate Entry Function

**Ramp Function:**
```c
ReturnType coroutine_name(params...) {
    // Allocate frame
    struct coroutine_name_frame* frame = malloc(sizeof(*frame));

    // Initialize
    frame->state = CORO_STATE_START;
    frame->resume_fn = coroutine_name_resume;
    frame->destroy_fn = coroutine_name_destroy;

    // Copy parameters
    frame->param1 = param1;
    // ...

    // Construct promise
    promise__ctor(&frame->promise);

    // Get return object
    ReturnType ret = promise__get_return_object(&frame->promise, frame);

    // Handle initial_suspend
    if (!promise__initial_suspend(&frame->promise)) {
        coroutine_name_resume(frame);  // Eager start
    }

    return ret;
}
```

---

## Edge Cases and Corner Cases

### 1. Exception Handling

**C++ Rule:** Exceptions propagate out of coroutines, call `promise.unhandled_exception()`.

**Implementation:**
```c
void coro_resume(struct frame* f) {
    struct __exception_context ex_ctx;
    if (__setjmp(ex_ctx.jmp_buf) == 0) {
        __exception_push(&ex_ctx);

        // ... coroutine body ...

        __exception_pop();
    } else {
        // Exception caught
        promise__unhandled_exception(&f->promise, ex_ctx.exception);
    }
}
```

### 2. Destructors for Frame Variables

**Problem:** Objects in frame may need destruction.

**Solution:** Track which objects are alive at each suspend point, run destructors in destroy function.

```c
void coro_destroy(struct frame* f) {
    switch (f->state) {
        case CORO_STATE_SUSPENDED_1:
            // Destruct objects alive at suspend 1
            object1__dtor(&f->object1);
            // Fall through
        case CORO_STATE_START:
            // Destruct promise
            promise__dtor(&f->promise);
            break;
    }
    free(f);
}
```

### 3. Coroutine Handle Operations

**Operations:**
- `handle.resume()` - Resume coroutine
- `handle.destroy()` - Destroy coroutine
- `handle.done()` - Check if done
- `handle.promise()` - Get promise reference

**Implementation:**
```c
struct coroutine_handle {
    struct coroutine_frame* frame;
};

void coroutine_handle__resume(struct coroutine_handle* h) {
    h->frame->resume_fn(h->frame);
}

void coroutine_handle__destroy(struct coroutine_handle* h) {
    h->frame->destroy_fn(h->frame);
}

int coroutine_handle__done(struct coroutine_handle* h) {
    return h->frame->state == CORO_STATE_DONE;
}

void* coroutine_handle__promise(struct coroutine_handle* h) {
    return &h->frame->promise;
}
```

### 4. Symmetric Transfer

**C++20 Feature:** `await_suspend` can return another coroutine_handle to transfer control.

**C++ Code:**
```cpp
coroutine_handle<> await_suspend(coroutine_handle<> h) {
    return other_coroutine;  // Symmetric transfer
}
```

**Generated C:**
```c
void* awaitable__await_suspend(struct awaitable* self, void* handle) {
    return self->other_coroutine;  // Return next coroutine to run
}

// In resume function:
void* next = awaitable__await_suspend(&frame->__await_temp, frame);
if (next != NULL) {
    // Symmetric transfer: tail call to next coroutine
    struct coroutine_frame* next_frame = (struct coroutine_frame*)next;
    return next_frame->resume_fn(next_frame);  // Tail call
}
```

### 5. Coroutines with Return Values (task<T>)

**Promise stores result:**
```c
struct task_int_promise {
    int result;
    int exception_pending;
};

void task_int_promise__return_value(struct task_int_promise* p, int value) {
    p->result = value;
}

int task_int__get_result(struct task_int* task) {
    if (task->frame->promise.exception_pending) {
        // Re-throw exception
        __cxx_rethrow(task->frame->promise.exception);
    }
    return task->frame->promise.result;
}
```

---

## Optimizations

### 1. Eliminate Heap Allocation (HALO)

**Condition:** Coroutine lifetime fully enclosed, frame doesn't escape.

**Optimization:** Allocate frame on caller's stack.

**Implementation:** Defer to later versions (complex analysis required).

### 2. Inline Small Coroutines

**Condition:** Single suspend point, no loops.

**Optimization:** Inline as explicit state machine in caller.

### 3. Devirtualize Resume Function

**Optimization:** If coroutine type known at call site, call resume directly instead of through function pointer.

```c
// Instead of:
frame->resume_fn(frame);

// Generate:
count_to_resume(frame);
```

### 4. Reuse Frame Allocations

**Optimization:** Pool of coroutine frames to reduce malloc/free overhead.

---

## Testing Strategy

### Unit Tests

**1. Simple Generator:**
```c
void test_generator() {
    struct generator_int gen = count_to(3);
    int value;

    assert(generator_int__next(&gen, &value) && value == 0);
    assert(generator_int__next(&gen, &value) && value == 1);
    assert(generator_int__next(&gen, &value) && value == 2);
    assert(!generator_int__next(&gen, &value));  // Done

    generator_int__destroy(&gen);
}
```

**2. Async Task:**
```c
void test_async_task() {
    struct task_int task = async_compute();

    // Run event loop until task completes
    while (!coroutine_handle__done(&task.handle)) {
        run_event_loop_iteration();
    }

    int result = task_int__get_result(&task);
    assert(result == 42);
}
```

**3. Exception Handling:**
```c
void test_coroutine_exception() {
    struct task_void task = coro_with_exception();

    // Should call promise.unhandled_exception()
    // and propagate exception
    int exception_caught = 0;
    // ... exception handling test ...
    assert(exception_caught);
}
```

### Integration Tests

**4. Complex Control Flow:**
- Multiple suspend points
- Loops with co_yield
- Nested co_await

**5. Interoperability:**
- Coroutines calling other coroutines
- Mixing coroutines with regular functions

### Performance Tests

**6. Benchmark:**
- Frame allocation overhead
- State machine dispatch overhead
- Comparison with native C++ coroutines

---

## Implementation Checklist

### Phase 1: Promise/Awaitable Infrastructure (Week 1)
- [ ] Define coroutine_handle structure
- [ ] Implement basic promise types (generator, task)
- [ ] Implement basic awaitables (suspend_always, suspend_never)
- [ ] Test: Basic promise/awaitable functionality

### Phase 2: Frame Analysis (Week 1-2)
- [ ] Detect coroutine functions (co_await/co_yield/co_return)
- [ ] Build control flow graph
- [ ] Identify suspend points
- [ ] Perform liveness analysis
- [ ] Determine frame contents (hoisted variables)
- [ ] Test: Verify frame structure correct

### Phase 3: State Machine Generation (Week 2-3)
- [ ] Assign state numbers to suspend points
- [ ] Generate switch-based dispatch
- [ ] Generate labels for resume points
- [ ] Transform suspend points to state updates + return
- [ ] Test: Verify state machine transitions

### Phase 4: Transformation (Week 3-4)
- [ ] Transform co_yield statements
- [ ] Transform co_await expressions
- [ ] Transform co_return statements
- [ ] Generate ramp function (entry point)
- [ ] Generate resume function
- [ ] Generate destroy function
- [ ] Test: Simple coroutines work end-to-end

### Phase 5: Edge Cases (Week 4-5)
- [ ] Handle exceptions in coroutines
- [ ] Handle destructors for frame objects
- [ ] Handle symmetric transfer
- [ ] Handle coroutines with return values
- [ ] Test: All edge cases pass

### Phase 6: Standard Library Support (Week 5-6)
- [ ] Implement std::coroutine_handle
- [ ] Implement std::suspend_always/never
- [ ] Implement common promise types
- [ ] Test: Works with standard coroutine patterns

### Phase 7: Optimization and Polish (Week 6)
- [ ] Optimize simple cases
- [ ] Minimize frame size
- [ ] Performance tuning
- [ ] Documentation and examples

---

## Dependencies

**Prerequisites:**
- ✅ Exception handling (for promise.unhandled_exception())
- ✅ RAII/destructors (for frame cleanup)
- Heap allocation (malloc/free)

**No dependencies on:**
- RTTI (not needed for coroutines)
- Virtual inheritance (orthogonal feature)

---

## Complexity Assessment

**Overall Complexity: MEDIUM-HIGH**

**What Makes It Medium-High:**
- Control flow analysis required (CFG, liveness)
- State machine generation is non-trivial
- Frame allocation and lifetime management
- Many edge cases (exceptions, destructors)

**Main Challenges:**
1. **Liveness Analysis** - Determining which variables to hoist
2. **Control Flow Rewriting** - Transforming to state machine
3. **Promise/Awaitable Abstraction** - Supporting arbitrary types
4. **Symmetric Transfer** - Tail call optimization

**Why Not More Complex:**
- Well-defined transformation (LLVM CoroSplit reference)
- Protothreads provide simpler C pattern
- Can start with simple cases (generators only)
- Standard library support can be incremental

---

## Risk Assessment

**Technical Risk: MEDIUM**

**Mitigating Factors:**
- ✅ LLVM CoroSplit provides detailed transformation algorithm
- ✅ Protothreads prove C state machine pattern works
- ✅ Can implement incrementally (generators first)
- ✅ Well-specified in C++20 standard

**Risks:**
1. **Complex Control Flow** - Loops, branches with suspend points
   - Mitigation: Build robust CFG, extensive testing
2. **Frame Size** - Hoisting too many variables
   - Mitigation: Precise liveness analysis, optimize later
3. **Performance Overhead** - State machine dispatch, heap allocation
   - Mitigation: Optimize common cases, consider HALO in future

**Confidence Level: HIGH**

Coroutines are implementable with known transformation patterns. Complexity is manageable with careful engineering.

---

## Recommendations

### Priority: MEDIUM

Coroutines should be implemented after RTTI and virtual inheritance (v1.6) because:
1. Less commonly used than RTTI (cutting-edge C++20 feature)
2. More complex implementation (5-6 weeks)
3. No dependencies on coroutines from other features

### Implementation Approach

**Phase 1 (Minimal - Generators):**
- Simple generators with co_yield only
- Fixed promise type
- No complex control flow

**Phase 2 (Tasks):**
- Add co_await support
- Awaitable abstraction
- Async task pattern

**Phase 3 (Complete):**
- co_return with values
- Exception handling
- Symmetric transfer
- All edge cases

### Testing Approach

1. Start with LLVM coroutine test suite
2. Test against C++20 compiler output
3. Use cppcoro library test cases
4. Performance benchmarks vs native

---

## References and Sources

### Primary Specifications
- [C++20 Coroutines - cppreference.com](https://en.cppreference.com/w/cpp/language/coroutines)
- [Coroutines TS Specification](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2019/p1477r0.pdf)

### LLVM Implementation
- [Coroutines in LLVM - Official Documentation](https://llvm.org/docs/Coroutines.html)
- [LLVM CoroSplit.cpp Source](https://llvm.org/doxygen/CoroSplit_8cpp_source.html)
- [Debugging C++ Coroutines - Clang](https://clang.llvm.org/docs/DebuggingCoroutines.html)

### Protothreads Pattern
- [Protothreads - Wikipedia](https://en.wikipedia.org/wiki/Protothread)
- [Hacking Coroutines into C](https://wiomoc.de/misc/posts/hacking_coroutines_into_c.html)
- [On Duff's Device and Coroutines](https://research.swtch.com/duff)
- [Coroutines in C - Simon Tatham](https://www.chiark.greenend.org.uk/~sgtatham/coroutines.html)

### Technical Articles
- [C++ Coroutines: Understanding the Compiler Transform - Lewis Baker](https://lewissbaker.github.io/2022/08/27/understanding-the-compiler-transform)
- [C++ Coroutines: Understanding operator co_await - Lewis Baker](https://lewissbaker.github.io/2017/11/17/understanding-operator-co-await)
- [C++ Coroutines: Understanding the promise type - Lewis Baker](https://lewissbaker.github.io/2018/09/05/understanding-the-promise-type)
- [C++ Coroutines: Understanding Symmetric Transfer - Lewis Baker](https://lewissbaker.github.io/2020/05/11/understanding_symmetric_transfer)
- [My tutorial and take on C++20 coroutines - Stanford](https://www.scs.stanford.edu/~dm/blog/c++-coroutines.html)
- [C++20 Coroutines: sketching a minimal async framework](https://www.jeremyong.com/cpp/2021/01/04/cpp20-coroutines-a-minimal-async-framework/)

---

## Conclusion

C++20 coroutines implementation in a C++ to C converter is **feasible** using state machine transformation patterns. The feature is well-specified, has reference implementations (LLVM CoroSplit), and proven C patterns (protothreads).

**Key Success Factors:**
1. ✅ LLVM CoroSplit provides complete transformation algorithm
2. ✅ Protothreads demonstrate C state machine viability
3. ✅ C++20 standard provides clear semantics
4. ✅ Can implement incrementally (generators → tasks → full)
5. ✅ Manageable complexity (5-6 weeks)

**Next Steps:**
1. Implement RTTI first (v1.4)
2. Implement virtual inheritance (v1.5)
3. Begin coroutines with simple generators (v1.6)
4. Add full co_await/task support
5. Optimize after correctness

**Confidence:** HIGH - Feature is implementable with known patterns and reasonable effort.

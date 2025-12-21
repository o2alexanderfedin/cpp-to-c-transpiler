# Phase 12 Plan: Exception Handling Integration (v2.5.0)

**Phase**: 12 of 17
**Roadmap**: `../../ROADMAP.md`
**Brief**: `../../BRIEF.md`
**Target Version**: v2.5.0
**Status**: PENDING
**Priority**: HIGH-VALUE (Tier 2 - Infrastructure exists)
**Prerequisite**: Phase 9 (Virtual Methods recommended for RTTI integration)

## Phase Goal

Integrate exception translation infrastructure (`TryCatchTransformer`, `ThrowTranslator`, `exception_runtime`) into the main transpiler by implementing `VisitCXXTryStmt` and `VisitCXXThrowExpr` visitor methods. Enable C++ exception handling through setjmp/longjmp-based stack unwinding with automatic destructor invocation and type-based catch handler matching.

## Business Value

Exception handling is critical for:
- Robust error handling in production C++ code
- Resource cleanup (RAII integration during stack unwinding)
- Type-safe error propagation across function boundaries
- Separation of normal and error-handling code paths
- Compatibility with standard C++ libraries (std::exception family)

**Impact**: Without exception handling, transpiled C++ cannot execute programs that rely on try-catch blocks—common in professional C++ codebases.

## Deliverables

### Source Code
- [ ] Implement `CppToCVisitor::VisitCXXTryStmt(CXXTryStmt *S)` visitor method
- [ ] Implement `CppToCVisitor::VisitCXXThrowExpr(CXXThrowExpr *E)` visitor method
- [ ] Integration of `TryCatchTransformer::transform()` for try-catch blocks
- [ ] Integration of `ThrowTranslator::translate()` for throw expressions
- [ ] Exception runtime library linking (`exception_runtime.cpp`)
- [ ] Action table generation for destructor unwinding
- [ ] Frame management code (push/pop exception frames)

### Tests
- [ ] `tests/ExceptionHandlingIntegrationTest.cpp` (15+ tests)
  - Basic try-catch with matching exception type
  - Multiple catch handlers with type fallthrough
  - Nested try-catch blocks (outer/inner exception propagation)
  - Exception re-throw (`throw;`) in catch handler
  - Stack unwinding with destructor calls
  - Uncaught exception propagation to outer scope
  - Catch-all handler (`catch(...)`)
  - Exception constructor with parameters
  - Exception type mismatch (exception propagates up)
  - Multiple destructors during unwinding (RAII)
  - Exception in destructor during unwinding
  - Function call that throws (transparent exception propagation)
  - Return from catch handler (exception consumed)
  - Nested function calls with exception boundaries
  - Exception object lifetime (heap allocation, deallocation)
  - Performance baseline (overhead <20%)

### CLI Integration
- [ ] Add `--enable-exceptions={off,on}` flag (default: on)
- [ ] Add `--exception-model={sjlj,tables}` for future extension (currently SJLJ only)

### Documentation
- [ ] Update `docs/CHANGELOG.md` for v2.5.0
- [ ] Update `README.md` with exception handling feature
- [ ] Update `website/src/pages/features.astro`
- [ ] Create `docs/examples/exception-handling.md` with C++ → C translation examples
- [ ] Document stack unwinding semantics and RAII integration

### Release
- [ ] Git-flow release v2.5.0
- [ ] Tag on GitHub with release notes

## Technical Design

### Architecture Overview

Exception handling uses **Setjmp/Longjmp (SJLJ) model** with action tables for RAII:

```
┌─────────────────────────────────────────────────────────────────┐
│ Exception Handling Architecture (SJLJ with Action Tables)       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  throw expression → cxx_throw()                               │
│         ↓                                                       │
│  [Allocate exception object + construct]                       │
│         ↓                                                       │
│  cxx_throw(object, type_info)                                 │
│         ↓                                                       │
│  [Two-phase unwinding]                                         │
│    Phase 1: Walk action table → call destructors              │
│    Phase 2: longjmp to nearest catch frame                    │
│         ↓                                                       │
│  setjmp(frame.jmpbuf) returns non-zero → catch handler       │
│         ↓                                                       │
│  [Type matching] → call matching handler or re-throw          │
│         ↓                                                       │
│  Normal path or exception propagation                          │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Exception Frame Data Structure

```c
struct __cxx_exception_frame {
  jmp_buf jmpbuf;                           // setjmp/longjmp state
  struct __cxx_exception_frame *next;       // Stack linkage (previous frame)
  const struct __cxx_action_entry *actions; // Destructor sequence
  void *exception_object;                   // Thrown exception object
  const char *exception_type;               // Type name (for catch matching)
};

struct __cxx_action_entry {
  void (*destructor)(void *);  // Destructor function pointer
  void *object;                // Object instance to destroy
};
```

### C++ → C Translation Mapping

#### 1. Basic Try-Catch with Single Handler

**C++**:
```cpp
class Error {
  int code;
public:
  Error(int c) : code(c) {}
};

void test_basic() {
  try {
    Error e(42);
    throw e;
  } catch (Error& err) {
    printf("Caught error: %d\n", err.code);
  }
}
```

**C** (Generated):
```c
// Action table: lists destructors to call during unwinding
static struct __cxx_action_entry actions_table_0[] = {
  { Error__dtor, NULL },  // Placeholder for caught exception
  { NULL, NULL }
};

void test_basic() {
  // Exception frame setup
  struct __cxx_exception_frame frame;
  frame.next = __cxx_exception_stack;
  frame.actions = actions_table_0;

  // Setjmp guard: catches thrown exceptions
  if (setjmp(frame.jmpbuf) == 0) {
    // Try block execution (normal path)
    __cxx_exception_stack = &frame;

    {
      // Variable allocation and initialization
      struct Error e;
      Error__ctor(&e, 42);

      // Throw exception
      struct Error *__ex = (struct Error*)malloc(sizeof(struct Error));
      Error__copy_ctor(__ex, &e);
      cxx_throw(__ex, "Error");
      // cxx_throw never returns (longjmp)
    }

    // Restore stack on normal path
    __cxx_exception_stack = frame.next;
  } else {
    // Exception caught: setjmp returns non-zero
    // frame contains exception_object and exception_type

    // Type matching and handler dispatch
    if (strcmp(frame.exception_type, "Error") == 0) {
      struct Error *err = (struct Error*)frame.exception_object;

      // Catch handler body
      printf("Caught error: %d\n", err->code);

      // Clean up exception object
      Error__dtor(err);
      free(err);
    } else {
      // No matching handler: re-throw
      cxx_throw(frame.exception_object, frame.exception_type);
    }

    // Restore stack on exception path
    __cxx_exception_stack = frame.next;
  }
}
```

**Translation Steps**:
1. Declare exception frame variable
2. Generate setjmp guard: `if (setjmp(frame.jmpbuf) == 0)`
3. In try block: push frame onto stack before user code
4. In catch handlers: generate type check with `strcmp()`
5. Pop frame on both normal and exception paths
6. Call destructors from action table during unwinding

#### 2. Multiple Catch Handlers with Fallthrough

**C++**:
```cpp
void test_multiple() {
  try {
    throw std::runtime_error("oops");
  } catch (std::logic_error& e) {
    printf("Logic error\n");
  } catch (std::runtime_error& e) {
    printf("Runtime error\n");
  } catch (...) {
    printf("Unknown error\n");
  }
}
```

**C** (Generated):
```c
void test_multiple() {
  struct __cxx_exception_frame frame;
  frame.next = __cxx_exception_stack;
  // ... setup ...

  if (setjmp(frame.jmpbuf) == 0) {
    __cxx_exception_stack = &frame;

    struct runtime_error *__ex =
      (struct runtime_error*)malloc(sizeof(struct runtime_error));
    runtime_error__ctor(__ex, "oops");
    cxx_throw(__ex, "std::runtime_error");
  } else {
    // Type-based dispatch (if-else chain)
    if (strcmp(frame.exception_type, "std::logic_error") == 0) {
      struct logic_error *e = (struct logic_error*)frame.exception_object;
      printf("Logic error\n");
      logic_error__dtor(e);
      free(e);
    }
    else if (strcmp(frame.exception_type, "std::runtime_error") == 0) {
      struct runtime_error *e = (struct runtime_error*)frame.exception_object;
      printf("Runtime error\n");
      runtime_error__dtor(e);
      free(e);
    }
    else {
      // Catch-all handler (...)
      printf("Unknown error: %s\n", frame.exception_type);
      free(frame.exception_object);  // Generic cleanup
    }
    __cxx_exception_stack = frame.next;
  }
}
```

#### 3. Nested Try-Catch Blocks

**C++**:
```cpp
void test_nested() {
  try {
    try {
      throw Error(1);
    } catch (Error& e) {
      printf("Inner: %d\n", e.code);
      throw Error(2);  // Re-throw different exception
    }
  } catch (Error& e) {
    printf("Outer: %d\n", e.code);
  }
}
```

**C** (Generated):
```c
void test_nested() {
  // Outer frame
  struct __cxx_exception_frame frame_outer;
  frame_outer.next = __cxx_exception_stack;
  // ... setup ...

  if (setjmp(frame_outer.jmpbuf) == 0) {
    __cxx_exception_stack = &frame_outer;

    // Inner frame (nested)
    struct __cxx_exception_frame frame_inner;
    frame_inner.next = __cxx_exception_stack;  // Links to outer
    // ... setup ...

    if (setjmp(frame_inner.jmpbuf) == 0) {
      __cxx_exception_stack = &frame_inner;

      struct Error *__ex = (struct Error*)malloc(sizeof(struct Error));
      Error__ctor(__ex, 1);
      cxx_throw(__ex, "Error");  // Jump to inner handler
    } else {
      // Inner catch handler
      struct Error *e = (struct Error*)frame_inner.exception_object;
      printf("Inner: %d\n", e->code);
      Error__dtor(e);
      free(e);

      // Re-throw different exception
      struct Error *__ex2 = (struct Error*)malloc(sizeof(struct Error));
      Error__ctor(__ex2, 2);
      cxx_throw(__ex2, "Error");  // Jump to outer handler (frame_inner.next)
    }

    __cxx_exception_stack = frame_outer.next;
  } else {
    // Outer catch handler
    struct Error *e = (struct Error*)frame_outer.exception_object;
    printf("Outer: %d\n", e->code);
    Error__dtor(e);
    free(e);
    __cxx_exception_stack = frame_outer.next;
  }
}
```

**Key Points for Nested Blocks**:
- Each try-catch has its own frame
- Frames are linked: `frame_inner.next = &frame_outer`
- When exception thrown: longjmp to innermost matching handler
- If no match: longjmp skips to outer frame (automatic by `cxx_throw`)
- Exception propagates up the frame stack naturally

#### 4. Stack Unwinding with RAII (Destructor Calls)

**C++**:
```cpp
class Resource {
public:
  Resource() { printf("Resource acquired\n"); }
  ~Resource() { printf("Resource released\n"); }
};

void test_raii() {
  Resource r1;
  try {
    Resource r2;
    throw Error(99);
  } catch (Error& e) {
    printf("Caught: %d\n", e.code);
  }
  // r1 destroyed here normally
}
```

**C** (Generated):
```c
// Action table: destructors called during unwinding
// Entries in REVERSE construction order (LIFO: last constructed = first destroyed)
static struct __cxx_action_entry actions_table_0[] = {
  { Resource__dtor, NULL },  // r2 destructor (constructed last)
  { NULL, NULL }             // Sentinel
};

void test_raii() {
  struct Resource r1;
  Resource__ctor(&r1);

  struct __cxx_exception_frame frame;
  frame.next = __cxx_exception_stack;
  frame.actions = actions_table_0;

  if (setjmp(frame.jmpbuf) == 0) {
    __cxx_exception_stack = &frame;

    struct Resource r2;
    Resource__ctor(&r2);
    actions_table_0[0].object = &r2;  // Register r2 for unwinding

    struct Error *__ex = (struct Error*)malloc(sizeof(struct Error));
    Error__ctor(__ex, 99);
    cxx_throw(__ex, "Error");  // Exception thrown here
    // Control never reaches here (longjmp)

  } else {
    // cxx_throw has already called destructors from action table
    // r2's destructor was called during unwinding (prints "Resource released")

    struct Error *e = (struct Error*)frame.exception_object;
    printf("Caught: %d\n", e->code);
    Error__dtor(e);
    free(e);
    __cxx_exception_stack = frame.next;
  }

  // r1 destroyed here (normal RAII)
  Resource__dtor(&r1);
}

// Output:
// Resource acquired         (r1 constructor)
// Resource acquired         (r2 constructor)
// Resource released         (r2 destructor, called by cxx_throw during unwinding!)
// Caught: 99                (catch handler)
// Resource released         (r1 destructor)
```

**Critical Implementation Details**:

1. **Action Table Generation**: Create table of (destructor, object) pairs in reverse construction order
2. **Registration During Execution**: Update action table entries with actual object addresses as they're constructed
3. **Unwinding Phase in `cxx_throw()`**:
   ```c
   void cxx_throw(void *exception, const char *type_info) {
     struct __cxx_exception_frame *frame = __cxx_exception_stack;

     if (!frame) abort();  // Uncaught exception

     // Phase 1: Call destructors (LIFO)
     if (frame->actions) {
       for (int i = 0; frame->actions[i].destructor; i++) {
         frame->actions[i].destructor(frame->actions[i].object);
       }
     }

     // Phase 2: Store exception and longjmp to catch handler
     frame->exception_object = exception;
     frame->exception_type = type_info;

     // Unwind to this frame (don't pop yet, catch handler will)
     longjmp(frame->jmpbuf, 1);  // Returns 1 from setjmp
   }
   ```

#### 5. Uncaught Exception Propagation

**C++**:
```cpp
void inner() {
  throw Error(1);  // No handler in this function
}

void middle() {
  inner();  // Exception passes through
}

void outer() {
  try {
    middle();
  } catch (Error& e) {
    printf("Caught: %d\n", e.code);
  }
}
```

**C** (Generated):
```c
void inner() {
  struct Error *__ex = (struct Error*)malloc(sizeof(struct Error));
  Error__ctor(__ex, 1);
  cxx_throw(__ex, "Error");  // No setjmp here, so exception propagates
  // cxx_throw walks up __cxx_exception_stack to find outer frame
}

void middle() {
  inner();  // Exception automatically propagates (longjmp happens in cxx_throw)
  // This line is never reached
}

void outer() {
  struct __cxx_exception_frame frame;
  frame.next = __cxx_exception_stack;
  // ... setup ...

  if (setjmp(frame.jmpbuf) == 0) {
    __cxx_exception_stack = &frame;
    middle();  // Exception will longjmp back to here
    __cxx_exception_stack = frame.next;
  } else {
    // Exception caught here
    struct Error *e = (struct Error*)frame.exception_object;
    printf("Caught: %d\n", e->code);
    Error__dtor(e);
    free(e);
    __cxx_exception_stack = frame.next;
  }
}
```

**Key Point**: Exception propagates automatically through nested function calls without explicit `goto` or return statements—the frame stack in `__cxx_exception_stack` handles it.

### Visitor Method Implementation Strategy

#### VisitCXXTryStmt Implementation

```cpp
bool CppToCVisitor::VisitCXXTryStmt(CXXTryStmt *S) {
  // 1. Generate frame variable name
  std::string frameVarName = "frame_" + std::to_string(exceptionFrameCounter++);

  // 2. Generate action table name
  std::string actionsTableName = "actions_table_" + std::to_string(tryBlockCounter++);

  // 3. Use TryCatchTransformer to generate complete try-catch code
  TryCatchTransformer transformer;
  std::string transformedCode = transformer.transformTryCatch(S, frameVarName, actionsTableName);

  // 4. Store in output code
  currentFunctionCode += transformedCode;

  // 5. Return true to indicate we've handled this (don't recurse into children)
  return false;  // Prevent default traversal
}
```

#### VisitCXXThrowExpr Implementation

```cpp
bool CppToCVisitor::VisitCXXThrowExpr(CXXThrowExpr *E) {
  // 1. Use ThrowTranslator to generate throw code
  ThrowTranslator translator;
  std::string throwCode;

  if (E->getSubExpr()) {
    // throw expression;
    throwCode = translator.generateThrowCode(E);
  } else {
    // throw; (re-throw)
    throwCode = translator.generateRethrowCode();
  }

  // 2. Store in output code
  currentExpressionCode += throwCode;

  // 3. Return true to indicate we've handled this
  return true;
}
```

### Key Challenges & Solutions

#### Challenge 1: Stack Unwinding Simulation in C

**Problem**: C has no native exception mechanism. Stack unwinding must be simulated using setjmp/longjmp.

**Solution**:
- Use setjmp to capture execution state before try block
- longjmp in cxx_throw to jump to catch handler
- Action table tracks objects to destroy during unwinding
- Frame stack in thread-local storage links nested try blocks

#### Challenge 2: Exception Type Matching

**Problem**: C has no RTTI. How to match exception types in catch handlers?

**Solution**:
- Store type name as string in exception frame
- Use strcmp() to match against catch handler types
- Support polymorphic exception hierarchy by type name string matching
- Catch-all handler (`...`) matches any type

#### Challenge 3: RAII Integration During Unwinding

**Problem**: Destructors must be called during stack unwinding, but longjmp skips normal code.

**Solution**:
- Pre-register destructors in action table before throw
- cxx_throw walks action table and calls destructors before longjmp
- Destructors called in LIFO order (reverse construction)
- Works with nested try blocks (frame stack ensures correct scope)

#### Challenge 4: Nested Try-Catch Blocks

**Problem**: Multiple try blocks need independent exception frames.

**Solution**:
- Each try block gets unique frame variable (frame_0, frame_1, etc.)
- Frames are linked: `frame.next = previous_frame_on_stack`
- When cxx_throw called, it uses __cxx_exception_stack (frame pointer)
- longjmp automatically goes to nearest frame with matching handler
- If no match: cxx_throw will longjmp to frame.next (outer frame)

#### Challenge 5: Exception Object Lifetime

**Problem**: Exception object allocated in throw expression, must survive unwinding and be accessible in catch handler.

**Solution**:
- Allocate exception object on heap (malloc) in throw expression
- Pass to cxx_throw which stores in frame->exception_object
- Catch handler receives pointer to heap object
- Catch handler responsible for destruction and free
- If uncaught, could leak (acceptable for uncaught exceptions)

### Integration Points

1. **CppToCVisitor**: Add `VisitCXXTryStmt` and `VisitCXXThrowExpr` visitor methods
2. **Transformer Integration**: Call `TryCatchTransformer::transform()` and `ThrowTranslator::translate()`
3. **Runtime Linking**: Link `runtime/exception_runtime.cpp` into final executable
4. **Frame Management**: Generate frame variables and action tables automatically
5. **RAII Coordination**: Ensure destructors registered in action tables during execution

### Test Plan (15+ Tests)

#### Basic Functionality (4 tests)
1. **SingleHandler**: throw and catch matching exception type
2. **MultipleHandlers**: exception matched among several catch clauses
3. **CatchAll**: catch-all handler (`catch(...)`) matches any exception
4. **RethrowBasic**: `throw;` in catch handler re-throws same exception

#### Control Flow (3 tests)
5. **NestedTryCatch**: exception in inner try caught by outer handler
6. **ThroughFunctionCall**: exception thrown in function caught by caller
7. **PropagationUpStack**: exception skips multiple function calls to reach handler

#### RAII & Cleanup (4 tests)
8. **UnwindingWithDestructors**: destructors called in reverse order during unwinding
9. **UnwindingMultipleObjects**: multiple objects destroyed during unwinding
10. **NormalPathCleanup**: resources cleaned up on normal exit (no exception)

#### Exception Object Management (2 tests)
11. **ExceptionWithData**: exception object carries data to catch handler
12. **ExceptionConstructor**: exception constructed with parameters

#### Edge Cases (2 tests)
13. **UnmatchedException**: exception type doesn't match any handler (propagates up)
14. **ExceptionInDestructor**: exception thrown during unwinding (abort)

### Verification Criteria

- [ ] **Functional**: All 15+ tests passing (100%)
- [ ] **Correctness**: Exceptions caught by matching handlers only
- [ ] **RAII**: Stack unwinding calls destructors in correct (LIFO) order
- [ ] **Propagation**: Uncaught exceptions propagate to outer scopes
- [ ] **Performance**: <20% overhead vs. code without exceptions (measured via benchmark)
- [ ] **Linting**: Zero linting errors (clang-tidy, cppcheck)
- [ ] **Code Review**: Separate review by another agent

## Key Features

1. **Setjmp/Longjmp-Based Exception Handling**: Portable C implementation of C++ exceptions
2. **Action Table Destructors**: RAII support with destructor invocation during unwinding
3. **Type-Based Catch Matching**: String-based type matching for exception handlers
4. **Nested Try-Catch Support**: Frame stack allows arbitrary nesting depth
5. **Exception Re-Throw**: Support for `throw;` expressions in catch handlers
6. **Catch-All Handlers**: Support for `catch(...)` fallback handler
7. **Uncaught Exception Propagation**: Exceptions skip non-matching handlers automatically

## Dependencies

- **None** (independent phase)
- **Infrastructure present**: TryCatchTransformer.h, ThrowTranslator.h, exception_runtime.h
- **Infrastructure present**: Exception tests and benchmarks already written

## Implementation Milestones

### Milestone 1: Visitor Method Scaffolding (20% effort)
- [ ] Add `VisitCXXTryStmt` method stub to CppToCVisitor
- [ ] Add `VisitCXXThrowExpr` method stub to CppToCVisitor
- [ ] Integrate TryCatchTransformer and ThrowTranslator headers
- [ ] Verify project builds without errors

### Milestone 2: Basic Exception Handling (40% effort)
- [ ] Implement setjmp/longjmp guard generation in VisitCXXTryStmt
- [ ] Implement single catch handler matching
- [ ] Implement exception object allocation in VisitCXXThrowExpr
- [ ] Basic tests passing (4/15)

### Milestone 3: Advanced Exception Features (25% effort)
- [ ] Multiple catch handler dispatch
- [ ] Nested try-catch block support
- [ ] Exception re-throw implementation
- [ ] Catch-all handler support
- [ ] Advanced tests passing (12/15)

### Milestone 4: Integration & Optimization (15% effort)
- [ ] Runtime linking verification
- [ ] RAII destructor integration testing
- [ ] Performance benchmarking (<20% overhead)
- [ ] All tests passing (15+/15)
- [ ] Code review and linting

## Success Criteria Summary

| Criteria | Target | Status |
|----------|--------|--------|
| Tests Passing | 15+/15 (100%) | ⏳ PENDING |
| RAII Correct | Destructors in LIFO order | ⏳ PENDING |
| Exception Propagation | Uncaught → outer scope | ⏳ PENDING |
| Performance Impact | <20% vs. non-exception code | ⏳ PENDING |
| Linting Errors | 0 errors/warnings | ⏳ PENDING |
| Code Review | Approved by separate review | ⏳ PENDING |

## Next Steps

1. **Setup**: Verify infrastructure files exist and build
2. **Implement**: Follow milestones to implement visitor methods
3. **Test**: Run test suite after each milestone
4. **Document**: Write examples and update documentation
5. **Release**: Execute git-flow release v2.5.0

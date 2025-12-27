# Phase 57: Move Semantics Implementation Plan

**Phase**: 57 (Move Semantics)
**Status**: PLANNING
**Priority**: MEDIUM (performance optimization)
**Estimated Duration**: 50-80 hours
**Risk Level**: HIGH (ownership semantics complex)
**Dependencies**: Phase 42 (References), Phase 44 (Classes/Constructors)

---

## Executive Summary

Phase 57 implements **full production-grade support for C++11 move semantics**, including rvalue references, move constructors/assignment, `std::move()`, and perfect forwarding. While exploratory work exists from earlier phases, this phase will **productionize, refactor, and complete** the implementation following SOLID principles and the new handler architecture.

**Current Status**: 35% complete (exploratory prototypes exist)
- ✅ Basic move constructor detection (MoveConstructorTranslator)
- ✅ Basic move assignment detection (MoveAssignmentTranslator)
- ✅ Basic `std::move()` translation (StdMoveTranslator)
- ✅ Rvalue reference parameter handling (RvalueRefParamTranslator)
- ❌ NOT production-ready (violates SOLID, lacks comprehensive tests)
- ❌ NOT integrated with handler architecture
- ❌ Incomplete perfect forwarding support
- ❌ Missing safety validations (use-after-move, double-free)

**Gap Analysis**: This phase will bridge prototype → production quality.

---

## Objective

**Complete production-grade move semantics support** with:

1. **Correctness**: Zero double-free bugs, use-after-move safety
2. **Performance**: Efficient resource transfer (O(1) moves vs O(n) copies)
3. **Architecture**: SOLID-compliant handler integration
4. **Testing**: 100% test coverage (unit, integration, E2E)
5. **Documentation**: User guide, troubleshooting, best practices

---

## Context

### Why Move Semantics Are Complex

Move semantics introduce **ownership transfer semantics** that don't exist in C:

1. **Resource Ownership Tracking**
   - After move, source object must be in "valid but unspecified" state
   - Pointers must be nullified to prevent double-free
   - Moved-from objects can still be destroyed safely

2. **Value Category Preservation**
   - Lvalues (named objects) vs rvalues (temporaries)
   - Perfect forwarding preserves value categories across function calls
   - Template argument deduction rules (`T&&` is universal reference)

3. **Overload Resolution Complexity**
   - Copy constructor vs move constructor selection
   - Implicit vs explicit moves (`std::move()`)
   - Move-only types (deleted copy operations)

4. **Exception Safety**
   - `noexcept` guarantees enable optimizations
   - Strong exception safety requires rollback on failure
   - Move operations should be non-throwing when possible

### Current C Limitations

C has no native concept of move semantics:
- No rvalue references → must track via conventions
- No compile-time value category tracking → runtime checks needed
- No automated moved-from state validation → manual nullification

### Translation Challenges

**Challenge 1: Rvalue References in C**
```cpp
// C++ Input
void process(Widget&& w) { /* ... */ }
```
```c
// C Output - how to represent rvalue-ness?
// Option 1: Same as lvalue ref (loses semantics)
void process(Widget* w) { /* ... */ }

// Option 2: Flag parameter (runtime overhead)
void process(Widget* w, int is_rvalue) { /* ... */ }

// Option 3: Naming convention (adopted)
void process_rvalue(Widget* w) { /* ... */ }
```

**Challenge 2: Moved-From State**
```cpp
// C++ Move Constructor
Widget(Widget&& other) : data(other.data) {
    other.data = nullptr;  // Nullify source
}
```
```c
// C Translation - must manually nullify
void Widget_move_construct(Widget* this, Widget* other) {
    this->data = other->data;
    other->data = NULL;  // CRITICAL: prevent double-free
}
```

**Challenge 3: Perfect Forwarding**
```cpp
// C++ Universal Reference
template<typename T>
void wrapper(T&& arg) {
    process(std::forward<T>(arg));
}
```
```c
// C Translation - must monomorphize per value category
void wrapper_int_lvalue(int* arg) {
    process_lvalue(arg);
}
void wrapper_int_rvalue(int* arg) {
    process_rvalue(arg);
}
```

### Existing Prototype Limitations

The existing move semantics code has architectural issues:

**Issue 1: Violates Single Responsibility Principle**
- `MoveConstructorTranslator` handles detection, translation, AND code generation
- Should separate concerns: detection → transformation → emission

**Issue 2: Not Integrated with Handler Architecture**
- Exists as standalone translators, not handlers
- Doesn't follow visitor pattern like ExpressionHandler, StatementHandler
- No coordination with ConstructorHandler

**Issue 3: Incomplete Testing**
- Test files exist but many are outdated (`_old` suffix)
- No systematic test coverage (missing edge cases)
- No E2E validation

**Issue 4: Missing Safety Features**
- No use-after-move detection
- No self-move assignment protection verification
- No double-free prevention validation

---

## Translation Strategy

### High-Level Approach

**3-Stage Pipeline** (consistent with transpiler architecture):

1. **Stage 1: C++ AST → Semantic Analysis**
   - Detect rvalue references, move constructors, move assignments
   - Identify `std::move()` calls and perfect forwarding
   - Analyze value categories (lvalue vs rvalue)

2. **Stage 2: Semantic Model → C AST**
   - Transform rvalue references to C pointer types
   - Create move constructor/assignment C functions
   - Replace `std::move()` with move constructor calls
   - Monomorphize perfect forwarding templates

3. **Stage 3: C AST → C Code Emission**
   - Emit move functions with proper nullification
   - Generate self-assignment checks
   - Add comments documenting ownership transfer

### Detailed Translation Patterns

#### Pattern 1: Rvalue Reference Types

**C++ Input:**
```cpp
void process(Widget&& w);
```

**Translation:**
```c
// C Declaration
void process_rvalue(Widget* w);
```

**Naming Convention:**
- Rvalue ref parameters → `_rvalue` suffix on function name
- OR separate overload: `process_move(Widget* w)`

#### Pattern 2: Move Constructor

**C++ Input:**
```cpp
class Widget {
    char* data;
public:
    Widget(Widget&& other) : data(other.data) {
        other.data = nullptr;
    }
};
```

**Translation:**
```c
// C Header (.h)
struct Widget {
    char* data;
};
void Widget_move_construct(Widget* this, Widget* other);

// C Implementation (.c)
void Widget_move_construct(Widget* this, Widget* other) {
    // Transfer ownership
    this->data = other->data;

    // CRITICAL: Nullify source to prevent double-free
    other->data = NULL;

    // Moved-from object is now in valid but unspecified state
    // Can be safely destroyed: Widget_destruct(other) will free(NULL) safely
}
```

**Safety Invariants:**
1. After move, source object is destructible
2. All pointer members nullified
3. All resource handles invalidated (-1 for fds, NULL for pointers)
4. Primitive members can have any value (unspecified)

#### Pattern 3: Move Assignment Operator

**C++ Input:**
```cpp
Widget& operator=(Widget&& other) {
    if (this != &other) {
        delete[] data;
        data = other.data;
        other.data = nullptr;
    }
    return *this;
}
```

**Translation:**
```c
Widget* Widget_move_assign(Widget* this, Widget* other) {
    // Self-assignment check (CRITICAL for safety)
    if (this != other) {
        // Clean up existing resources
        free(this->data);

        // Transfer ownership
        this->data = other->data;

        // Nullify source
        other->data = NULL;
    }
    return this;
}
```

**Safety Invariants:**
1. Self-assignment safe (`if (this != other)`)
2. Existing resources cleaned up before transfer
3. Source nullified after transfer
4. Returns `this` for chaining

#### Pattern 4: std::move() Calls

**C++ Input:**
```cpp
Widget w1;
Widget w2 = std::move(w1);
```

**Translation:**
```c
Widget w1;
Widget_construct(&w1);

Widget w2;
Widget_move_construct(&w2, &w1);

// w1 is now in moved-from state (data == NULL)
// Using w1 is legal but unpredictable
```

**Detection Strategy:**
1. Identify `std::move()` calls in AST (CallExpr to `std::move`)
2. Determine if used in constructor or assignment context
3. Replace with move constructor/assignment call
4. Add comment: `/* w1 moved from */`

#### Pattern 5: Perfect Forwarding (Template Monomorphization)

**C++ Input:**
```cpp
template<typename T>
void wrapper(T&& arg) {
    process(std::forward<T>(arg));
}

void use() {
    int x = 5;
    wrapper(x);           // T = int&, arg is lvalue
    wrapper(10);          // T = int, arg is rvalue
}
```

**Translation (Monomorphized):**
```c
// Monomorphization 1: T = int& (lvalue)
void wrapper_int_ref(int* arg) {
    process_lvalue(arg);  // Forward as lvalue
}

// Monomorphization 2: T = int (rvalue)
void wrapper_int(int* arg) {
    process_rvalue(arg);  // Forward as rvalue
}

// Call sites
void use() {
    int x = 5;
    wrapper_int_ref(&x);   // Lvalue forwarding

    int temp = 10;
    wrapper_int(&temp);    // Rvalue forwarding
}
```

**Forwarding Rules:**
- Lvalue arg → forward as lvalue (no move)
- Rvalue arg → forward as rvalue (enable move)
- Preserve value category through template instantiation

#### Pattern 6: Move-Only Types

**C++ Input:**
```cpp
class UniquePtr {
    int* ptr;
public:
    UniquePtr(UniquePtr&& other) : ptr(other.ptr) {
        other.ptr = nullptr;
    }

    // Delete copy operations
    UniquePtr(const UniquePtr&) = delete;
    UniquePtr& operator=(const UniquePtr&) = delete;
};
```

**Translation:**
```c
struct UniquePtr {
    int* ptr;
};

// Move constructor exists
void UniquePtr_move_construct(UniquePtr* this, UniquePtr* other) {
    this->ptr = other->ptr;
    other->ptr = NULL;
}

// Copy constructor NOT generated (deleted)
// Attempting to copy would fail at C++ level (compilation error)
// At C level, user must not call non-existent UniquePtr_copy_construct
```

**Enforcement:**
- C++ compiler rejects copy attempts
- C code relies on developer discipline
- Add `/* MOVE-ONLY TYPE */` comment in header

---

## Architecture Refactoring

### Current State (Prototype)

```
CppToCVisitor
  └─> MoveConstructorTranslator (standalone)
  └─> MoveAssignmentTranslator (standalone)
  └─> StdMoveTranslator (standalone)
  └─> RvalueRefParamTranslator (standalone)
```

**Problems:**
- Tight coupling to CppToCVisitor
- Each translator duplicates detection logic
- No shared infrastructure for moved-from state tracking

### Target State (SOLID Architecture)

```
TranslationOrchestrator
  │
  ├─> ConstructorHandler
  │     ├─> handleConstructor()
  │     └─> handleMoveConstructor()  ← NEW
  │
  ├─> ExpressionHandler
  │     ├─> handleCallExpr()
  │     └─> handleStdMove()  ← NEW
  │
  ├─> MoveSemanticValidator  ← NEW
  │     ├─> validateMovedFromState()
  │     ├─> validateSelfMoveAssignment()
  │     └─> detectUseAfterMove()
  │
  └─> PerfectForwardingHandler  ← NEW
        ├─> analyzeForwardingContext()
        └─> monomorphizeForwardingCall()
```

**Benefits:**
1. **Single Responsibility**: Each handler has one job
2. **Open/Closed**: Extend via new handlers, not modifying existing
3. **Dependency Inversion**: Handlers depend on abstractions (CNodeBuilder)
4. **Testability**: Unit test handlers independently

### Refactoring Strategy

**Phase 1: Extract Move Constructor Handling** (8-12 hrs)
- Move `MoveConstructorTranslator` logic into `ConstructorHandler::handleMoveConstructor()`
- Consolidate with existing copy constructor logic
- Ensure overload resolution works (copy vs move)

**Phase 2: Integrate Move Assignment** (8-12 hrs)
- Add `MethodHandler::handleMoveAssignment()`
- Coordinate with `operator=` translation
- Validate self-assignment protection

**Phase 3: Refactor std::move() Translation** (6-8 hrs)
- Move `StdMoveTranslator` logic into `ExpressionHandler::handleStdMove()`
- Detect `std::move()` in CallExpr visitor
- Replace with move constructor/assignment calls

**Phase 4: Extract Perfect Forwarding** (10-15 hrs)
- Create `PerfectForwardingHandler` class
- Integrate with TemplateMonomorphizer
- Handle `std::forward<T>()` detection and translation

**Phase 5: Add Safety Validation** (8-12 hrs)
- Create `MoveSemanticValidator` class
- Add moved-from state tracking
- Validate nullification patterns
- Detect use-after-move bugs (optional warning)

---

## Task Breakdown (TDD Approach)

### Group 1: Refactor Existing Prototypes (Sequential)

**Task 1.1: Audit Existing Code** (4 hrs)
- Review all `include/Move*.h` and `src/Move*.cpp` files
- Document what works, what's broken
- Identify SOLID violations
- Map to target architecture

**Task 1.2: Extract Move Constructor Handler** (8 hrs)
- **TDD Steps**:
  1. Write failing test: `ConstructorHandlerTest::MoveConstructor`
  2. Move logic from `MoveConstructorTranslator` to `ConstructorHandler`
  3. Test copy vs move overload resolution
  4. Validate nullification patterns
  5. Refactor while keeping tests green

**Task 1.3: Extract Move Assignment Handler** (8 hrs)
- **TDD Steps**:
  1. Write failing test: `MethodHandlerTest::MoveAssignmentOperator`
  2. Move logic from `MoveAssignmentTranslator` to `MethodHandler`
  3. Test self-assignment protection
  4. Validate resource cleanup + transfer
  5. Refactor for clarity

**Task 1.4: Integrate std::move() into ExpressionHandler** (6 hrs)
- **TDD Steps**:
  1. Write failing test: `ExpressionHandlerTest::StdMoveCall`
  2. Detect `std::move()` in `handleCallExpr()`
  3. Replace with move constructor/assignment
  4. Test with various contexts (constructor, assignment, return)
  5. Validate moved-from state

### Group 2: Perfect Forwarding (Sequential, depends on Group 1)

**Task 2.1: Create PerfectForwardingHandler** (10 hrs)
- **TDD Steps**:
  1. Write test: `PerfectForwardingHandlerTest::BasicForwarding`
  2. Detect universal references (`T&&` in templates)
  3. Analyze `std::forward<T>()` calls
  4. Determine value category (lvalue vs rvalue)
  5. Monomorphize forwarding function per value category

**Task 2.2: Integrate with TemplateMonomorphizer** (8 hrs)
- **TDD Steps**:
  1. Write test: `TemplateMonomorphizerTest::ForwardingIntegration`
  2. Coordinate template instantiation with forwarding analysis
  3. Generate separate monomorphizations for lvalue/rvalue
  4. Test with variadic templates (`Args&&...`)
  5. Validate correct call site selection

**Task 2.3: Handle Edge Cases** (6 hrs)
- **Test Cases**:
  - Nested forwarding (forwarding through multiple wrappers)
  - Forwarding with move-only types
  - Forwarding with const references
  - Mixed lvalue/rvalue parameter packs

### Group 3: Safety Validation (Parallel with Group 2)

**Task 3.1: Create MoveSemanticValidator** (8 hrs)
- **TDD Steps**:
  1. Write test: `MoveSemanticValidatorTest::NullificationCheck`
  2. Implement AST walker to find move constructors
  3. Verify all pointer members nullified
  4. Verify all resource handles invalidated
  5. Emit warnings for missing nullification

**Task 3.2: Self-Assignment Protection** (4 hrs)
- **TDD Steps**:
  1. Write test: `MoveSemanticValidatorTest::SelfMoveAssignment`
  2. Check for `if (this != other)` in move assignment
  3. Validate pattern coverage
  4. Emit warnings for missing checks

**Task 3.3: Use-After-Move Detection (Optional)** (6 hrs)
- **TDD Steps**:
  1. Write test: `MoveSemanticValidatorTest::UseAfterMove`
  2. Track moved-from variables in scope
  3. Detect subsequent usage (DeclRefExpr)
  4. Emit warning: "variable 'x' used after move"
  5. Handle moved-from reset (reassignment)

### Group 4: Comprehensive Testing (Sequential, final stage)

**Task 4.1: Unit Tests** (12 hrs)
- **Coverage**:
  - `ConstructorHandlerTest`: Move constructor (15 tests)
  - `MethodHandlerTest`: Move assignment (12 tests)
  - `ExpressionHandlerTest`: `std::move()` (10 tests)
  - `PerfectForwardingHandlerTest`: Forwarding (15 tests)
  - `MoveSemanticValidatorTest`: Safety (10 tests)
- **Total**: 62 unit tests

**Task 4.2: Integration Tests** (10 hrs)
- **File**: `tests/integration/handlers/MoveSemanticsIntegrationTest.cpp`
- **Tests** (20 tests):
  - Unique pointer-like ownership transfer
  - Vector-like container move
  - Move-only types (FileHandle, Socket)
  - Member-wise moves (composite objects)
  - Move with inheritance (base class move)
  - Rvalue reference parameters
  - Perfect forwarding scenarios
  - Self-move assignment safety
  - Use-after-move scenarios
  - Exception safety (if applicable)

**Task 4.3: E2E Tests** (8 hrs)
- **File**: `tests/e2e/phase57/MoveSemanticsE2ETest.cpp`
- **Tests** (10 tests):
  - 1 active sanity test (UniquePtr transfer)
  - 9 disabled real-world tests:
    - Resource manager with move semantics
    - Container with move operations
    - Factory returning move-only type
    - Move-based swap implementation
    - Perfect forwarding factory (make_unique)
    - Move semantics with exceptions
    - Move-only network socket wrapper
    - String class with move optimization
    - Smart pointer array (unique_ptr<T[]>)

**Task 4.4: Regression Testing** (4 hrs)
- Run all existing tests to ensure no breakage
- Fix any regressions introduced by refactoring
- Verify 100% pass rate maintained

---

## Execution Strategy

### Timeline

**Week 1: Refactoring Foundation** (Group 1)
- Day 1-2: Audit existing code (Task 1.1)
- Day 3-4: Extract move constructor handler (Task 1.2)
- Day 5-6: Extract move assignment handler (Task 1.3)
- Day 7: Integrate std::move() (Task 1.4)

**Week 2: Perfect Forwarding** (Group 2)
- Day 1-3: Create PerfectForwardingHandler (Task 2.1)
- Day 4-5: Integrate with TemplateMonomorphizer (Task 2.2)
- Day 6-7: Handle edge cases (Task 2.3)

**Week 3: Safety & Validation** (Group 3, parallel)
- Day 1-3: Create MoveSemanticValidator (Task 3.1)
- Day 4: Self-assignment protection (Task 3.2)
- Day 5-7: Use-after-move detection (Task 3.3, optional)

**Week 4: Comprehensive Testing** (Group 4)
- Day 1-3: Unit tests (Task 4.1)
- Day 4-5: Integration tests (Task 4.2)
- Day 6-7: E2E tests (Task 4.3)

**Week 5: Finalization**
- Day 1-2: Regression testing (Task 4.4)
- Day 3-4: Documentation (user guide, troubleshooting)
- Day 5: Code review, polish
- Day 6-7: Buffer for unexpected issues

**Total: 50-80 hours (5 weeks at 10-16 hrs/week)**

### Parallelization Opportunities

**Parallel Execution Groups:**

1. **Week 3**: Group 2 (Perfect Forwarding) + Group 3 (Safety) can run in parallel
   - Different codebases (PerfectForwardingHandler vs MoveSemanticValidator)
   - No shared dependencies
   - ~50% time savings

2. **Unit Tests**: Tests for different handlers can be written in parallel
   - ConstructorHandlerTest, MethodHandlerTest, ExpressionHandlerTest independent
   - ~30% time savings on testing

**Resource Allocation:**
- Week 1-2: 1 engineer (sequential refactoring)
- Week 3: 2 engineers (parallel forwarding + validation)
- Week 4: 1-2 engineers (testing)
- Week 5: 1 engineer (finalization)

### Deviation Rules

1. **Use-After-Move Detection Fails**: Make optional (warning only)
2. **Perfect Forwarding Too Complex**: Defer variadic templates to Phase 59
3. **Performance Regression**: Document acceptable overhead (<5%)
4. **Test Failures**: Fix root cause, don't skip tests

---

## Success Criteria

### Functional Requirements

- [ ] Move constructors correctly translated to C functions
- [ ] Move assignment operators correctly translated
- [ ] `std::move()` calls replaced with move constructor/assignment
- [ ] Perfect forwarding works for simple cases (single param)
- [ ] Rvalue reference parameters handled
- [ ] Move-only types supported
- [ ] Self-assignment protection validated
- [ ] Moved-from state properly nullified

### Quality Requirements

- [ ] All unit tests pass (62 tests, 100%)
- [ ] All integration tests pass (20 tests, 100%)
- [ ] 1 E2E sanity test passes (100%)
- [ ] No regressions in existing tests
- [ ] Code follows SOLID principles
- [ ] TDD followed throughout
- [ ] No compiler warnings
- [ ] Valgrind clean (no memory leaks)

### Performance Requirements

- [ ] Move operations are O(1) (constant time)
- [ ] Transpiler overhead < 5% vs hand-written C
- [ ] Large container moves avoid O(n) copies
- [ ] No unnecessary copies introduced

### Documentation Requirements

- [ ] User guide updated (move semantics section)
- [ ] API documentation (handler methods)
- [ ] Architecture document (refactoring rationale)
- [ ] Test coverage report
- [ ] Performance benchmarks (move vs copy)

---

## Risk Analysis & Mitigation

### Risk 1: Refactoring Breaks Existing Code (HIGH)

**Impact**: Regressions in copy semantics, constructor translation
**Probability**: MEDIUM
**Mitigation**:
- Run full test suite after each refactoring step
- Incremental refactoring (one handler at a time)
- Keep old code until new code passes all tests
- Comprehensive regression testing

### Risk 2: Perfect Forwarding Complexity (HIGH)

**Impact**: Incorrect value category preservation, wrong overload selection
**Probability**: HIGH
**Mitigation**:
- Start with simple cases (single parameter)
- Defer variadic templates to Phase 59
- Extensive test coverage for lvalue/rvalue scenarios
- Document limitations clearly

### Risk 3: Use-After-Move False Positives (MEDIUM)

**Impact**: Too many warnings, user fatigue
**Probability**: MEDIUM
**Mitigation**:
- Make detection optional (flag-controlled)
- Conservative analysis (few false positives)
- Clear diagnostic messages
- Allow suppression annotations

### Risk 4: Timeline Overrun (MEDIUM)

**Impact**: Phase extends beyond 80 hours
**Probability**: MEDIUM
**Mitigation**:
- Buffer week (Week 5) for overruns
- Defer optional features (use-after-move)
- Prioritize correctness over optimization
- Track progress weekly

### Risk 5: Self-Move Assignment Edge Cases (MEDIUM)

**Impact**: Self-move causes resource leak or corruption
**Probability**: LOW
**Mitigation**:
- Always generate `if (this != other)` check
- Validate pattern in MoveSemanticValidator
- Test self-move explicitly
- Document requirement

---

## Performance Benchmarks

### Expected Performance Characteristics

| Scenario | Copy (C++) | Move (C++) | Transpiled Move | Overhead |
|----------|-----------|-----------|-----------------|----------|
| Small object (<64B) | 5 ns | 2 ns | 2.2 ns | 10% |
| std::string (short) | 10 ns | 2 ns | 2.2 ns | 10% |
| std::string (1KB) | 200 ns | 2 ns | 2.2 ns | 10% |
| std::vector (100 int) | 150 ns | 2 ns | 2.2 ns | 10% |
| std::vector (1M int) | 2 ms | 2 ns | 2.2 ns | 10% |
| Custom resource | Varies | ~2 ns | 2.2 ns | 10% |

**Key Insight**: Move semantics provide 10-1000x speedup vs copy, transpiler overhead negligible.

### Measurement Plan

**Benchmark Suite** (tests/benchmarks/move_semantics_benchmark.cpp):
1. Small object move (POD struct)
2. Large string move (1KB heap-allocated)
3. Vector move (1M integers)
4. Unique pointer move
5. Composite object move (multiple members)

**Metrics**:
- Move time (ns)
- Memory allocations (should be 0)
- Memcpy calls (should be 0)
- Destructor calls (verify moved-from state safe)

**Tools**:
- Google Benchmark framework
- Valgrind (callgrind) for profiling
- perf for low-level CPU metrics

---

## Test Strategy

### Unit Test Coverage

**ConstructorHandlerTest.cpp** (~15 tests):
- Move constructor detection
- Move constructor with single member (pointer)
- Move constructor with multiple members
- Move constructor with base class
- Move constructor `noexcept` specification
- Compiler-generated move constructor
- Deleted move constructor
- Move constructor with const members (should delete move)
- Move constructor with reference members (should delete move)
- Move constructor exception safety
- Move constructor overload resolution (copy vs move)

**MethodHandlerTest.cpp** (~12 tests):
- Move assignment detection
- Move assignment with resource cleanup
- Move assignment self-assignment protection
- Move assignment with base class
- Move assignment `noexcept`
- Compiler-generated move assignment
- Deleted move assignment
- Move assignment overload resolution
- Move assignment return value (`*this`)
- Move assignment exception safety

**ExpressionHandlerTest.cpp** (~10 tests):
- `std::move()` detection in variable init
- `std::move()` in function call
- `std::move()` in return statement
- `std::move()` in constructor member init
- `std::move()` with temporary (redundant)
- `std::move()` on const object (no-op)
- Nested `std::move()` calls
- `std::move()` with member access

**PerfectForwardingHandlerTest.cpp** (~15 tests):
- Universal reference detection (`T&&`)
- `std::forward<T>()` detection
- Lvalue forwarding (preserves lvalue)
- Rvalue forwarding (preserves rvalue)
- Forwarding to constructor
- Forwarding to function
- Const lvalue forwarding
- Const rvalue forwarding
- Reference collapsing (`T& && → T&`)
- Variadic forwarding (simple case)
- Forwarding with move-only types

**MoveSemanticValidatorTest.cpp** (~10 tests):
- Nullification validation (pointer members)
- Resource invalidation (file descriptors)
- Self-assignment check presence
- Self-assignment check correctness
- Use-after-move detection (basic)
- Use-after-move reset (reassignment)
- Double-free prevention validation
- Moved-from state consistency

### Integration Test Coverage

**MoveSemanticsIntegrationTest.cpp** (~20 tests):
1. UniquePtr-like ownership transfer
2. SharedPtr-like reference counting (if implemented)
3. Vector-like move construction
4. Vector-like move assignment
5. String-like move optimization
6. FileHandle move-only type
7. Socket move-only type
8. Database connection move
9. Member-wise move (composite object)
10. Move with single inheritance
11. Move with multiple inheritance
12. Rvalue reference parameter in function
13. Rvalue reference parameter in method
14. Perfect forwarding (simple)
15. Perfect forwarding (factory pattern)
16. Self-move assignment safety
17. Move in return statement (RVO interaction)
18. Move in conditional expression
19. Move in loop (repeated moves)
20. Exception safety (if implemented)

### E2E Test Coverage

**MoveSemanticsE2ETest.cpp** (~10 tests):
- **ACTIVE**: UniquePtr ownership transfer (sanity check)
- **DISABLED**: ResourceManager with RAII + move
- **DISABLED**: Container with move operations (std::vector equivalent)
- **DISABLED**: Factory returning move-only type
- **DISABLED**: Move-based swap implementation
- **DISABLED**: Perfect forwarding factory (make_unique)
- **DISABLED**: Network socket wrapper (move-only)
- **DISABLED**: Custom string class with move optimization
- **DISABLED**: Smart pointer array (unique_ptr<T[]> equivalent)
- **DISABLED**: Database transaction with move semantics

**E2E Test Requirements**:
- Each test must compile to C
- Each test must run without errors
- Each test must not leak memory (Valgrind clean)
- Each test must demonstrate performance improvement (move > copy)

---

## Documentation Deliverables

### 1. User Guide: Move Semantics

**File**: `docs/features/MOVE-SEMANTICS.md`

**Contents**:
- What are move semantics?
- How move semantics map to C
- Supported features (constructors, assignment, std::move, forwarding)
- Usage examples (UniquePtr, Vector, FileHandle)
- Performance characteristics
- Best practices (when to use move, pitfalls)
- Troubleshooting (move not called, double-free, use-after-move)

### 2. API Documentation

**Files**:
- `docs/api/ConstructorHandler.md` (handleMoveConstructor section)
- `docs/api/MethodHandler.md` (handleMoveAssignment section)
- `docs/api/ExpressionHandler.md` (handleStdMove section)
- `docs/api/PerfectForwardingHandler.md` (new file)
- `docs/api/MoveSemanticValidator.md` (new file)

### 3. Architecture Document

**File**: `docs/architecture/MOVE-SEMANTICS-REFACTORING.md`

**Contents**:
- Previous architecture (prototype)
- Target architecture (SOLID handlers)
- Refactoring rationale
- Component responsibilities
- Integration points
- Testing strategy

### 4. Test Coverage Report

**File**: `.planning/phases/57-move-semantics/TEST-COVERAGE.md`

**Contents**:
- Unit test summary (62 tests)
- Integration test summary (20 tests)
- E2E test summary (10 tests, 1 active)
- Coverage percentage (lines, branches)
- Untested edge cases (if any)

### 5. Performance Benchmark Report

**File**: `.planning/phases/57-move-semantics/PERFORMANCE-BENCHMARKS.md`

**Contents**:
- Benchmark methodology
- Move vs copy timings
- Transpiler overhead measurements
- Memory allocation counts
- Comparison to hand-written C
- Optimization recommendations

---

## Dependencies

### Phase Dependencies

**Required (Must Complete First)**:
- ✅ Phase 42: Pointers & References (complete)
- ✅ Phase 44: Classes (Simple) (complete)
- ✅ Constructors & Destructors (part of Phase 44)

**Optional (Enhances Functionality)**:
- Phase 11: Templates (for perfect forwarding monomorphization)
- Phase 50: Operator Overloading (for move assignment operator=)

### External Dependencies

**Tooling**:
- Clang/LLVM AST API (rvalue reference detection)
- Google Test (unit/integration tests)
- Google Benchmark (performance tests)
- Valgrind (memory leak detection)
- CMake build system

**Transpiler Components**:
- CNodeBuilder (C AST creation)
- TemplateMonomorphizer (perfect forwarding)
- NameMangler (move constructor naming)
- ExpressionHandler (std::move detection)
- ConstructorHandler (move constructor integration)
- MethodHandler (move assignment integration)

---

## Deliverables Checklist

### Code Deliverables

- [ ] `include/handlers/ConstructorHandler.h` - handleMoveConstructor method
- [ ] `src/handlers/ConstructorHandler.cpp` - implementation
- [ ] `include/handlers/MethodHandler.h` - handleMoveAssignment method
- [ ] `src/handlers/MethodHandler.cpp` - implementation
- [ ] `include/handlers/ExpressionHandler.h` - handleStdMove method
- [ ] `src/handlers/ExpressionHandler.cpp` - implementation
- [ ] `include/handlers/PerfectForwardingHandler.h` - new file
- [ ] `src/handlers/PerfectForwardingHandler.cpp` - new file
- [ ] `include/validation/MoveSemanticValidator.h` - new file
- [ ] `src/validation/MoveSemanticValidator.cpp` - new file

### Test Deliverables

- [ ] `tests/unit/handlers/ConstructorHandlerTest.cpp` - move tests added
- [ ] `tests/unit/handlers/MethodHandlerTest.cpp` - move tests added
- [ ] `tests/unit/handlers/ExpressionHandlerTest.cpp` - std::move tests
- [ ] `tests/unit/handlers/PerfectForwardingHandlerTest.cpp` - new file
- [ ] `tests/unit/validation/MoveSemanticValidatorTest.cpp` - new file
- [ ] `tests/integration/handlers/MoveSemanticsIntegrationTest.cpp` - new file
- [ ] `tests/e2e/phase57/MoveSemanticsE2ETest.cpp` - new file
- [ ] `tests/benchmarks/move_semantics_benchmark.cpp` - new file

### Documentation Deliverables

- [ ] `docs/features/MOVE-SEMANTICS.md` - user guide
- [ ] `docs/api/PerfectForwardingHandler.md` - API docs
- [ ] `docs/api/MoveSemanticValidator.md` - API docs
- [ ] `docs/architecture/MOVE-SEMANTICS-REFACTORING.md` - architecture
- [ ] `.planning/phases/57-move-semantics/PHASE57-PLAN.md` - this file
- [ ] `.planning/phases/57-move-semantics/PHASE57-SUMMARY.md` - execution summary
- [ ] `.planning/phases/57-move-semantics/TEST-COVERAGE.md` - test report
- [ ] `.planning/phases/57-move-semantics/PERFORMANCE-BENCHMARKS.md` - perf report

### Build Configuration

- [ ] `CMakeLists.txt` - add new test executables
- [ ] `CMakeLists.txt` - add new handler sources
- [ ] `.github/workflows/ci.yml` - add benchmark job (optional)

---

## Next Steps After Completion

**Phase 58: constexpr/consteval** - Compile-time evaluation (80-120 hrs)
- Move semantics enable efficient runtime operations
- constexpr enables compile-time operations
- Natural progression: runtime → compile-time optimization

**Phase 59: Variadic Templates** - Extended template support (60-90 hrs)
- Perfect forwarding with variadic templates (`Args&&...`)
- Enables advanced factory patterns
- Builds on Phase 57 forwarding infrastructure

**Alternative Path: Phase 50-52 (Operator Overloading)** - Complete operator support
- Move assignment is an operator
- Coordinate with general operator overloading
- May be higher priority for users

---

## Notes & Lessons Learned

### From Existing Prototype

**What Worked Well**:
- Basic move constructor/assignment detection functional
- `std::move()` translation pattern correct
- Naming conventions (`_move_construct`) clear

**What Needs Improvement**:
- Architecture violates SOLID (tight coupling)
- Testing incomplete (many `_old` test files)
- No safety validation (nullification, self-assignment)
- Perfect forwarding support minimal

### Key Insights

1. **Move Semantics ≠ Simple Feature**: Ownership transfer semantics are complex
2. **Safety Critical**: Double-free bugs are catastrophic, must validate
3. **C Limitations**: No compile-time value category tracking, need runtime conventions
4. **Refactoring Essential**: Prototype → production requires architectural overhaul

### Recommendations for Future Phases

1. **Start with Architecture**: Design SOLID structure before implementation
2. **TDD from Day 1**: Tests guide design, prevent regressions
3. **Incremental Integration**: One handler at a time, validate continuously
4. **Document Limitations**: C can't match all C++ semantics, be explicit

---

## Approval & Sign-Off

**Plan Status**: READY FOR REVIEW
**Estimated Effort**: 50-80 hours
**Recommended Team Size**: 1-2 engineers
**Timeline**: 5 weeks at 10-16 hrs/week

**Next Action**: Obtain approval and begin Week 1 (Refactoring Foundation)

---

**END OF PHASE 57 PLAN**

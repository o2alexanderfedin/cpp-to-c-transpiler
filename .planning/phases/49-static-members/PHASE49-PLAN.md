# Phase 49 Plan: Static Data Members

**Phase**: 49 (Static Data Members)
**Prerequisite**: None (name mangling exists)
**Status**: PLANNING
**Target**: Complete static data member support with global variable translation

## Phase Goal

Implement full static data member support by translating C++ static data members to C global variables with mangled names. Bridge the gap from 35% completion (static methods work) to 100% (static data members work too).

## Current State Analysis

### What Works (35%)
- **Static methods**: Fully supported, translated to regular C functions with mangled names
- **Name mangling infrastructure**: `NameMangler` exists and works
- **Class structure**: RecordHandler processes classes correctly
- **Method calls**: Static method calls work through ExpressionHandler

### What's Missing (65%)
1. **Static data member detection**: RecordHandler doesn't identify static members
2. **Global variable generation**: No translation of static members to globals
3. **Declaration generation**: No forward declarations for static members
4. **Initialization handling**: Out-of-class definitions not processed
5. **Access translation**: `ClassName::staticMember` not translated
6. **Reference expressions**: DeclRefExpr to static members not handled

### Why 35%?
Static methods represent roughly 1/3 of static member usage. The infrastructure (name mangling, handler architecture) exists, but the specific static data member pipeline is missing.

## Translation Pattern

### Pattern Overview

C++ static data members become C global variables with mangled names. Access through class scope becomes direct global variable access.

**C++ Source:**
```cpp
class Counter {
public:
    static int count;           // Declaration in class
    static const int MAX = 100; // Const with initializer

    void increment() {
        count++;  // Access in method
    }
};

// Out-of-class definition
int Counter::count = 0;

// Usage
void test() {
    Counter::count = 10;  // Scope-resolved access
    int x = Counter::count;
}
```

**Generated C:**
```c
/* Forward declarations (header) */
extern int Counter__count;
extern const int Counter__MAX;

/* Struct definition */
struct Counter {
    /* No static members in struct */
};

/* Global variable definitions (implementation) */
int Counter__count = 0;           /* Out-of-class definition */
const int Counter__MAX = 100;     /* In-class initializer */

/* Method translation */
void Counter_increment(struct Counter *this) {
    Counter__count++;  /* Direct global access */
}

/* Usage translation */
void test() {
    Counter__count = 10;  /* Direct global access */
    int x = Counter__count;
}
```

### Key Translation Rules

1. **Declaration**: Static data members removed from struct definition
2. **Name mangling**: `ClassName::memberName` → `ClassName__memberName`
3. **Storage**: Declared as global variables with `extern` in header
4. **Definition**:
   - Out-of-class definition → global variable definition
   - In-class initializer → global variable with initializer
5. **Access**: `obj.staticMember` or `Class::staticMember` → `Class__staticMember`
6. **Const static**: Treated as const global (can have in-class initializer)

## Implementation Tasks

### Stage 1: Detection & Declaration (8-12 hours)

This stage focuses on identifying static data members and generating their declarations.

#### Task 1A: Static Member Detection in RecordHandler (Parallel)
**Estimated Time**: 3-4 hours

**Goal**: Extend RecordHandler to detect and separate static data members from instance fields.

**Implementation**:
- Create `detectStaticMembers()` helper method
- Walk through `CXXRecordDecl::fields()` and `CXXRecordDecl::decls()`
- Use `VarDecl::isStaticDataMember()` to identify static members
- Separate into:
  - Instance fields (keep in struct)
  - Static data members (process separately)
- Store static members in `HandlerContext` for later processing

**Tests** (10-12 tests in `RecordHandlerTest.cpp`):
- Detect single static int member
- Detect multiple static members
- Detect const static member
- Detect static member with in-class initializer
- Detect static array member
- Distinguish static from instance fields
- Handle empty class (no statics)
- Handle class with only static members
- Handle mix of public/private static members
- Detect static members in nested classes
- Handle template class static members (future)
- Verify static members not in struct fields

#### Task 1B: Static Member Declaration Generator (Parallel)
**Estimated Time**: 3-4 hours

**Goal**: Generate C global variable declarations for static data members.

**Implementation**:
- Create `StaticMemberTranslator` helper class
- Method: `generateStaticDeclaration(VarDecl* staticMember, Context& ctx)`
- Extract member type, name, qualifiers
- Generate mangled name: `ClassName__memberName`
- Create C `VarDecl` with:
  - Translated type
  - Mangled name
  - `extern` storage class (for header)
  - Const qualifier preserved
- Register in `HandlerContext::globalDecls`

**Tests** (10-12 tests in `StaticMemberTranslatorTest.cpp`):
- Generate declaration for static int
- Generate declaration for static const int
- Generate declaration for static pointer
- Generate declaration for static array
- Generate declaration for static struct
- Verify mangled name format
- Verify extern storage class
- Verify const qualifier preserved
- Generate multiple declarations
- Handle complex types (struct*, array, etc.)
- Verify type translation
- Handle static member with namespace scope

#### Task 1C: Name Mangling for Static Members (Parallel)
**Estimated Time**: 2-3 hours

**Goal**: Extend `NameMangler` to support static data member mangling.

**Implementation**:
- Add `mangleStaticMember(CXXRecordDecl* record, VarDecl* member)` method
- Pattern: `RecordName__memberName`
- Handle nested classes: `Outer__Inner__member`
- Handle namespaces: `Namespace__Class__member`
- Preserve existing method mangling compatibility

**Tests** (8-10 tests in `NameManglerTest.cpp`):
- Mangle simple static member
- Mangle static member in nested class
- Mangle static member in namespaced class
- Mangle static member with namespace and nested class
- Verify no collision with method names
- Mangle multiple static members
- Mangle static member with special chars in name
- Verify consistency with method mangling
- Handle anonymous namespace (internal linkage)
- Mangle template class static member (future)

**Integration Point**:
After Stage 1, RecordHandler should:
- Detect static members
- Generate extern declarations for header
- Store metadata in HandlerContext
- NOT include static members in struct definition

---

### Stage 2: Initialization (8-12 hours)

This stage handles static member definitions and initialization.

#### Task 2A: Out-of-Class Definition Detection (Parallel)
**Estimated Time**: 3-4 hours

**Goal**: Detect and process out-of-class static member definitions.

**Implementation**:
- Extend `ASTHandler` or `VariableHandler` to detect:
  - `VarDecl` with `CXXRecordDecl` as `DeclContext`
  - Not a local variable (file scope)
  - Matches a static member declaration
- Extract definition location (file scope, not in class)
- Link definition to declaration via `VarDecl::getDefinition()`
- Store in `HandlerContext::staticMemberDefinitions`

**Tests** (8-10 tests in `StaticMemberDefinitionDetectorTest.cpp`):
- Detect out-of-class definition
- Detect multiple definitions in one file
- Link definition to declaration
- Handle definition with initializer
- Handle definition without initializer (default init)
- Detect definition in namespace scope
- Handle forward declaration + definition
- Verify definition location (file scope)
- Handle split declaration/definition across files
- Error on missing definition (ODR violation check)

#### Task 2B: Global Variable Generation (Parallel)
**Estimated Time**: 3-4 hours

**Goal**: Generate C global variable definitions from static member definitions.

**Implementation**:
- Create `generateStaticDefinition(VarDecl* definition, Context& ctx)` method
- Extract initializer expression
- Generate mangled name (same as declaration)
- Create C `VarDecl` with:
  - Translated type
  - Mangled name
  - `SC_None` storage class (global scope)
  - Const qualifier if present
  - Initializer expression (translated)
- Add to implementation file, not header

**Tests** (10-12 tests in `StaticMemberTranslatorTest.cpp`):
- Generate definition with initializer
- Generate definition without initializer
- Generate const static definition
- Generate static array definition
- Generate static pointer definition
- Generate static struct definition
- Verify mangled name matches declaration
- Verify storage class (not extern)
- Verify initializer translated
- Handle complex initializer expressions
- Generate multiple definitions
- Handle zero-initialization

#### Task 2C: Initializer Expression Translation (Parallel)
**Estimated Time**: 2-3 hours

**Goal**: Translate static member initializers using ExpressionHandler.

**Implementation**:
- Integrate with existing `ExpressionHandler`
- Handle literal initializers: `static int x = 42;`
- Handle const static with in-class initializer
- Handle complex expressions: `static int* p = &globalVar;`
- Handle array initializers: `static int arr[3] = {1,2,3};`
- Handle struct initializers (designated initializers)

**Tests** (8-10 tests in `ExpressionHandlerTest.cpp`):
- Translate literal initializer
- Translate pointer initializer
- Translate array initializer
- Translate struct initializer
- Translate expression initializer (arithmetic)
- Translate reference to another static member
- Translate nullptr initializer
- Translate string literal initializer
- Handle missing initializer (default)
- Translate complex nested initializer

**Integration Point**:
After Stage 2, the transpiler should:
- Detect out-of-class definitions
- Generate global variable definitions
- Translate initializer expressions
- Place definitions in implementation file
- Maintain linkage between declaration and definition

---

### Stage 3: Access & References (8-12 hours)

This stage enables access to static members through scope resolution and member expressions.

#### Task 3A: Scope-Resolved DeclRefExpr (Parallel)
**Estimated Time**: 3-4 hours

**Goal**: Translate `ClassName::staticMember` to `ClassName__staticMember`.

**Implementation**:
- Extend `ExpressionHandler::handleDeclRefExpr()`
- Detect `DeclRefExpr` pointing to static data member
- Check if accessed through qualified name (`Class::member`)
- Generate mangled name using `NameMangler`
- Create C `DeclRefExpr` referencing global variable
- Preserve lvalue/rvalue semantics

**Tests** (10-12 tests in `ExpressionHandlerTest.cpp`):
- Translate `Class::staticMember` read
- Translate `Class::staticMember` write
- Translate `Class::staticMember` in expression
- Translate `Class::staticMember` as function argument
- Translate `Class::staticMember` address-of (`&Class::member`)
- Translate nested class static member access
- Translate namespaced class static member
- Handle const static member access
- Handle static array access with subscript
- Handle static struct member access with dot
- Translate multiple accesses in one expression
- Verify lvalue semantics preserved

#### Task 3B: Member Access Through Class Name (Parallel)
**Estimated Time**: 3-4 hours

**Goal**: Handle `obj.staticMember` (incorrect but legal C++) → `ClassName__staticMember`.

**Implementation**:
- Extend `ExpressionHandler::handleMemberExpr()`
- Detect `MemberExpr` pointing to static data member
- NOTE: In C++, `obj.staticMember` is legal but discouraged
- Translate to global variable access (ignore `obj`)
- Issue warning (optional): "Static member accessed through instance"
- Generate same mangled name as scope-resolved access

**Tests** (8-10 tests in `ExpressionHandlerTest.cpp`):
- Translate `obj.staticMember` read
- Translate `obj.staticMember` write
- Verify object expression ignored
- Translate `ptr->staticMember` (also legal)
- Handle `this->staticMember` in method
- Translate in expression context
- Handle const static access through instance
- Verify no instance field confusion
- Handle access through temporary object
- Translate multiple instance accesses

#### Task 3C: Integration with ExpressionHandler (Sequential after 3A, 3B)
**Estimated Time**: 2-3 hours

**Goal**: Ensure all expression contexts handle static member references.

**Implementation**:
- Review all `ExpressionHandler` methods
- Ensure static member refs work in:
  - Binary operators: `Class::x + Class::y`
  - Unary operators: `++Class::counter`
  - Function calls: `foo(Class::member)`
  - Assignments: `Class::x = value`
  - Casts: `(int*)Class::ptr`
  - Ternary: `cond ? Class::a : Class::b`
- Add integration tests for each context

**Tests** (12-15 tests in `ExpressionHandlerIntegrationTest.cpp`):
- Binary op with static members
- Unary increment/decrement static member
- Function call with static member argument
- Assignment to static member
- Assignment from static member
- Compound assignment (`Class::x += 5`)
- Pre/post increment on static
- Address-of static member
- Dereference static pointer
- Static member in ternary operator
- Static member in array subscript
- Static member in struct member access
- Cast involving static member
- Multiple static members in one expression
- Nested expression with static members

**Integration Point**:
After Stage 3, the transpiler should:
- Translate all static member accesses
- Handle both scope-resolved and instance access
- Work in all expression contexts
- Preserve semantics (lvalue/rvalue)
- Generate correct mangled names consistently

---

### Stage 4: Integration & E2E (6-8 hours)

Final integration and end-to-end validation.

#### Task 4A: Integration Tests
**Estimated Time**: 3-4 hours

**Goal**: Comprehensive integration tests for static member lifecycle.

**Location**: `tests/integration/handlers/StaticMemberIntegrationTest.cpp`

**Tests** (25-30 tests):
- **Declaration & Definition** (5 tests):
  - Static int with out-of-class definition
  - Const static with in-class initializer
  - Static array with definition
  - Static pointer with initializer
  - Multiple static members in one class
- **Access Patterns** (8 tests):
  - Scope-resolved access (read)
  - Scope-resolved access (write)
  - Instance access (read/write)
  - Access in method body
  - Access from free function
  - Access in constructor
  - Access in static method
  - Nested class static member access
- **Initialization** (5 tests):
  - Literal initializer
  - Expression initializer
  - Array initializer
  - Pointer initializer (address-of)
  - Reference to another static member
- **Expression Contexts** (7 tests):
  - Static member in arithmetic
  - Static member in comparison
  - Static member as function argument
  - Address-of static member
  - Increment/decrement static member
  - Static member in ternary
  - Multiple static members in expression
- **Edge Cases** (5 tests):
  - Public/private/protected static members (all become globals)
  - Static member in template class (future)
  - Static const vs non-const
  - Static member shadowing
  - Forward declaration + definition

#### Task 4B: E2E Tests
**Estimated Time**: 3-4 hours

**Goal**: Compile and execute generated C code with real algorithms.

**Location**: `tests/e2e/phase49/StaticMemberE2ETest.cpp`

**Tests** (12-15 tests: 3-4 active, 8-11 disabled):

**Active Tests** (must pass):
1. **Simple Counter**: Static int counter, increment/decrement, read
2. **Const Config**: Static const values (MAX, MIN, DEFAULT)
3. **Static Array**: Static array of ints, access by index
4. **Singleton Pattern**: Static pointer to instance, initialization

**Disabled Tests** (real-world algorithms, reference only):
5. **Object Pool**: Static pool of reusable objects
6. **Reference Counter**: Static ref count for shared resources
7. **Global Registry**: Static map/array of registered objects
8. **Factory Pattern**: Static factory method with static registry
9. **Logger**: Static log buffer and methods
10. **Performance Counter**: Static perf counters (calls, time)
11. **Memoization**: Static cache for expensive computations
12. **Flyweight Pattern**: Static pool of shared state objects
13. **State Machine**: Static state and transition table
14. **Resource Manager**: Static resource allocation tracking
15. **Thread-local Simulation**: Static per-"thread" data (single-threaded C)

**Validation**:
- Generated C code compiles without warnings
- Execution produces correct results
- Memory layout correct (no static members in struct)
- Static initialization order correct
- Global linkage correct (extern in header, definition in impl)

---

## Execution Strategy

### Parallel Execution Groups

**Stage 1 (Tasks 1A-1C)**: Detection & Declaration
- **Parallel Tasks**: 1A (Detection) + 1B (Declaration) + 1C (Mangling)
- **Duration**: ~3-4 hours (max of parallel tasks)
- **Output**: RecordHandler detects and declares static members

**Stage 2 (Tasks 2A-2C)**: Initialization
- **Parallel Tasks**: 2A (Detection) + 2B (Generation) + 2C (Initializer)
- **Duration**: ~3-4 hours (max of parallel tasks)
- **Output**: Static member definitions generated with initializers

**Stage 3 (Tasks 3A-3B → 3C)**: Access & References
- **Parallel Tasks**: 3A (Scope-resolved) + 3B (Member access)
- **Sequential Task**: 3C (Integration) after 3A, 3B complete
- **Duration**: ~3-4 hours parallel + ~2-3 hours sequential = ~5-7 hours
- **Output**: All static member accesses translated

**Stage 4 (Tasks 4A → 4B)**: Integration & E2E
- **Sequential Tasks**: 4A (Integration) then 4B (E2E)
- **Duration**: ~6-8 hours
- **Output**: Fully tested static member support

**Overall Estimated Time:**
- **Parallel approach**: ~17-23 hours (with parallelization)
- **Sequential approach**: ~30-44 hours (without parallelization)
- **Time savings**: ~40-48%

### Resource Allocation

**Optimal parallelization** (3 agents):
- **Stage 1**: Agent 1 (1A), Agent 2 (1B), Agent 3 (1C) - 3-4 hrs
- **Stage 2**: Agent 1 (2A), Agent 2 (2B), Agent 3 (2C) - 3-4 hrs
- **Stage 3**: Agent 1 (3A), Agent 2 (3B), then merge for 3C - 5-7 hrs
- **Stage 4**: Single agent for integration - 6-8 hrs

**Total with 3 agents**: ~17-23 hours

---

## Test Cases Breakdown

### Critical Test Cases

#### 1. Const Static with In-Class Initializer
```cpp
// C++
class Config {
    static const int MAX_SIZE = 1024;
};

// C
extern const int Config__MAX_SIZE;
// In impl file:
const int Config__MAX_SIZE = 1024;
```

#### 2. Non-Const Static with Out-of-Class Definition
```cpp
// C++
class Counter {
    static int count;
};
int Counter::count = 0;

// C
extern int Counter__count;
// In impl file:
int Counter__count = 0;
```

#### 3. Static Array
```cpp
// C++
class Table {
    static int lookup[256];
};
int Table::lookup[256] = {0};

// C
extern int Table__lookup[256];
// In impl file:
int Table__lookup[256] = {0};
```

#### 4. Complex Initializer
```cpp
// C++
class Manager {
    static int* ptr;
};
int Manager::ptr = nullptr;

// C
extern int* Manager__ptr;
// In impl file:
int* Manager__ptr = ((void*)0);
```

#### 5. Access in Method
```cpp
// C++
class Counter {
    static int count;
    void increment() { count++; }
};

// C
extern int Counter__count;
void Counter_increment(struct Counter* this) {
    Counter__count++;
}
```

#### 6. Scope-Resolved Access
```cpp
// C++
void test() {
    Counter::count = 10;
    int x = Counter::count;
}

// C
void test() {
    Counter__count = 10;
    int x = Counter__count;
}
```

---

## Success Criteria

### Must Have (100% Pass Rate)
- [ ] All 28-34 unit tests pass (100%)
- [ ] All 25-30 integration tests pass (100%)
- [ ] 3-4 E2E active tests compile and execute correctly
- [ ] Static members NOT in struct definition
- [ ] Global variables generated with correct names
- [ ] Extern declarations in header
- [ ] Definitions in implementation file
- [ ] Scope-resolved access translated correctly
- [ ] Instance access translated (with optional warning)
- [ ] Initializers translated correctly
- [ ] Name mangling consistent with methods
- [ ] No regressions in existing tests

### Quality Criteria
- [ ] Code follows SOLID principles
- [ ] TDD followed throughout (tests before implementation)
- [ ] Proper separation: RecordHandler (detection) + StaticMemberTranslator (translation)
- [ ] Minimal changes to existing handlers
- [ ] Documentation updated
- [ ] Generated C code compiles without warnings
- [ ] Proper const correctness maintained
- [ ] Linkage correct (extern/static)

---

## Files to Create

### New Files
1. `include/helpers/StaticMemberTranslator.h` - Static member translation
2. `src/helpers/StaticMemberTranslator.cpp` - Implementation
3. `tests/unit/helpers/StaticMemberTranslatorTest.cpp` - Unit tests
4. `tests/unit/helpers/StaticMemberDefinitionDetectorTest.cpp` - Definition detection tests
5. `tests/integration/handlers/StaticMemberIntegrationTest.cpp` - Integration tests
6. `tests/e2e/phase49/StaticMemberE2ETest.cpp` - E2E tests
7. `.planning/phases/49-static-members/PHASE49-COMPLETE.md` - Summary doc

### Files to Modify

#### Handlers
1. `include/handlers/RecordHandler.h` - Add static member detection
2. `src/handlers/RecordHandler.cpp` - Implement detection, call StaticMemberTranslator
3. `include/handlers/ExpressionHandler.h` - Add static member access
4. `src/handlers/ExpressionHandler.cpp` - Translate DeclRefExpr/MemberExpr for statics
5. `include/handlers/VariableHandler.h` - Add out-of-class definition handling
6. `src/handlers/VariableHandler.cpp` - Detect and link definitions

#### Helpers
7. `include/helpers/NameMangler.h` - Add static member mangling method
8. `src/helpers/NameMangler.cpp` - Implement mangling
9. `tests/unit/helpers/NameManglerTest.cpp` - Add mangling tests

#### Context
10. `include/handlers/HandlerContext.h` - Add static member storage
11. `src/handlers/HandlerContext.cpp` - Manage static member metadata

#### Build
12. `CMakeLists.txt` - Add new test targets

---

## Dependencies

### Internal (Required)
- **Phase 44**: Classes (RecordHandler exists)
- **Phase 45**: Virtual methods (NameMangler pattern established)
- **RecordHandler**: Detect static members in class
- **VariableHandler**: Handle out-of-class definitions
- **ExpressionHandler**: Translate access expressions
- **NameMangler**: Mangle static member names
- **HandlerContext**: Store static member metadata

### External
- **Clang AST API**: `VarDecl::isStaticDataMember()`, `CXXRecordDecl::decls()`
- **Google Test**: Unit/integration testing framework
- **CMake**: Build system

### No Dependencies
- Static members are independent of:
  - Virtual methods (Phase 45)
  - Multiple inheritance (Phase 46)
  - Templates (future)
  - Namespaces (can enhance but not required)

---

## Risk Mitigation

### Risk 1: Initialization Order
**Problem**: C++ guarantees static member initialization order within a TU, not across TUs.

**Mitigation**:
- Document limitation in generated C code
- Add comments explaining initialization order
- Suggest manual initialization if cross-TU dependencies exist
- Test: Verify single-TU initialization works correctly

### Risk 2: Template Class Static Members
**Problem**: Each template instantiation has separate static member.

**Mitigation**:
- Explicitly OUT OF SCOPE for Phase 49
- Defer to template specialization phase
- Document limitation
- Test: Skip or error on template class static members

### Risk 3: Name Collisions
**Problem**: Mangled names might collide with user-defined globals.

**Mitigation**:
- Use consistent mangling pattern (`Class__member`)
- Add `__cpptoc_` prefix if collision detected (optional)
- Test: Verify no collisions in large codebases
- Document mangling pattern

### Risk 4: ODR Violations
**Problem**: Missing or duplicate definitions.

**Mitigation**:
- Validate definition exists for non-const statics
- Error if definition missing
- Warn if multiple definitions found
- Test: Verify ODR checks work

### Risk 5: Const Static In-Class Initializer
**Problem**: C++11 allows const static with in-class initializer, but pre-C++11 doesn't.

**Mitigation**:
- Support both patterns
- In-class initializer → direct global definition
- Out-of-class definition → link to declaration
- Test: Both initialization patterns

---

## Naming Conventions

### Mangled Names
- **Pattern**: `ClassName__memberName`
- **Nested class**: `Outer__Inner__member`
- **Namespace**: `Namespace__Class__member`
- **Examples**:
  - `Counter::count` → `Counter__count`
  - `Outer::Inner::x` → `Outer__Inner__x`
  - `ns::Class::val` → `ns__Class__val`

### Helper Classes
- `StaticMemberTranslator` - Main translation logic
- `StaticMemberDefinitionDetector` - Find out-of-class definitions

### Test Files
- `StaticMemberTranslatorTest.cpp` - Unit tests
- `StaticMemberIntegrationTest.cpp` - Integration tests
- `StaticMemberE2ETest.cpp` - E2E tests

---

## Next Steps After Completion

### Phase 50-52: Operator Overloading (235-365 hours)
- Arithmetic operators
- Comparison operators
- Special operators (assignment, subscript, arrow)

### Phase 53: Using Declarations (12-18 hours)
- Type aliases
- Using directives
- Namespace aliases

### Phase 54: Range-Based For Loops (20-30 hours)
- Iterator protocol
- Container support

### Enhancement: Template Static Members
- Each instantiation gets unique static member
- Mangle with template parameters
- Link to template phase

---

## Validation Strategy

### Unit Tests
- Test each helper class in isolation
- Mock dependencies
- 100% code coverage goal

### Integration Tests
- Test complete static member lifecycle
- Declaration → Definition → Access
- Multiple classes, multiple members

### E2E Tests
- Compile generated C code
- Execute and verify results
- Real-world algorithms (disabled tests as reference)

### Regression Tests
- Ensure no breaks in existing features
- Run full test suite after each stage
- Automated CI/CD checks

---

## Documentation Updates

### User Documentation
- Add "Static Members" section to user guide
- Show translation examples
- Explain limitations (templates, initialization order)
- Migration guide from C++ to C

### Developer Documentation
- Update architecture diagram
- Document StaticMemberTranslator
- Add to handler pipeline documentation
- Update CLAUDE.md with static member notes

### Code Comments
- Document all new public APIs
- Explain mangling pattern
- Note ODR requirements
- Clarify initialization order

---

## Progress Tracking

### Stage Completion Checklist

**Stage 1: Detection & Declaration**
- [ ] Task 1A: Static member detection (10-12 tests)
- [ ] Task 1B: Declaration generation (10-12 tests)
- [ ] Task 1C: Name mangling (8-10 tests)
- [ ] Stage 1 integration test

**Stage 2: Initialization**
- [ ] Task 2A: Definition detection (8-10 tests)
- [ ] Task 2B: Global variable generation (10-12 tests)
- [ ] Task 2C: Initializer translation (8-10 tests)
- [ ] Stage 2 integration test

**Stage 3: Access & References**
- [ ] Task 3A: Scope-resolved access (10-12 tests)
- [ ] Task 3B: Member access (8-10 tests)
- [ ] Task 3C: Expression integration (12-15 tests)
- [ ] Stage 3 integration test

**Stage 4: Integration & E2E**
- [ ] Task 4A: Integration tests (25-30 tests)
- [ ] Task 4B: E2E tests (3-4 active tests)
- [ ] All tests passing
- [ ] Documentation complete

**Final Validation**
- [ ] No regressions in existing tests
- [ ] Code review complete
- [ ] SOLID principles verified
- [ ] TDD process followed
- [ ] Git commit with proper message
- [ ] Phase completion summary written

---

**Created**: 2025-12-26
**Status**: READY FOR IMPLEMENTATION
**Pattern**: Global variables with name mangling
**Estimated Completion**: 17-23 hours (parallel) / 30-44 hours (sequential)

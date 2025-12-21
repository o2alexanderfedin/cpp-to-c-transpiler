# Phase 10 Plan: Lambda Expression Translation (v2.3.0)

**Phase**: 10 of 17 (C++ Core Features Workstream)
**Roadmap**: `../../ROADMAP.md`
**Brief**: `../../BRIEF.md`
**Target Version**: v2.3.0
**Status**: PENDING
**Priority**: HIGH (Critical feature for modern C++)
**Prerequisite**: Phase 8 (Standalone Functions - lambda body becomes standalone C function)

## Phase Goal

Translate C++ lambda expressions to C function pointers combined with closure structs. Enable modern C++ code patterns that use lambdas for callbacks, algorithm parameters, and functional programming idioms by generating equivalent C code with manual closure management.

## Business Value

Lambda expressions are ubiquitous in modern C++ codebases:
- Callbacks and event handlers (common in UI frameworks, async libraries)
- Algorithm parameters (std::sort, std::find_if predicates)
- Functional programming patterns (map, filter, reduce operations)
- Asynchronous operations (async tasks, promise continuations)
- STL algorithms (any modern code using <algorithm>)

**Impact**: Without lambda support, transpiled C++ cannot execute code using modern C++ idioms—affecting >50% of contemporary C++ libraries.

## Deliverables

### Source Code
- [ ] Implement `CppToCVisitor::VisitLambdaExpr(LambdaExpr *E)` visitor method
- [ ] Capture analysis engine (by value, by reference, implicit captures [=], [&])
- [ ] Closure struct generation (struct with captured variables as members)
- [ ] Function pointer generation (standalone C function for lambda body)
- [ ] Lambda invocation translation (convert `lambda_expr()` to `lambda_func(closure_ptr)`)
- [ ] Mutable lambda support (allow captured variables to be modified)
- [ ] Generic lambda support (template instantiation for auto parameters)
- [ ] Nested lambda support (lambdas capturing outer lambda's closure)

### Tests
- [ ] `tests/LambdaExpressionIntegrationTest.cpp` (18+ tests)
  - Basic lambda (no captures)
  - Value captures (copy semantics)
  - Reference captures (pointer semantics)
  - Implicit value captures ([=])
  - Implicit reference captures ([&])
  - Mixed captures ([=, &var1, &var2])
  - Generic lambdas (auto parameters)
  - Mutable lambdas (const correctness)
  - Lambda with return type (auto vs explicit)
  - Nested lambdas (lambda capturing outer lambda)
  - Lambda as function parameter
  - Lambda in STL algorithms (std::sort with custom comparator)
  - Lambda lifetime and closure lifetime
  - Lambda in containers (storing lambda function pointers)
  - Capture of this pointer
  - Capture of static variables
  - Recursive lambda (via reference capture of self)
  - Performance baseline (closure overhead <10%)

### CLI Integration
- [ ] Add `--enable-lambdas={off,on}` flag (default: on)
- [ ] Add `--lambda-strategy={closure,fastpath}` for future optimization

### Documentation
- [ ] Update `docs/CHANGELOG.md` for v2.3.0
- [ ] Update `README.md` with lambda feature description
- [ ] Update `website/src/pages/features.astro`
- [ ] Create `docs/examples/lambda-expressions.md` with C++ → C translation examples
- [ ] Document capture semantics and closure struct layout

### Release
- [ ] Git-flow release v2.3.0
- [ ] Tag on GitHub with release notes

## Technical Design

### Architecture Overview

Lambda expression translation converts C++ lambdas to C function pointers + closure structs:

```
┌──────────────────────────────────────────────────────┐
│ Lambda Expression Translation Architecture           │
├──────────────────────────────────────────────────────┤
│                                                      │
│  C++ Lambda:                                        │
│    auto lam = [x, &y](int z) { return x+y+z; }    │
│         ↓                                            │
│  [Step 1: Capture Analysis]                         │
│    - Extract variables from capture list           │
│    - Classify: by-value (x) vs by-reference (&y)  │
│         ↓                                            │
│  [Step 2: Closure Struct Generation]                │
│    struct lambda_closure_0 {                        │
│      int x;      // value capture                   │
│      int *y;     // reference capture               │
│    };                                               │
│         ↓                                            │
│  [Step 3: Function Pointer Generation]              │
│    int lambda_func_0(struct lambda_closure_0 *cl, │
│                      int z) {                       │
│      return cl->x + *cl->y + z;                    │
│    }                                                │
│         ↓                                            │
│  [Step 4: Invocation Translation]                   │
│    struct lambda_closure_0 closure;                │
│    closure.x = x;                                  │
│    closure.y = &y;                                 │
│    int result = lambda_func_0(&closure, 10);      │
│                                                      │
└──────────────────────────────────────────────────────┘
```

### Capture Semantics

#### 1. By-Value Capture

**C++**:
```cpp
void test_value_capture() {
  int x = 42;
  auto lam = [x](int z) { return x + z; };
  int result = lam(10);  // 52
}
```

**C** (Generated):
```c
struct lambda_closure_0 {
  int x;  // Captured by value
};

int lambda_func_0(struct lambda_closure_0 *cl, int z) {
  return cl->x + z;
}

void test_value_capture() {
  int x = 42;

  // Create closure with captured value
  struct lambda_closure_0 closure;
  closure.x = x;

  // Invoke lambda function
  int result = lambda_func_0(&closure, 10);  // 52
}
```

**Key Points**:
- Captured variable copied into closure struct
- Modifications to `x` after capture don't affect lambda
- Closure outlives original variable lifetime

#### 2. By-Reference Capture

**C++**:
```cpp
void test_reference_capture() {
  int x = 42;
  auto lam = [&x](int z) { x += z; return x; };
  int result = lam(10);  // x becomes 52, returns 52
}
```

**C** (Generated):
```c
struct lambda_closure_0 {
  int *x;  // Captured by reference (pointer)
};

int lambda_func_0(struct lambda_closure_0 *cl, int z) {
  *cl->x += z;
  return *cl->x;
}

void test_reference_capture() {
  int x = 42;

  // Create closure with reference (pointer) to variable
  struct lambda_closure_0 closure;
  closure.x = &x;

  // Invoke lambda function
  int result = lambda_func_0(&closure, 10);  // x becomes 52
}
```

**Key Points**:
- Captured variable stored as pointer in closure struct
- Lambda accesses original variable via pointer dereference
- Modifications affect original variable
- **CRITICAL**: Dangling reference danger if closure outlives variable

#### 3. Implicit Value Capture ([=])

**C++**:
```cpp
void test_implicit_value() {
  int x = 10, y = 20, z = 30;
  auto lam = [=](int a) { return x + y + z + a; };
  int result = lam(5);  // 65
}
```

**C** (Generated):
```c
struct lambda_closure_0 {
  int x;  // All local variables captured
  int y;
  int z;
};

int lambda_func_0(struct lambda_closure_0 *cl, int a) {
  return cl->x + cl->y + cl->z + a;
}

void test_implicit_value() {
  int x = 10, y = 20, z = 30;

  // Capture all variables in scope
  struct lambda_closure_0 closure;
  closure.x = x;
  closure.y = y;
  closure.z = z;

  int result = lambda_func_0(&closure, 5);  // 65
}
```

**Capture Analysis**:
- `[=]` captures all local variables by value
- Parser must identify all variable references in lambda body
- Generate closure struct member for each referenced variable

#### 4. Implicit Reference Capture ([&])

**C++**:
```cpp
void test_implicit_reference() {
  int x = 10, y = 20, z = 30;
  auto lam = [&](int a) { x += a; return x + y + z; };
  int result = lam(5);  // 65
}
```

**C** (Generated):
```c
struct lambda_closure_0 {
  int *x;  // All variables captured by reference
  int *y;
  int *z;
};

int lambda_func_0(struct lambda_closure_0 *cl, int a) {
  *cl->x += a;
  return *cl->x + *cl->y + *cl->z;
}

void test_implicit_reference() {
  int x = 10, y = 20, z = 30;

  // Capture pointers to all variables
  struct lambda_closure_0 closure;
  closure.x = &x;
  closure.y = &y;
  closure.z = &z;

  int result = lambda_func_0(&closure, 5);
}
```

#### 5. Mixed Captures

**C++**:
```cpp
void test_mixed_captures() {
  int x = 1, y = 2, z = 3, w = 4;
  // Default value capture, but y and z by reference
  auto lam = [=, &y, &z](int a) {
    return x + y + z + w + a;
  };
  int result = lam(10);
}
```

**C** (Generated):
```c
struct lambda_closure_0 {
  int x;      // Value capture
  int *y;     // Reference capture (pointer)
  int *z;     // Reference capture (pointer)
  int w;      // Value capture (default)
};

int lambda_func_0(struct lambda_closure_0 *cl, int a) {
  return cl->x + *cl->y + *cl->z + cl->w + a;
}

void test_mixed_captures() {
  int x = 1, y = 2, z = 3, w = 4;

  struct lambda_closure_0 closure;
  closure.x = x;
  closure.y = &y;
  closure.z = &z;
  closure.w = w;

  int result = lambda_func_0(&closure, 10);
}
```

**Parsing Logic**:
1. Parse capture list to extract explicit captures
2. If `[=` present: capture all referenced variables by value (unless explicitly `&var`)
3. If `[&` present: capture all referenced variables by reference (unless explicitly `var`)
4. Create closure struct with appropriate member types

### Generic Lambdas (Template Instantiation)

**C++**:
```cpp
void test_generic_lambda() {
  int x = 10;
  double y = 3.14;

  auto lam = [x](auto z) { return x + z; };

  int result1 = lam(5);           // Instantiation 1: int
  double result2 = lam(2.71);     // Instantiation 2: double
}
```

**C** (Generated - Template-Like Pattern):
```c
// Closure struct (shared across instantiations)
struct lambda_closure_0 {
  int x;
};

// Template instance 1: int parameter
int lambda_func_0_int(struct lambda_closure_0 *cl, int z) {
  return cl->x + z;
}

// Template instance 2: double parameter
double lambda_func_0_double(struct lambda_closure_0 *cl, double z) {
  return cl->x + z;
}

// Overload resolution wrapper (optional, for direct calls)
// In practice, we use function pointers to select at runtime

void test_generic_lambda() {
  int x = 10;
  double y = 3.14;

  struct lambda_closure_0 closure;
  closure.x = x;

  // Instantiation 1
  int result1 = lambda_func_0_int(&closure, 5);

  // Instantiation 2
  double result2 = lambda_func_0_double(&closure, 2.71);
}
```

**Translation Steps**:
1. Detect `auto` parameters in lambda (marks generic lambda)
2. For each instantiation site (call with different type):
   - Generate specialized function (lambda_func_0_int, lambda_func_0_double, etc.)
   - Reuse closure struct across instantiations
3. Replace call site with direct call to appropriate specialization

### Mutable Lambdas (Const Correctness)

**C++**:
```cpp
void test_mutable_lambda() {
  int counter = 0;

  // mutable allows modification of captured value
  auto increment = [counter]() mutable {
    return ++counter;  // Modifies the COPY in closure
  };

  increment();  // counter in closure = 1
  increment();  // counter in closure = 2
  // Original counter still 0
}
```

**C** (Generated):
```c
struct lambda_closure_0 {
  int counter;  // Mutable member (no const)
};

int lambda_func_0(struct lambda_closure_0 *cl) {
  return ++cl->counter;
}

void test_mutable_lambda() {
  int counter = 0;

  struct lambda_closure_0 closure;
  closure.counter = counter;

  lambda_func_0(&closure);  // closure.counter = 1
  lambda_func_0(&closure);  // closure.counter = 2
  // counter still 0 (closure is separate copy)
}
```

**Key Difference**:
- Non-mutable lambda: closure parameters passed as `const` (read-only)
- Mutable lambda: closure parameters can be modified
- Implementation: Add/remove `const` from closure pointer parameter

### Nested Lambdas (Lambda Capturing Lambda)

**C++**:
```cpp
void test_nested_lambda() {
  int x = 10;

  auto outer = [x](int y) { return x + y; };
  auto inner = [outer](int z) { return outer(5) + z; };

  int result = inner(3);  // outer(5) + 3 = 18
}
```

**C** (Generated):
```c
// Outer lambda
struct lambda_closure_outer {
  int x;
};

int lambda_func_outer(struct lambda_closure_outer *cl, int y) {
  return cl->x + y;
}

// Inner lambda captures outer lambda
struct lambda_closure_inner {
  int (*outer_func)(struct lambda_closure_outer*, int);  // Function pointer
  struct lambda_closure_outer outer_closure;              // Closure struct
};

int lambda_func_inner(struct lambda_closure_inner *cl, int z) {
  // Call captured lambda (needs closure)
  int outer_result = cl->outer_func(&cl->outer_closure, 5);
  return outer_result + z;
}

void test_nested_lambda() {
  int x = 10;

  // Create outer lambda closure
  struct lambda_closure_outer outer_closure;
  outer_closure.x = x;

  // Create inner lambda closure (captures outer lambda)
  struct lambda_closure_inner inner_closure;
  inner_closure.outer_func = &lambda_func_outer;
  inner_closure.outer_closure = outer_closure;

  int result = lambda_func_inner(&inner_closure, 3);
}
```

### Lambda as Function Parameter

**C++**:
```cpp
int apply_operation(int x, int y, auto fn) {
  return fn(x, y);
}

void test_lambda_param() {
  int result = apply_operation(5, 3,
    [](int a, int b) { return a * b; }
  );
}
```

**C** (Generated):
```c
// Generic function parameter: needs function pointer + closure
typedef int (*operation_func)(void*, int, int);

struct lambda_closure_0 {
  // No captures
};

int lambda_func_0(struct lambda_closure_0 *cl, int a, int b) {
  return a * b;
}

int apply_operation(int x, int y,
                   operation_func fn, void *closure) {
  return fn(closure, x, y);
}

void test_lambda_param() {
  struct lambda_closure_0 closure;

  int result = apply_operation(5, 3,
                              (operation_func)lambda_func_0,
                              (void*)&closure);
}
```

**Challenge**: C templates don't exist, so generic function parameters require:
- Type erasure via `void*` closure pointer
- Function pointers with consistent signature

### Lambda Capture of `this` Pointer

**C++**:
```cpp
class Counter {
  int count;
public:
  auto make_incrementer() {
    return [this](int x) { count += x; return count; };
  }
};
```

**C** (Generated):
```c
struct Counter {
  int count;
};

struct lambda_closure_0 {
  struct Counter *this_ptr;  // Capture this pointer
};

int lambda_func_0(struct lambda_closure_0 *cl, int x) {
  cl->this_ptr->count += x;
  return cl->this_ptr->count;
}

// Method becomes standalone function
int Counter_make_incrementer(struct Counter *this,
                            // Return function pointer + closure?
                            // Tricky - return by output parameter
                            void (**out_func)(void*, int),
                            void (**out_closure)()) {
  struct lambda_closure_0 *closure =
    (struct lambda_closure_0*)malloc(sizeof(*closure));
  closure->this_ptr = this;

  *out_func = (void(*)(void*,int))lambda_func_0;
  *out_closure = (void*)closure;
}
```

### Visitor Method Implementation Strategy

#### VisitLambdaExpr Implementation

```cpp
bool CppToCVisitor::VisitLambdaExpr(LambdaExpr *E) {
  // 1. Generate unique lambda identifier
  std::string lambdaId = "lambda_" + std::to_string(lambdaCounter++);

  // 2. Analyze captures
  LambdaCapture capture_analyzer;
  auto captures = capture_analyzer.analyzeCaptures(E);
  // Result: map of variable_name -> (capture_type, type_name)
  // capture_type: VALUE, REFERENCE, IMPLICIT_VALUE, IMPLICIT_REFERENCE

  // 3. Generate closure struct
  std::string closureStructName = lambdaId + "_closure";
  std::string closureStruct = generateClosureStruct(
    closureStructName,
    E->getLambdaClass(),
    captures
  );

  // 4. Generate lambda function
  std::string funcName = lambdaId + "_func";
  std::string lambdaFunc = generateLambdaFunction(
    funcName,
    closureStructName,
    E
  );

  // 5. Store translation (needed when lambda is invoked)
  lambdaTranslations[E] = {
    .closureStruct = closureStruct,
    .lambdaFunc = lambdaFunc,
    .funcName = funcName,
    .closureStructName = closureStructName,
    .captures = captures
  };

  // 6. Return true to indicate we handled this expression
  return true;
}
```

#### Call Expression Handling for Lambdas

When a lambda is called (`lam(arg1, arg2)`), detect and translate:

```cpp
bool CppToCVisitor::VisitCallExpr(CallExpr *E) {
  // Check if callee is a lambda expression
  if (auto lambdaE = dyn_cast<LambdaExpr>(E->getCallee())) {
    // 1. Generate closure initialization code
    std::string closureInit = generateClosureInit(
      lambdaE,
      lambdaTranslations[lambdaE]
    );

    // 2. Generate function call
    std::string funcCall = generateLambdaCall(
      E,
      lambdaTranslations[lambdaE]
    );

    // Output: closure struct + initialization + function call
    currentCode += closureInit;
    currentCode += "\n";
    currentCode += funcCall;

    return true;
  }

  // ... handle non-lambda calls ...
}
```

### Key Challenges & Solutions

#### Challenge 1: Capture Analysis Complexity

**Problem**: Identifying all captured variables requires semantic analysis.

**Solution**:
- Use Clang's built-in capture list from LambdaExpr
- Analyze lambda body for variable references
- Support explicit capture list + implicit captures
- Build dependency graph for nested captures

#### Challenge 2: Generic Lambda Instantiation

**Problem**: `auto` parameters require function specialization at each call site.

**Solution**:
- Detect generic lambdas (have auto parameters)
- For each call site: generate type-specific function
- Reuse closure struct across instantiations
- Use suffix naming: lambda_func_0_int, lambda_func_0_double

#### Challenge 3: Dangling Reference Danger

**Problem**: Reference captures can outlive captured variables.

**Solution**:
- Generate compiler warning when closure escapes function scope
- Document lifetime semantics clearly
- Recommend by-value capture for non-trivial lifetimes
- Runtime validation option (debug mode)

#### Challenge 4: Function Pointer Representation

**Problem**: Lambda signature varies by capture list and parameters.

**Solution**:
- Generate function with explicit closure pointer parameter
- Use void* type erasure for generic higher-order functions
- Create typedef for lambda function signature
- Provide macro for easy function pointer assignment

#### Challenge 5: Nested Lambdas and Recursion

**Problem**: Lambdas can capture other lambdas or themselves.

**Solution**:
- Store function pointer + closure in nested lambda closure
- For self-recursion: capture via reference using void*
- Handle forward declarations for recursive lambdas
- Limit nesting depth in analysis (prevent exponential code generation)

### Integration Points

1. **CppToCVisitor**: Add `VisitLambdaExpr` visitor method
2. **Call Expression Handling**: Detect lambda invocations and translate calls
3. **Scope Analysis**: Coordinate with variable tracking for captures
4. **Type System**: Map C++ lambda types to C function pointer types
5. **Code Generation**: Insert closure structs and functions into output

### Test Plan (18+ Tests)

#### Basic Lambdas (3 tests)
1. **NoCapture**: Lambda with no captured variables
2. **StaticLambda**: Static/constexpr lambda (no runtime closure needed)
3. **EmptyLambda**: Lambda with empty parameter list

#### Value Captures (4 tests)
4. **SingleValueCapture**: Single variable captured by value
5. **MultipleValueCaptures**: Multiple variables captured by value
6. **ValueCaptureModification**: Verify captured copy is independent
7. **ValueCaptureAfterModification**: Capture value at time of invocation

#### Reference Captures (4 tests)
8. **SingleReferenceCapture**: Single variable captured by reference
9. **MultipleReferenceCaptures**: Multiple variables captured by reference
10. **ReferenceCaptureSeeModification**: Lambda sees variable modifications
11. **ReferenceCaptureDanglingDetection**: Warning on escaping closure

#### Implicit Captures (3 tests)
12. **ImplicitValueCapture**: [=] captures all variables by value
13. **ImplicitReferenceCapture**: [&] captures all variables by reference
14. **MixedExplicitImplicit**: [=, &var] default value, explicit reference

#### Advanced Features (4 tests)
15. **GenericLambda**: auto parameter instantiation at multiple call sites
16. **MutableLambda**: mutable keyword allows modification of captured values
17. **LambdaWithReturnType**: Explicit return type specification
18. **NestedLambdas**: Lambda capturing another lambda

#### Integration Tests (3+ tests)
19. **LambdaAsParameter**: Passing lambda to function expecting callback
20. **LambdaInSTLAlgorithm**: Using lambda with std::sort comparator
21. **LambdaInContainer**: Storing lambda function pointers in vector
22. **CaptureThisPointer**: Member lambda capturing this in class method
23. **RecursiveLambda**: Self-referential lambda via reference capture
24. **LambdaLifetime**: Closure lifetime vs. original variable lifetime
25. **PerformanceBaseline**: Closure overhead measured (<10%)

### Verification Criteria

- [ ] **Functional**: All 18+ tests passing (100%)
- [ ] **Capture Correctness**: Variables captured correctly (value vs. reference)
- [ ] **Closure Struct**: Generated with correct member layout and types
- [ ] **Function Pointer**: Proper signature and calling convention
- [ ] **Generic Support**: Template instantiation working for auto parameters
- [ ] **Mutable Support**: mutable lambdas modify closure members
- [ ] **Nesting**: Nested lambdas working with proper closure passing
- [ ] **Performance**: Closure overhead <10% vs. inline code
- [ ] **Linting**: Zero linting errors (clang-tidy, cppcheck)
- [ ] **Code Review**: Separate review by another agent

## Key Features

1. **Capture Semantics**: Full support for value, reference, and implicit captures
2. **Closure Struct Generation**: Automatic struct creation with captured variable members
3. **Function Pointer Generation**: Lambda body as standalone C function with closure pointer
4. **Generic Lambda Support**: Template instantiation for auto parameters
5. **Mutable Lambda Support**: const correctness with mutable keyword
6. **Nested Lambda Support**: Lambdas capturing other lambdas
7. **STL Algorithm Integration**: Lambdas as predicates in std::sort, std::find_if, etc.
8. **Lifetime Safety**: Warnings for dangling references from escaping closures

## Dependencies

- **Requires: Phase 8 (Standalone Functions)** - Lambda body becomes standalone C function with closure parameter
- **Requires: Phase 7 or earlier** - Basic variable tracking and scope analysis
- **Optional: Phase 9** - Virtual method support for member lambdas
- **Optional: Phase 11** - Template instantiation already solved (reuse for generic lambdas)

## Implementation Milestones

### Milestone 1: Visitor Method Scaffolding (15% effort)
- [ ] Add `VisitLambdaExpr` method stub to CppToCVisitor
- [ ] Add LambdaCapture analyzer class stub
- [ ] Add lambda ID counter and translation map
- [ ] Verify project builds without errors

### Milestone 2: Basic Lambda Translation (35% effort)
- [ ] Implement capture analysis (explicit captures)
- [ ] Generate closure struct for basic captures
- [ ] Generate lambda function with closure parameter
- [ ] Implement simple call expression handling
- [ ] Basic tests passing (4/18)
- [ ] No captures and single value capture working

### Milestone 3: Advanced Captures (25% effort)
- [ ] Implement reference capture (pointer members)
- [ ] Implement implicit [=] and [&] captures
- [ ] Implement mixed explicit/implicit captures
- [ ] Mutable lambda support
- [ ] Advanced tests passing (12/18)
- [ ] All capture modes working

### Milestone 4: Generic & Nested Lambdas (15% effort)
- [ ] Generic lambda (auto parameter) instantiation
- [ ] Nested lambda support (lambda capturing lambda)
- [ ] Recursive lambda support
- [ ] Integration tests passing (18+/18)

### Milestone 5: Integration & Optimization (10% effort)
- [ ] STL algorithm integration testing
- [ ] Performance benchmarking (<10% overhead)
- [ ] All tests passing (18+/18)
- [ ] Code review and linting
- [ ] Documentation completion

## Success Criteria Summary

| Criteria | Target | Status |
|----------|--------|--------|
| Tests Passing | 18+/18 (100%) | ⏳ PENDING |
| Captures Correct | All modes (value, ref, implicit) | ⏳ PENDING |
| Closure Generation | Correct layout for all captures | ⏳ PENDING |
| Generic Support | Template instantiation working | ⏳ PENDING |
| Mutable Support | Const correctness correct | ⏳ PENDING |
| Performance Impact | <10% closure overhead | ⏳ PENDING |
| Linting Errors | 0 errors/warnings | ⏳ PENDING |
| Code Review | Approved by separate review | ⏳ PENDING |

## Next Steps

1. **Setup**: Create LambdaCapture analyzer class skeleton
2. **Implement**: Follow milestones to implement visitor method
3. **Test**: Run test suite after each milestone
4. **Document**: Write examples and update documentation
5. **Release**: Execute git-flow release v2.3.0

## Resources

### Key Files
- Source: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCVisitor.cpp`
- Headers:
  - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/CppToCVisitor.h`
  - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/LambdaCapture.h` (to create)
- Tests:
  - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/LambdaExpressionIntegrationTest.cpp` (to create)

### Documentation References
- [C++ Lambda Expressions Reference](https://en.cppreference.com/w/cpp/language/lambda)
- [C++ Capture Semantics](https://en.cppreference.com/w/cpp/language/lambda#Capture)
- [C++ Generic Lambdas](https://en.cppreference.com/w/cpp/language/lambda#Generic_lambda)
- [C Function Pointers](https://en.cppreference.com/w/c/language/pointer)
- [Phase 8: Standalone Functions](./../../phases/08-standalone-functions/PLAN.md) (Prerequisite)

### Related Phases
- **Phase 8: Standalone Functions** (v2.2.0) - Lambda body becomes function
- **Phase 11: Template Integration** (v2.4.0) - Template instantiation patterns
- **Phase 9: Virtual Methods** (v2.2.0) - Member lambdas may need vtable integration

---

## Execution Checklist

- [ ] Read and understand ROADMAP and this PLAN
- [ ] Review Phase 8 implementation (standalone functions)
- [ ] Design LambdaCapture analyzer class
- [ ] Create LambdaCapture.h header with interface
- [ ] Implement CppToCVisitor::VisitLambdaExpr
- [ ] Implement CppToCVisitor::VisitCallExpr for lambda invocations
- [ ] Create LambdaExpressionIntegrationTest.cpp with 18+ tests
- [ ] Implement and test each capture mode
- [ ] Implement generic lambda support
- [ ] Implement mutable lambda support
- [ ] Implement nested lambda support
- [ ] Run all tests and verify passing
- [ ] Run linters (clang-format, clang-tidy)
- [ ] Update documentation files
- [ ] Create git-flow release v2.3.0
- [ ] Verify release builds and tests pass
- [ ] Update git tags and branches

**Ready to execute Phase 10: Lambda Expression Translation**

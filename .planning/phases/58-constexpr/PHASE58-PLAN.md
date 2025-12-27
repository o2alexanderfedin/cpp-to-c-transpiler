# Phase 58: constexpr/consteval Implementation Plan

**Phase**: 58 (Compile-Time Evaluation)
**Status**: PLANNING
**Priority**: LOW (optimization feature, not critical for correctness)
**Estimated Duration**: 80-120 hours
**Risk Level**: VERY HIGH (requires compile-time interpreter)
**Dependencies**: Expression evaluation engine, constant folding infrastructure

---

## Executive Summary

Phase 58 implements **partial support for C++11/14/17/20/23 constexpr and C++20 consteval features** with a **pragmatic, conservative approach** that prioritizes correctness over completeness.

**Strategic Decision: Hybrid Approach**
- **Simple cases**: Compile-time evaluation (macros, const values)
- **Complex cases**: Runtime fallback (emit as normal functions)
- **Goal**: Enable constexpr-heavy code to transpile, not achieve full compile-time evaluation

**Current Status**: 10% complete (exploratory prototypes exist)
- ✅ Basic constexpr detection (`ConstexprEnhancementHandler`)
- ✅ Basic `if consteval` translation (`ConstevalIfTranslator`)
- ✅ Simple compile-time evaluation (literals only)
- ❌ NOT production-ready (limited scope)
- ❌ Complex constexpr → runtime fallback only
- ❌ No full expression evaluator
- ❌ No constexpr lambda support
- ❌ No constexpr destructor support

**Gap Analysis**: Full constexpr support requires a **compile-time interpreter**, which is 200+ hours of work. This phase focuses on **best-effort optimization** with runtime fallback as the safety net.

---

## Objective

**Provide pragmatic constexpr support** that enables C++ code using constexpr to transpile successfully, with:

1. **Simple Cases Optimized**: Compile-time evaluation for literals, arithmetic, simple logic
2. **Complex Cases Deferred**: Runtime fallback for loops, function calls, allocation
3. **Correctness Guaranteed**: Runtime fallback ensures semantic equivalence
4. **Transparent Behavior**: Clear diagnostics when falling back to runtime
5. **User Control**: Flags to control optimization level

**Non-Objectives** (Explicitly Out of Scope):
- ❌ Full compile-time interpreter (too complex for this phase)
- ❌ Compile-time allocation/deallocation (C has no equivalent)
- ❌ Compile-time virtual function calls (requires RTTI at compile-time)
- ❌ Compile-time exception handling (C has no exceptions)
- ❌ Compile-time new/delete (dynamic memory)

---

## Context

### What is constexpr?

**C++11**: `constexpr` functions can be evaluated at compile-time if given constant arguments.

```cpp
constexpr int square(int x) {
    return x * x;
}

constexpr int result = square(5);  // Evaluated at compile-time: result = 25
```

**C++14**: Relaxed restrictions (local variables, loops, conditionals).

```cpp
constexpr int factorial(int n) {
    int result = 1;
    for (int i = 2; i <= n; ++i) {
        result *= i;
    }
    return result;
}

constexpr int fact5 = factorial(5);  // Compile-time: 120
```

**C++17**: constexpr lambdas, if constexpr.

**C++20**: constexpr destructors, virtual functions, dynamic allocation (limited).

**C++20**: `consteval` - **always** evaluated at compile-time (immediate functions).

```cpp
consteval int must_be_compile_time(int x) {
    return x * x;
}

int runtime_value = 5;
// int result = must_be_compile_time(runtime_value);  // ERROR: not compile-time
constexpr int result = must_be_compile_time(5);  // OK
```

**C++23**: `if consteval` - branch based on compile-time vs runtime context.

```cpp
constexpr int compute(int x) {
    if consteval {
        return x * x;  // Compile-time version
    } else {
        return x * x + log(x);  // Runtime version (can use non-constexpr functions)
    }
}
```

### Why constexpr is Complex to Transpile

**Challenge 1: C Has No Compile-Time Evaluation**

C has `const` (immutable) but not `constexpr` (compile-time evaluated):

```c
// C: const means immutable, not compile-time constant
const int x = 5;
int arr[x];  // ERROR in C: array size must be constant expression

// C++: constexpr is compile-time constant
constexpr int x = 5;
int arr[x];  // OK: x is compile-time constant
```

**Challenge 2: Evaluator Complexity**

To evaluate constexpr functions at compile-time, we need:
- **Expression evaluator**: Arithmetic, logic, comparisons
- **Control flow evaluator**: Loops, conditionals, branching
- **Function call evaluator**: Recursive function calls
- **Memory model**: Simulated compile-time memory for variables
- **Error handling**: Detect undefined behavior at compile-time

This is essentially **building an interpreter** for a subset of C++.

**Challenge 3: Clang Already Has an Evaluator**

Clang has a compile-time evaluator (`clang::Expr::EvaluateAsInt()`), but:
- It evaluates in the **C++ AST**, not the **C AST**
- Evaluated results are `APValue` (LLVM arbitrary precision values)
- We can reuse this for **simple cases** (literals, arithmetic)
- But **complex cases** (loops, calls) require our own evaluator

**Challenge 4: consteval Guarantees**

`consteval` functions **must** be evaluated at compile-time:
- If we can't evaluate, we must emit a compilation error (not just warning)
- Fallback to runtime violates C++ semantics
- This is a **hard constraint** that limits what we can transpile

### Existing Prototype Analysis

**ConstexprEnhancementHandler** (include/ConstexprEnhancementHandler.h):
- Detects `isConstexpr()` on function declarations
- Attempts simple evaluation via `isSimpleReturnLiteral()`
- Falls back to runtime for complex cases
- **Limitations**: Only handles trivial cases (return 42;)

**ConstevalIfTranslator** (include/ConstevalIfTranslator.h):
- Detects `if consteval` statements
- Emits runtime branch (else clause) by default
- **Limitations**: Doesn't detect compile-time context, always chooses runtime

**Evaluation Attempt**:
```cpp
bool attemptCompileTimeEval(FunctionDecl* FD, Expr::EvalResult& Result, ASTContext& Ctx);
```
- Uses Clang's `EvaluateAsInt()`, `EvaluateAsFloat()`, etc.
- Works for **simple arithmetic** only
- Fails for **control flow** (loops, branches)

### Strategic Decision: Hybrid Approach

Given the complexity, we adopt a **tiered strategy**:

**Tier 1: Compile-Time Evaluation (Simple Cases)**
- Literal returns: `constexpr int answer() { return 42; }`
- Arithmetic expressions: `constexpr int add(int a, int b) { return a + b; }`
- Boolean logic: `constexpr bool check(int x) { return x > 0; }`
- Constant folding: `constexpr int x = 3 + 4;`

**Translation**: Replace with macro or const value.
```c
// C++ Input
constexpr int answer() { return 42; }

// C Output
#define answer() 42
```

**Tier 2: Runtime Fallback (Complex Cases)**
- Loops: `for`, `while`, `do-while`
- Function calls: `constexpr int f() { return g(); }`
- Local variables with non-trivial initialization
- Conditionals: `if`, `switch`

**Translation**: Emit as normal C function.
```c
// C++ Input
constexpr int factorial(int n) {
    int result = 1;
    for (int i = 2; i <= n; ++i) {
        result *= i;
    }
    return result;
}

// C Output (runtime fallback)
int factorial(int n) {
    int result = 1;
    for (int i = 2; i <= n; ++i) {
        result *= i;
    }
    return result;
}
```

**Tier 3: Unsupported (Reject)**
- `consteval` functions (must be compile-time, can't fallback)
- `constexpr` with dynamic allocation (`new`, `delete`)
- `constexpr` with virtual functions (requires runtime polymorphism)
- `constexpr` with exceptions

**Translation**: Emit error, fail transpilation.
```cpp
// C++ Input
consteval int must_be_constexpr(int x) {
    return x * x;
}

// Transpiler Output
ERROR: consteval function 'must_be_constexpr' cannot be transpiled to C.
       C has no compile-time evaluation. Rewrite as constexpr (runtime fallback) or macro.
```

---

## Translation Strategy

### Tier 1: Simple Compile-Time Evaluation

**Pattern 1: Literal Return**

**C++ Input:**
```cpp
constexpr int answer() {
    return 42;
}

int main() {
    constexpr int x = answer();
    int arr[answer()];
}
```

**C Output:**
```c
#define answer() 42

int main(void) {
    const int x = 42;
    int arr[42];
    return 0;
}
```

**Implementation**:
1. Detect `FunctionDecl::isConstexpr()`
2. Check if body is `return <literal>;`
3. Extract literal value
4. Replace function with macro
5. Replace call sites with literal

**Pattern 2: Arithmetic Expression**

**C++ Input:**
```cpp
constexpr int add(int a, int b) {
    return a + b;
}

constexpr int result = add(3, 4);
```

**C Output:**
```c
// Option 1: Macro (if simple)
#define add(a, b) ((a) + (b))

const int result = 7;  // Folded at transpile-time

// Option 2: inline function (if complex)
static inline int add(int a, int b) {
    return a + b;
}

const int result = 7;  // Still folded if possible
```

**Implementation**:
1. Detect constexpr variable initialization
2. Attempt to evaluate using Clang's `EvaluateAsInt()`
3. If successful, replace with literal
4. If failed, emit runtime initialization

**Pattern 3: Boolean Logic**

**C++ Input:**
```cpp
constexpr bool is_positive(int x) {
    return x > 0;
}

if (is_positive(5)) {
    // ...
}
```

**C Output:**
```c
#define is_positive(x) ((x) > 0)

if (1) {  // Folded: is_positive(5) → 5 > 0 → true → 1
    // ...
}
```

**Implementation**:
1. Detect constexpr function with boolean return
2. Check if body is simple comparison
3. Emit as macro
4. Fold call sites if arguments are constants

### Tier 2: Runtime Fallback (Complex Cases)

**Pattern 4: Loop-Based Computation**

**C++ Input:**
```cpp
constexpr int factorial(int n) {
    int result = 1;
    for (int i = 2; i <= n; ++i) {
        result *= i;
    }
    return result;
}

constexpr int fact5 = factorial(5);  // Could be compile-time
int fact_runtime = factorial(n);     // Runtime
```

**C Output:**
```c
// Emit as normal function (runtime)
int factorial(int n) {
    int result = 1;
    for (int i = 2; i <= n; ++i) {
        result *= i;
    }
    return result;
}

// Attempt to evaluate constant initialization
const int fact5 = 120;  // IF we can evaluate, else: factorial(5)
int fact_runtime = factorial(n);
```

**Implementation**:
1. Detect constexpr function with loops
2. Emit as normal C function
3. Attempt constant folding at call sites with constant args
4. Emit warning: "constexpr 'factorial' emitted as runtime function"

**Pattern 5: Recursive Function**

**C++ Input:**
```cpp
constexpr int fibonacci(int n) {
    return n <= 1 ? n : fibonacci(n-1) + fibonacci(n-2);
}

constexpr int fib10 = fibonacci(10);
```

**C Output:**
```c
// Emit as normal function (no inline recursion in macro)
int fibonacci(int n) {
    return n <= 1 ? n : fibonacci(n-1) + fibonacci(n-2);
}

// Attempt compile-time evaluation
const int fib10 = 55;  // IF evaluator can handle recursion, else: fibonacci(10)
```

**Implementation**:
1. Detect constexpr recursive function
2. Emit as normal C function
3. Use Clang's evaluator for constant folding (has recursion limit)
4. If evaluation fails, emit runtime call

### Tier 3: Unsupported Features (Reject)

**Pattern 6: consteval (Always Compile-Time)**

**C++ Input:**
```cpp
consteval int must_be_compile_time(int x) {
    return x * x;
}

constexpr int result = must_be_compile_time(5);  // OK: compile-time context
int runtime = must_be_compile_time(n);  // ERROR in C++: runtime context
```

**Transpiler Behavior:**
```
ERROR: consteval function 'must_be_compile_time' cannot be transpiled.
       Reason: C has no compile-time evaluation guarantees.
       Suggestion: Replace with constexpr (allows runtime fallback) or preprocessor macro.
```

**Implementation**:
1. Detect `FunctionDecl::isConsteval()`
2. Emit error and fail transpilation
3. Document as unsupported feature

**Pattern 7: if consteval**

**C++ Input:**
```cpp
constexpr int compute(int x) {
    if consteval {
        return x * x;  // Compile-time path
    } else {
        return expensive_runtime_computation(x);  // Runtime path
    }
}
```

**C Output (Conservative):**
```c
// Always emit runtime path (else branch)
int compute(int x) {
    // Note: if consteval branch omitted (C has no compile-time context)
    return expensive_runtime_computation(x);
}

// Emit warning
WARNING: 'if consteval' in function 'compute' emits runtime (else) branch.
         Compile-time optimization lost. Consider separate functions.
```

**Implementation**:
1. Detect `if consteval` (IfStmt with consteval condition)
2. Emit else branch only
3. Emit warning about optimization loss
4. Add comment: `/* if consteval branch omitted */`

**Pattern 8: Constexpr Dynamic Allocation (C++20)**

**C++ Input:**
```cpp
constexpr int allocate_and_compute() {
    int* p = new int(42);
    int result = *p;
    delete p;
    return result;
}
```

**Transpiler Behavior:**
```
ERROR: constexpr function 'allocate_and_compute' uses dynamic allocation.
       Reason: C has no compile-time memory allocation.
       Suggestion: Rewrite without dynamic allocation or emit as runtime function.
```

**Implementation**:
1. Detect `new`, `delete` in constexpr function body
2. Emit error (Tier 3: unsupported)
3. OR: Emit warning and fallback to runtime (if user enables permissive mode)

---

## Architecture Design

### Component Overview

```
┌─────────────────────────────────────────────────────────────┐
│                 TranslationOrchestrator                      │
│  (Coordinates constexpr handling)                            │
└────────────┬────────────────────────────────────────────────┘
             │
             ▼
┌─────────────────────────────────────────────────────────────┐
│            ConstexprOrchestrator (NEW)                       │
│  - Detects constexpr/consteval                               │
│  - Determines tier (simple/complex/unsupported)              │
│  - Delegates to appropriate handler                          │
└──┬───────────┬──────────────┬──────────────┬────────────────┘
   │           │              │              │
   ▼           ▼              ▼              ▼
┌────────┐ ┌──────────┐ ┌─────────────┐ ┌────────────────┐
│ Simple │ │ Complex  │ │ Unsupported │ │ ConstevalIf    │
│ Eval   │ │ Runtime  │ │ Rejector    │ │ Translator     │
│ Handler│ │ Fallback │ │             │ │                │
└────────┘ └──────────┘ └─────────────┘ └────────────────┘
```

### Handler Responsibilities

**ConstexprOrchestrator** (NEW):
- **Responsibility**: Analyze constexpr functions/variables, route to tier
- **Input**: FunctionDecl, VarDecl with constexpr
- **Output**: Routing decision (Tier 1/2/3)
- **SOLID**: Single responsibility (routing), delegates actual translation

**SimpleConstexprEvaluator** (NEW):
- **Responsibility**: Evaluate simple constexpr expressions at transpile-time
- **Input**: Constexpr function/variable with simple body
- **Output**: Literal value or macro definition
- **Dependencies**: Clang evaluator (`Expr::EvaluateAsInt()`)
- **SOLID**: Open/closed (extendable to new literal types)

**RuntimeFallbackHandler** (EXISTING: FunctionHandler):
- **Responsibility**: Emit constexpr function as normal C function
- **Input**: Constexpr function that can't be evaluated
- **Output**: C function declaration/definition
- **SOLID**: Dependency inversion (uses CNodeBuilder abstraction)

**UnsupportedConstexprRejector** (NEW):
- **Responsibility**: Detect and reject unsupported constexpr features
- **Input**: FunctionDecl with consteval, dynamic allocation, etc.
- **Output**: Error diagnostic, transpilation failure
- **SOLID**: Fail-fast principle, clear error messages

**ConstevalIfTranslator** (EXISTING, ENHANCE):
- **Responsibility**: Translate `if consteval` to C
- **Current**: Emits runtime branch only
- **Enhancement**: Detect compile-time context, emit both branches with #ifdef
- **SOLID**: Single responsibility (if consteval only)

### Integration with Existing Handlers

**FunctionHandler**:
- Add `isConstexpr()` check in `handleFunctionDecl()`
- Delegate to `ConstexprOrchestrator` if constexpr
- If Tier 2 (fallback), continue normal translation

**VariableHandler**:
- Add `isConstexpr()` check in `handleVarDecl()`
- Attempt compile-time evaluation for initializer
- If successful, emit `const` with literal
- If failed, emit normal variable

**ExpressionHandler**:
- Check if CallExpr is to constexpr function
- Attempt constant folding if arguments are constants
- Replace with literal if successful

---

## Task Breakdown (TDD Approach)

### Group 1: Foundation (Sequential)

**Task 1.1: Create ConstexprOrchestrator** (8 hrs)
- **TDD Steps**:
  1. Write test: `ConstexprOrchestratorTest::DetectSimpleConstexpr`
  2. Implement `detectConstexpr(FunctionDecl*)` → return Tier enum
  3. Test with simple literal return
  4. Test with arithmetic expression
  5. Test with loop (should detect Tier 2)
  6. Test with consteval (should detect Tier 3)
- **Output**: Routing logic for constexpr

**Task 1.2: Create SimpleConstexprEvaluator** (12 hrs)
- **TDD Steps**:
  1. Write test: `SimpleConstexprEvaluatorTest::EvaluateLiteral`
  2. Implement `evaluateToLiteral(FunctionDecl*)` using Clang evaluator
  3. Test integer literal
  4. Test floating-point literal
  5. Test boolean literal
  6. Test string literal
  7. Test arithmetic expression (a + b)
  8. Test comparison (a > b)
- **Output**: Compile-time evaluation for simple cases

**Task 1.3: Create UnsupportedConstexprRejector** (6 hrs)
- **TDD Steps**:
  1. Write test: `UnsupportedConstexprRejectorTest::RejectConsteval`
  2. Implement `rejectIfUnsupported(FunctionDecl*)` → emit error
  3. Test consteval detection
  4. Test dynamic allocation detection (new/delete)
  5. Test virtual function call detection
  6. Test exception throw detection
- **Output**: Clear error messages for unsupported features

**Task 1.4: Enhance ConstevalIfTranslator** (8 hrs)
- **TDD Steps**:
  1. Write test: `ConstevalIfTranslatorTest::EmitRuntimeBranch`
  2. Implement `transform(IfStmt*)` → emit else branch
  3. Test negated if consteval (`if !consteval`)
  4. Test nested if consteval
  5. Add warning emission
  6. Add comment generation
- **Output**: Functional if consteval translation

### Group 2: Constant Folding (Parallel with Group 1)

**Task 2.1: Integrate Clang Evaluator** (10 hrs)
- **TDD Steps**:
  1. Write test: `ClangEvaluatorTest::EvaluateIntExpr`
  2. Implement wrapper for `Expr::EvaluateAsInt()`
  3. Test with literal: `5`
  4. Test with arithmetic: `3 + 4`
  5. Test with variables: `x + 1` (should fail if x not constant)
  6. Test with function call: `f(3)` (should fail if f not constexpr)
  7. Handle `APValue` to literal conversion
- **Output**: Wrapper for Clang's evaluator

**Task 2.2: Implement Macro Generation** (8 hrs)
- **TDD Steps**:
  1. Write test: `MacroGeneratorTest::SimpleFunctionToMacro`
  2. Implement `generateMacro(FunctionDecl*, LiteralValue)` → `#define`
  3. Test with zero-arg function: `#define answer() 42`
  4. Test with one-arg function: `#define square(x) ((x) * (x))`
  5. Test with multi-arg: `#define add(a, b) ((a) + (b))`
  6. Ensure proper parenthesization (avoid macro pitfalls)
  7. Test macro safety (double evaluation issues)
- **Output**: Macro emission for simple constexpr

**Task 2.3: Constant Initialization Folding** (10 hrs)
- **TDD Steps**:
  1. Write test: `ConstantFoldingTest::FoldConstexprVariable`
  2. Implement `foldConstexprInit(VarDecl*)` → literal
  3. Test: `constexpr int x = 42;` → `const int x = 42;`
  4. Test: `constexpr int y = 3 + 4;` → `const int y = 7;`
  5. Test: `constexpr int z = f(5);` → evaluate f if possible
  6. Test failure case: `constexpr int w = runtime();` → error or runtime
  7. Integrate with VariableHandler
- **Output**: Constant variable folding

### Group 3: Runtime Fallback (Sequential after Group 1)

**Task 3.1: Detect Complex Constexpr** (6 hrs)
- **TDD Steps**:
  1. Write test: `ComplexityDetectorTest::DetectLoop`
  2. Implement `isComplexConstexpr(FunctionDecl*)` → bool
  3. Test with for loop
  4. Test with while loop
  5. Test with recursive call
  6. Test with local variable
  7. Test with if statement
- **Output**: Complexity heuristic

**Task 3.2: Emit Runtime Fallback Warning** (4 hrs)
- **TDD Steps**:
  1. Write test: `DiagnosticTest::EmitFallbackWarning`
  2. Implement `emitRuntimeFallbackWarning(FunctionDecl*)`
  3. Test message format
  4. Test source location
  5. Test suppression flag (--no-constexpr-warnings)
- **Output**: User-facing diagnostics

**Task 3.3: Integrate with FunctionHandler** (8 hrs)
- **TDD Steps**:
  1. Write test: `FunctionHandlerTest::ConstexprRuntimeFallback`
  2. Modify `handleFunctionDecl()` to check constexpr
  3. Delegate to ConstexprOrchestrator
  4. If Tier 2, emit normal function
  5. Add comment: `/* constexpr (runtime fallback) */`
  6. Test end-to-end: constexpr → C function
- **Output**: Seamless fallback

### Group 4: Call Site Optimization (Parallel with Group 3)

**Task 4.1: Detect Constant Arguments** (8 hrs)
- **TDD Steps**:
  1. Write test: `ConstantArgumentDetectorTest::DetectIntegerLiteral`
  2. Implement `areAllArgsConstant(CallExpr*)` → bool
  3. Test with literal args: `f(5, 10)`
  4. Test with const variables: `f(constexpr_x, constexpr_y)`
  5. Test with non-const: `f(runtime_var)` → false
  6. Test with mixed: `f(5, runtime_var)` → false
- **Output**: Call site analysis

**Task 4.2: Fold Constant Calls** (10 hrs)
- **TDD Steps**:
  1. Write test: `CallFoldingTest::FoldSimpleCall`
  2. Implement `foldConstexprCall(CallExpr*)` → Expr*
  3. Test: `square(5)` → `25` (if square is constexpr)
  4. Test: `add(3, 4)` → `7`
  5. Test: `factorial(5)` → `120` (if evaluator can handle)
  6. Test: `factorial(10)` → runtime call (if too complex)
  7. Replace CallExpr with IntegerLiteral in AST
- **Output**: Call site constant folding

**Task 4.3: Integrate with ExpressionHandler** (6 hrs)
- **TDD Steps**:
  1. Write test: `ExpressionHandlerTest::ConstexprCallFolding`
  2. Modify `handleCallExpr()` to attempt folding
  3. Check if callee is constexpr
  4. Check if args are constant
  5. Attempt evaluation
  6. Replace with literal if successful
- **Output**: Automatic call site optimization

### Group 5: Comprehensive Testing (Sequential, final stage)

**Task 5.1: Unit Tests** (12 hrs)
- **Coverage**:
  - `ConstexprOrchestratorTest`: Tier detection (10 tests)
  - `SimpleConstexprEvaluatorTest`: Evaluation (15 tests)
  - `UnsupportedConstexprRejectorTest`: Error detection (8 tests)
  - `ConstevalIfTranslatorTest`: if consteval (10 tests)
  - `ConstantFoldingTest`: Variable initialization (12 tests)
  - `CallFoldingTest`: Call site optimization (15 tests)
- **Total**: 70 unit tests

**Task 5.2: Integration Tests** (12 hrs)
- **File**: `tests/integration/handlers/ConstexprIntegrationTest.cpp`
- **Tests** (25 tests):
  - Simple constexpr function → macro
  - Arithmetic constexpr → folding
  - Constexpr variable initialization
  - Loop-based constexpr → runtime fallback
  - Recursive constexpr → runtime or folding
  - if consteval → runtime branch
  - Consteval rejection (should fail transpilation)
  - Constexpr with dynamic allocation → error
  - Constexpr in template (monomorphization)
  - Constexpr in class (static member)
  - Constexpr constructor
  - Constexpr destructor (C++20)
  - Constexpr lambda (C++17)
  - Array size from constexpr
  - Switch case from constexpr
  - Template argument from constexpr
  - Constexpr if (C++17)
  - Constexpr virtual function (C++20)
  - Constexpr new/delete (C++20) → error
  - Constexpr with exceptions → error
  - Constexpr with goto → runtime fallback
  - Constexpr with reinterpret_cast → error
  - Constexpr with inline asm → error
  - Constexpr with volatile → runtime fallback
  - Constexpr with mutable → runtime fallback

**Task 5.3: E2E Tests** (10 hrs)
- **File**: `tests/e2e/phase58/ConstexprE2ETest.cpp`
- **Tests** (10 tests):
  - **ACTIVE**: Simple compile-time constant (sanity check)
  - **DISABLED**: Math library (sqrt, sin, cos) constexpr
  - **DISABLED**: Compile-time string manipulation
  - **DISABLED**: Compile-time JSON parsing (if feasible)
  - **DISABLED**: Compile-time regular expression
  - **DISABLED**: Compile-time sorting algorithm
  - **DISABLED**: Constexpr map/lookup table
  - **DISABLED**: Constexpr type traits simulation
  - **DISABLED**: Constexpr tuple implementation
  - **DISABLED**: Constexpr variant implementation

**Task 5.4: Performance Benchmarks** (6 hrs)
- **File**: `tests/benchmarks/constexpr_benchmark.cpp`
- **Metrics**:
  - Transpilation time (constexpr vs non-constexpr)
  - Runtime performance (folded vs runtime call)
  - Binary size (macro vs function)
  - Compilation time (C compile time)

---

## Execution Strategy

### Timeline

**Week 1: Foundation** (Group 1)
- Day 1-2: ConstexprOrchestrator (Task 1.1)
- Day 3-4: SimpleConstexprEvaluator (Task 1.2)
- Day 5: UnsupportedConstexprRejector (Task 1.3)
- Day 6-7: Enhance ConstevalIfTranslator (Task 1.4)

**Week 2: Constant Folding** (Group 2, parallel)
- Day 1-3: Integrate Clang Evaluator (Task 2.1)
- Day 4-5: Implement Macro Generation (Task 2.2)
- Day 6-7: Constant Initialization Folding (Task 2.3)

**Week 3: Runtime Fallback** (Group 3)
- Day 1-2: Detect Complex Constexpr (Task 3.1)
- Day 3: Emit Runtime Fallback Warning (Task 3.2)
- Day 4-5: Integrate with FunctionHandler (Task 3.3)

**Week 4: Call Site Optimization** (Group 4, parallel with Week 3)
- Day 1-2: Detect Constant Arguments (Task 4.1)
- Day 3-5: Fold Constant Calls (Task 4.2)
- Day 6-7: Integrate with ExpressionHandler (Task 4.3)

**Week 5-6: Comprehensive Testing** (Group 5)
- Week 5 Day 1-3: Unit tests (Task 5.1)
- Week 5 Day 4-7: Integration tests (Task 5.2)
- Week 6 Day 1-3: E2E tests (Task 5.3)
- Week 6 Day 4-5: Performance benchmarks (Task 5.4)

**Week 7: Buffer & Finalization**
- Day 1-3: Bug fixes from testing
- Day 4-5: Documentation
- Day 6-7: Code review, polish

**Total: 80-120 hours (7 weeks at 12-17 hrs/week)**

### Parallelization Opportunities

**Parallel Execution Groups:**

1. **Week 2**: Group 2 (Constant Folding) can run independently after Week 1
2. **Week 3-4**: Group 3 (Runtime Fallback) + Group 4 (Call Site Optimization) in parallel
   - ~40% time savings

**Resource Allocation**:
- Week 1: 1 engineer (foundation)
- Week 2: 1 engineer (folding)
- Week 3-4: 2 engineers (parallel fallback + optimization)
- Week 5-6: 1-2 engineers (testing)
- Week 7: 1 engineer (finalization)

### Deviation Rules

1. **Full Evaluator Too Complex**: Limit to Tier 1 + Tier 2 fallback (no custom evaluator)
2. **Clang Evaluator Insufficient**: Use simpler heuristics (literal detection only)
3. **consteval Must Reject**: No fallback allowed (violates C++ semantics)
4. **if consteval Complexity**: Emit runtime branch only (no compile-time detection)
5. **Performance Regression**: Document overhead, don't block on optimization

---

## Success Criteria

### Functional Requirements

- [ ] Simple constexpr functions → macros or const values
- [ ] Arithmetic constexpr → constant folding
- [ ] Constexpr variables → const with literal initialization
- [ ] Complex constexpr → runtime fallback (emit warning)
- [ ] consteval → error (reject transpilation)
- [ ] if consteval → emit runtime branch
- [ ] Constexpr call sites → fold if args constant
- [ ] Unsupported features → clear error messages

### Quality Requirements

- [ ] All unit tests pass (70 tests, 100%)
- [ ] All integration tests pass (25 tests, 100%)
- [ ] 1 E2E sanity test passes (100%)
- [ ] No regressions in existing tests
- [ ] Code follows SOLID principles
- [ ] TDD followed throughout
- [ ] No compiler warnings
- [ ] Clear diagnostics for fallback/errors

### Performance Requirements

- [ ] Transpilation time overhead < 10% for constexpr-heavy code
- [ ] Folded constants have zero runtime overhead
- [ ] Runtime fallback equivalent to hand-written C
- [ ] Binary size comparable (macros don't bloat excessively)

### Documentation Requirements

- [ ] User guide (what's supported, what's not)
- [ ] API documentation (orchestrator, evaluator)
- [ ] Limitations document (explicit list)
- [ ] Migration guide (constexpr → C patterns)
- [ ] Performance analysis (folding benefits)

---

## Risk Analysis & Mitigation

### Risk 1: Full Evaluation Infeasible (VERY HIGH)

**Impact**: Can't evaluate most constexpr functions
**Probability**: HIGH
**Mitigation**:
- Accept runtime fallback as primary strategy
- Focus on simple cases (Tier 1) only
- Use Clang's evaluator, don't build custom
- Document limitations clearly

### Risk 2: Clang Evaluator Limitations (HIGH)

**Impact**: Can't evaluate even simple cases reliably
**Probability**: MEDIUM
**Mitigation**:
- Fallback to pattern matching (literal detection)
- Emit macros for trivial cases only
- Don't promise full evaluation
- Runtime fallback is always safe

### Risk 3: consteval Rejection Breaks Code (HIGH)

**Impact**: Users can't transpile consteval-heavy codebases
**Probability**: MEDIUM
**Mitigation**:
- Provide clear error messages
- Suggest rewrites (constexpr or macro)
- Document workarounds
- Offer permissive mode (fallback to runtime, violates semantics)

### Risk 4: Macro Safety Issues (MEDIUM)

**Impact**: Generated macros have double-evaluation bugs
**Probability**: MEDIUM
**Mitigation**:
- Always parenthesize macro arguments
- Detect side effects (warn if unsafe)
- Prefer inline functions when feasible
- Test macro expansion thoroughly

### Risk 5: Timeline Overrun (MEDIUM)

**Impact**: Phase extends beyond 120 hours
**Probability**: MEDIUM
**Mitigation**:
- Buffer week (Week 7) for overruns
- Defer advanced features (constexpr lambdas)
- Prioritize correctness over optimization
- Track progress weekly

---

## Strategic Recommendation: Defer or Implement?

### Arguments for Deferring (LOW Priority)

**Pros**:
- Extremely complex (80-120 hours)
- Requires compile-time evaluator (200+ hours for full support)
- Limited user impact (most code doesn't rely on constexpr)
- Runtime fallback is semantically equivalent
- C has no constexpr → users expect limitations

**Cons**:
- Constexpr is increasingly common in modern C++
- Consteval code can't transpile (hard error)
- Optimization opportunities lost
- Competition may support constexpr better

### Arguments for Implementing (Phase 58)

**Pros**:
- Enables transpilation of constexpr-heavy codebases
- Optimization for compile-time constants
- Demonstrates technical capability
- Users expect modern C++ feature support
- Foundation for future enhancements (full evaluator)

**Cons**:
- High complexity-to-value ratio
- Many edge cases and limitations
- May not deliver expected optimization
- Users may expect more than we can deliver

### Recommendation: **IMPLEMENT WITH LIMITED SCOPE**

**Rationale**:
- Implement **Tier 1 (Simple)** + **Tier 2 (Fallback)** fully
- Defer **Tier 3 (Unsupported)** with clear errors
- Do NOT build custom evaluator (use Clang's)
- Focus on **enabling transpilation**, not **optimization**
- Document limitations prominently

**Scope Reduction**:
- Skip constexpr lambdas (defer to Phase 59+)
- Skip constexpr destructors (rare use case)
- Skip constexpr virtual functions (C++20, uncommon)
- Skip constexpr dynamic allocation (unsupported in C)

**Revised Estimate**: 60-80 hours (down from 80-120)

---

## Deliverables Checklist

### Code Deliverables

- [ ] `include/handlers/ConstexprOrchestrator.h` - new file
- [ ] `src/handlers/ConstexprOrchestrator.cpp` - new file
- [ ] `include/handlers/SimpleConstexprEvaluator.h` - new file
- [ ] `src/handlers/SimpleConstexprEvaluator.cpp` - new file
- [ ] `include/handlers/UnsupportedConstexprRejector.h` - new file
- [ ] `src/handlers/UnsupportedConstexprRejector.cpp` - new file
- [ ] `include/ConstevalIfTranslator.h` - enhanced
- [ ] `src/ConstevalIfTranslator.cpp` - enhanced
- [ ] `include/handlers/FunctionHandler.h` - constexpr integration
- [ ] `src/handlers/FunctionHandler.cpp` - constexpr integration
- [ ] `include/handlers/VariableHandler.h` - constexpr variable folding
- [ ] `src/handlers/VariableHandler.cpp` - constexpr variable folding
- [ ] `include/handlers/ExpressionHandler.h` - call folding
- [ ] `src/handlers/ExpressionHandler.cpp` - call folding

### Test Deliverables

- [ ] `tests/unit/handlers/ConstexprOrchestratorTest.cpp` - new file
- [ ] `tests/unit/handlers/SimpleConstexprEvaluatorTest.cpp` - new file
- [ ] `tests/unit/handlers/UnsupportedConstexprRejectorTest.cpp` - new file
- [ ] `tests/unit/handlers/ConstevalIfTranslatorTest.cpp` - new file
- [ ] `tests/unit/handlers/ConstantFoldingTest.cpp` - new file
- [ ] `tests/unit/handlers/CallFoldingTest.cpp` - new file
- [ ] `tests/integration/handlers/ConstexprIntegrationTest.cpp` - new file
- [ ] `tests/e2e/phase58/ConstexprE2ETest.cpp` - new file
- [ ] `tests/benchmarks/constexpr_benchmark.cpp` - new file

### Documentation Deliverables

- [ ] `docs/features/CONSTEXPR.md` - user guide
- [ ] `docs/features/CONSTEXPR-LIMITATIONS.md` - explicit limitations
- [ ] `docs/api/ConstexprOrchestrator.md` - API docs
- [ ] `docs/api/SimpleConstexprEvaluator.md` - API docs
- [ ] `.planning/phases/58-constexpr/PHASE58-PLAN.md` - this file
- [ ] `.planning/phases/58-constexpr/PHASE58-SUMMARY.md` - execution summary
- [ ] `.planning/phases/58-constexpr/LIMITATIONS.md` - comprehensive list
- [ ] `.planning/phases/58-constexpr/MIGRATION-GUIDE.md` - C++ → C patterns

### Build Configuration

- [ ] `CMakeLists.txt` - add new test executables
- [ ] `CMakeLists.txt` - add new handler sources
- [ ] `.github/workflows/ci.yml` - add constexpr tests

---

## Next Steps After Completion

**Phase 59: Variadic Templates** - Extended template support (60-90 hrs)
- Constexpr in variadic templates
- Perfect forwarding with constexpr
- Natural progression from Phase 58

**Alternative: Phase 60+ (Advanced Features)** - Defer
- Concepts, Modules, SFINAE all low priority
- Focus on more impactful features first

---

## Notes & Lessons Learned

### From Existing Prototype

**What Worked Well**:
- `ConstexprEnhancementHandler` structure is sound
- Clang evaluator integration functional for simple cases
- `if consteval` translation pattern correct

**What Needs Improvement**:
- Too ambitious (tried full evaluation)
- No clear tiering (simple vs complex)
- Insufficient error messages for unsupported features
- No systematic testing

### Key Insights

1. **Don't Build a C++ Interpreter**: Use Clang's evaluator or fallback to runtime
2. **Runtime Fallback is Safe**: Semantically equivalent, just slower
3. **consteval is Hard Constraint**: Can't fallback, must reject
4. **Optimization ≠ Correctness**: Focus on enabling transpilation, not optimization

### Recommendations

1. **Start Simple**: Literal return, arithmetic, boolean logic only
2. **Fallback Liberally**: Don't fight complexity, emit runtime code
3. **Document Limitations**: Users expect C limitations
4. **Test Edge Cases**: consteval, dynamic allocation, exceptions

---

## Approval & Sign-Off

**Plan Status**: READY FOR REVIEW
**Estimated Effort**: 60-80 hours (reduced scope)
**Recommended Team Size**: 1-2 engineers
**Timeline**: 6-7 weeks at 10-13 hrs/week
**Priority**: LOW (defer if higher priorities exist)

**Recommendation**: APPROVE with reduced scope (Tier 1 + Tier 2 only)

**Next Action**: Obtain approval and begin Week 1 (Foundation)

---

**END OF PHASE 58 PLAN**

# Phase 8 Plan: Standalone Function Translation (v2.1.0)

**Phase**: 8 of 17
**Roadmap**: `../.planning/ROADMAP.md`
**Brief**: `../.planning/BRIEF.md`
**Target Version**: v2.1.0
**Status**: PENDING
**Priority**: CRITICAL (Tier 1 - Blocking basic usage)
**Prerequisite**: None (independent)

## Phase Goal

Enable translation of standalone functions (non-member functions) including function declarations, definitions, overloading, function calls, and the `main()` function. Currently, the transpiler only translates class methods—free functions are silently skipped, blocking most C++ programs.

## Business Value

Standalone functions are fundamental to C++ and required for:
- Entry point (`main()` function)
- Utility functions and algorithms
- Global callback functions
- Functional programming patterns
- Standard library integration

**Impact**: Without this phase, the transpiler cannot translate any practical C++ program.

## Deliverables

### Source Code
- [ ] Enhanced `CppToCVisitor::VisitFunctionDecl` (currently RAII analysis only)
- [ ] Function signature translation logic
- [ ] Function body translation (reuse existing statement translator)
- [ ] Function call translation in `VisitCallExpr`
- [ ] Name mangling for overloaded standalone functions
- [ ] Main function special handling

### Tests
- [ ] `tests/StandaloneFunctionTranslationTest.cpp` (12+ tests)
  - Simple function declaration and definition
  - Function with parameters and return type
  - Multiple overloaded functions (name mangling)
  - Function pointers (forward declarations)
  - Recursive functions
  - `main()` function translation
  - Function calls (direct, through pointers, through references)
  - Variable argument functions (variadic)
  - Inline functions
  - Static standalone functions (internal linkage)
  - Extern standalone functions (external linkage)
  - Function declarations without definitions (forward declarations)

### CLI Integration
- [ ] Add `--enable-standalone-functions={off,on}` flag (default: on)

### Documentation
- [ ] Update `docs/CHANGELOG.md` for v2.1.0
- [ ] Update `README.md` with standalone function feature
- [ ] Update `website/src/pages/features.astro`
- [ ] Create `docs/examples/standalone-functions.md` with C++ → C translation examples

### Release
- [ ] Git-flow release v2.1.0
- [ ] Tag on GitHub with release notes

## Technical Design

### C++ → C Translation Mapping

#### 1. Simple Function Declaration and Definition

**C++**:
```cpp
int add(int a, int b) {
  return a + b;
}
```

**C** (Generated):
```c
/*@ requires \valid(\result);
  @ ensures \result == a + b;
  @*/
int add(int a, int b) {
  return a + b;
}
```

#### 2. Function with Pointer Return

**C++**:
```cpp
void* allocate(size_t size) {
  return malloc(size);
}
```

**C** (Generated):
```c
/*@ requires \valid(\result);
  @ ensures \fresh(\result, size);
  @*/
void* allocate(size_t size) {
  return malloc(size);
}
```

#### 3. Overloaded Functions (Name Mangling)

**C++**:
```cpp
int max(int a, int b) {
  return a > b ? a : b;
}

double max(double a, double b) {
  return a > b ? a : b;
}
```

**C** (Generated):
```c
int max_int_int(int a, int b) {
  return a > b ? a : b;
}

double max_double_double(double a, double b) {
  return a > b ? a : b;
}
```

#### 4. Function Pointers

**C++**:
```cpp
typedef int (*FuncPtr)(int, int);

int apply(FuncPtr f, int a, int b) {
  return f(a, b);
}
```

**C** (Generated):
```c
typedef int (*FuncPtr)(int, int);

int apply(int (*f)(int, int), int a, int b) {
  return (*f)(a, b);
}
```

#### 5. Recursive Functions

**C++**:
```cpp
int factorial(int n) {
  if (n <= 1) return 1;
  return n * factorial(n - 1);
}
```

**C** (Generated):
```c
/*@ requires n > 0;
  @ ensures \result > 0;
  @ decreases n;
  @*/
int factorial(int n) {
  if (n <= 1) return 1;
  return n * factorial(n - 1);
}
```

#### 6. Main Function

**C++**:
```cpp
int main(int argc, char* argv[]) {
  std::cout << "Hello, World!\n";
  return 0;
}
```

**C** (Generated):
```c
int main(int argc, char* argv[]) {
  printf("Hello, World!\n");
  return 0;
}
```

#### 7. Function Calls

**C++**:
```cpp
int result = add(5, 3);              // Direct call
int (*fp)(int, int) = &add;          // Function pointer
int result2 = fp(5, 3);              // Call through pointer
```

**C** (Generated):
```c
int result = add(5, 3);              // Direct call
int (*fp)(int, int) = &add;          // Function pointer
int result2 = (*fp)(5, 3);           // Call through pointer (dereference)
```

#### 8. Static Functions (Internal Linkage)

**C++**:
```cpp
static int internal_helper(int x) {
  return x * 2;
}

int process(int x) {
  return internal_helper(x);
}
```

**C** (Generated):
```c
static int internal_helper(int x) {
  return x * 2;
}

int process(int x) {
  return internal_helper(x);
}
```

#### 9. Extern Functions (External Linkage)

**C++**:
```cpp
extern int external_func(int a);

int wrapper(int a) {
  return external_func(a);
}
```

**C** (Generated):
```c
extern int external_func(int a);

int wrapper(int a) {
  return external_func(a);
}
```

#### 10. Variadic Functions

**C++**:
```cpp
#include <cstdarg>

int sum(int count, ...) {
  va_list args;
  va_start(args, count);
  int total = 0;
  for (int i = 0; i < count; ++i) {
    total += va_arg(args, int);
  }
  va_end(args);
  return total;
}
```

**C** (Generated):
```c
#include <stdarg.h>

int sum(int count, ...) {
  va_list args;
  va_start(args, count);
  int total = 0;
  for (int i = 0; i < count; ++i) {
    total += va_arg(args, int);
  }
  va_end(args);
  return total;
}
```

### Key Features

1. **Function Signature Translation**
   - Return type translation (including pointers and references)
   - Parameter translation (including default values removal in C)
   - Const/volatile qualifier handling
   - Linkage preservation (static, extern)

2. **Function Body Translation**
   - Reuse existing statement translator
   - Local variable declarations
   - Return statement handling
   - Control flow (if/while/for/switch)

3. **Function Call Translation**
   - Direct calls: `f(a, b)` → `f(a, b)`
   - Function pointer calls: `f(a, b)` where `f` is a pointer → `(*f)(a, b)`
   - Method calls on objects (handled by method translator)
   - Implicit conversions for parameter types

4. **Name Mangling for Overloading**
   - Use existing `NameMangler::mangleName()` infrastructure
   - Pattern: `functionName_paramType1_paramType2`
   - Handle type names: `int`, `double`, `void*`, `struct Point`, etc.
   - Track used names to avoid collisions

5. **Main Function Special Handling**
   - Detect `main()` function
   - Preserve signature: `int main(int argc, char* argv[])`
   - Translate body normally
   - Set as entry point

6. **Static Initialization Order**
   - Track function dependencies (which functions call which)
   - For standalone functions, unlike global variables, no special handling needed
   - Calls resolved at link time

### Architecture

```
CppToCVisitor
├── VisitFunctionDecl(FunctionDecl *FD)
│   ├── Skip if CXXMethodDecl (handled by VisitCXXMethodDecl)
│   ├── Skip if no body (forward declaration)
│   ├── Handle name mangling for overloads
│   ├── Translate function signature
│   ├── Translate function body (statement translator)
│   └── Register in function registry
│
├── VisitCallExpr(CallExpr *CE)
│   ├── Detect function pointer calls
│   ├── Translate to dereference if needed
│   ├── Translate arguments
│   └── Return function call expression
│
├── VisitDeclRefExpr (existing, may need enhancement)
│   └── For function references (function pointers)
│
└── NameMangler (existing infrastructure)
    ├── mangleName(FunctionDecl *FD)
    ├── getSimpleTypeName(QualType QT)
    └── usedNames tracking
```

### Implementation Steps

#### Step 1: Extend NameMangler for Standalone Functions
- Add `mangleFunction(FunctionDecl *FD)` method
- Pattern: `namespace_functionName_paramType1_paramType2`
- Reuse existing type name generation

#### Step 2: Enhance VisitFunctionDecl
- Keep existing RAII analysis (lines 523-610)
- Add code generation for non-method functions:
  - Check if `CXXMethodDecl` (skip if yes)
  - Check if has body (skip forward declarations)
  - Get mangled name from NameMangler
  - Translate signature: return type, parameters
  - Translate body using existing statement translator
  - Store function in registry

#### Step 3: Enhance VisitCallExpr
- Detect function calls on function pointers
- Check if callee is UnaryOperator with dereference
- For pointer calls, wrap in dereference: `(*fp)(args)`
- For direct calls, translate directly

#### Step 4: Handle Main Function
- Detect when function is named "main"
- Preserve special signature
- No name mangling
- Translate body normally

#### Step 5: Create Test Suite
- 12+ tests covering all scenarios above
- Unit tests for NameMangler enhancements
- Integration tests for function translation

### Dependencies

**Internal**:
- Existing `NameMangler.cpp` (enhances with standalone function support)
- Existing statement translator (reuse for function body)
- Existing type translator (reuse for parameters/return)

**External**:
- None new (uses existing Clang LibTooling)

## Test Cases (12+)

### Test 1: SimpleFunctionDeclaration
**Input**:
```cpp
int add(int a, int b) { return a + b; }
```
**Expected**: C function with correct signature and body
**Verification**: Compiles, returns correct values

### Test 2: FunctionWithPointerReturn
**Input**:
```cpp
int* allocate(int size) { return new int[size]; }
```
**Expected**: C function returning pointer
**Verification**: Type signature correct, pointer arithmetic works

### Test 3: OverloadedFunctions
**Input**:
```cpp
int max(int a, int b) { return a > b ? a : b; }
double max(double a, double b) { return a > b ? a : b; }
```
**Expected**: Two functions with mangled names (`max_int_int`, `max_double_double`)
**Verification**: Both compile, calls resolve to correct function

### Test 4: FunctionPointerCall
**Input**:
```cpp
int apply(int (*f)(int), int x) { return f(x); }
int square(int x) { return x * x; }
// Later: apply(square, 5);
```
**Expected**: Function pointer call translates to `(*f)(x)`
**Verification**: Correct dereference syntax generated

### Test 5: RecursiveFunction
**Input**:
```cpp
int factorial(int n) {
  return n <= 1 ? 1 : n * factorial(n - 1);
}
```
**Expected**: Recursive call to self works
**Verification**: factorial(5) = 120

### Test 6: MainFunction
**Input**:
```cpp
int main(int argc, char* argv[]) { return 0; }
```
**Expected**: `main` function preserved (no name mangling)
**Verification**: Correct signature, no name mangling applied

### Test 7: DirectFunctionCall
**Input**:
```cpp
int add(int a, int b) { return a + b; }
int main() { int result = add(3, 4); return result; }
```
**Expected**: Direct call `add(3, 4)` translates correctly
**Verification**: Result = 7

### Test 8: VariadicFunction
**Input**:
```cpp
int sum(int count, ...) { /* va_list handling */ }
```
**Expected**: Variadic signature preserved
**Verification**: Compiles with `...` syntax

### Test 9: InlineFunction
**Input**:
```cpp
inline int abs(int x) { return x < 0 ? -x : x; }
```
**Expected**: `inline` keyword preserved
**Verification**: Inlining hints preserved

### Test 10: StaticFunction
**Input**:
```cpp
static int helper(int x) { return x * 2; }
int process(int x) { return helper(x); }
```
**Expected**: `static` keyword preserved for internal linkage
**Verification**: Function not exported in generated header

### Test 11: ExternFunction
**Input**:
```cpp
extern int external_func(int a);
int wrapper(int a) { return external_func(a); }
```
**Expected**: `extern` keyword preserved
**Verification**: Function declaration preserved without body

### Test 12: FunctionReferenceThroughPointer
**Input**:
```cpp
int add(int a, int b) { return a + b; }
int (*fp)(int, int) = &add;
int result = fp(3, 4);  // Call through pointer
```
**Expected**: Function reference creates pointer, call dereferences
**Verification**: `&add` works, `fp(...)` translates to `(*fp)(...)`

### Test 13+: Integration Tests (3+ additional)
- Mutually recursive functions
- Function overloading with different parameter counts
- Function parameter forwarding
- Return type deduction (auto) - if applicable
- Lambdas calling standalone functions - (if integrated with Phase 10)

## Implementation Tasks

### Task 1: Analyze Current State (Checkpoint: Understanding)
**Duration**: Research
**Actions**:
- [ ] Review `CppToCVisitor::VisitFunctionDecl` (line 523+)
- [ ] Review `NameMangler.cpp` for existing infrastructure
- [ ] Check `VisitCallExpr` implementation
- [ ] Check function registry mechanism
**Verification**: Document current state and gaps

### Task 2: Extend NameMangler for Standalone Functions (Checkpoint: Infrastructure)
**Duration**: Development + Testing
**Actions**:
- [ ] Add `std::string mangleFunction(FunctionDecl *FD)` method
- [ ] Add `bool isMangledNameRequired(FunctionDecl *FD)` to detect overloads
- [ ] Pattern: `functionName_paramType1_paramType2_..._returnType`
- [ ] Reuse `getSimpleTypeName()` for type names
- [ ] Write unit tests for name mangling
**Verification**: 5+ unit tests pass, no collisions in test suite

### Task 3: Implement Function Signature Translation (Checkpoint: Signature)
**Duration**: Development + Testing
**Actions**:
- [ ] Create `std::string translateFunctionSignature(FunctionDecl *FD)`
- [ ] Handle return type translation
- [ ] Handle parameter translation (remove defaults)
- [ ] Handle linkage keywords (static, extern, inline)
- [ ] Handle const/volatile qualifiers
- [ ] Write unit tests
**Verification**: 3+ unit tests pass, signatures match expected C

### Task 4: Enhance VisitFunctionDecl for Code Generation (Checkpoint: CodeGen)
**Duration**: Development + Testing
**Actions**:
- [ ] Keep existing RAII analysis (lines 523-610)
- [ ] Add check: skip if `CXXMethodDecl` (already done)
- [ ] Add check: skip if no body (forward declaration)
- [ ] Get mangled name: `Mangler.mangleFunction(FD)`
- [ ] Get translated signature: `translateFunctionSignature(FD)`
- [ ] Translate body: reuse statement translator
- [ ] Store in function registry
- [ ] Generate ACSL contracts (if annotator available)
- [ ] Log generated functions
**Verification**: 4+ unit tests pass

### Task 5: Enhance VisitCallExpr for Function Calls (Checkpoint: FunctionCalls)
**Duration**: Development + Testing
**Actions**:
- [ ] Analyze current `VisitCallExpr` implementation
- [ ] Detect function pointer calls (callee is dereference)
- [ ] For direct calls: translate normally
- [ ] For pointer calls: wrap with `(*)`
- [ ] Translate arguments
- [ ] Handle implicit conversions (if needed)
- [ ] Write unit tests
**Verification**: 3+ unit tests pass

### Task 6: Handle Main Function Special Case (Checkpoint: Main)
**Duration**: Development + Testing
**Actions**:
- [ ] Detect function name == "main"
- [ ] Skip name mangling for main
- [ ] Preserve signature: `int main(int argc, char* argv[])`
- [ ] Translate body normally
- [ ] Write unit tests
**Verification**: 2+ unit tests pass

### Task 7: Create Comprehensive Test Suite (Checkpoint: Tests)
**Duration**: Testing
**Actions**:
- [ ] Implement all 12+ test cases above
- [ ] Add integration tests (3+ more)
- [ ] Test name mangling for overloads
- [ ] Test function pointers
- [ ] Test recursive calls
- [ ] Test main() function
- [ ] Measure code coverage (target: ≥95%)
**Verification**: 15+ tests pass, ≥95% code coverage

### Task 8: CLI Integration (Checkpoint: CLI)
**Duration**: Development
**Actions**:
- [ ] Add `--enable-standalone-functions={off,on}` flag
- [ ] Default: `on` (enabled)
- [ ] Integrate with existing CLI framework
- [ ] Document in help text
**Verification**: Flag parses correctly, affects transpilation

### Task 9: Update Documentation (Checkpoint: Docs)
**Duration**: Documentation
**Actions**:
- [ ] Update `CHANGELOG.md` for v2.1.0
- [ ] Update `README.md` with feature
- [ ] Update `website/src/pages/features.astro`
- [ ] Create `docs/examples/standalone-functions.md` with 5+ examples
- [ ] Add C++ → C translation examples
- [ ] Document CLI flag
**Verification**: Documentation complete and accurate

### Task 10: Code Review & Optimization (Checkpoint: Quality)
**Duration**: Review
**Actions**:
- [ ] Run all linters (clang-format, clang-tidy, etc.)
- [ ] Fix all warnings (zero tolerance)
- [ ] Review code for SOLID principles adherence
- [ ] Optimize hot paths if needed
- [ ] Performance benchmark (target: <5% transpilation time overhead)
**Verification**: All linters pass, performance acceptable

### Task 11: Git-Flow Release (Checkpoint: Release)
**Duration**: Release
**Actions**:
- [ ] Create git-flow release branch: `release/v2.1.0`
- [ ] Ensure all tests pass
- [ ] Commit version bump
- [ ] Merge to main and develop
- [ ] Tag: `v2.1.0`
- [ ] Push to GitHub
- [ ] Create release notes
**Verification**: GitHub release created with notes

## Verification Steps

### Pre-Implementation Verification
1. [ ] Review `CppToCVisitor::VisitFunctionDecl` source (line 523+)
2. [ ] Review `NameMangler.cpp` infrastructure
3. [ ] Review `VisitCallExpr` implementation
4. [ ] Document gap analysis
5. [ ] Estimate implementation complexity

### Unit Test Verification (Run After Task 4)
```bash
ctest -R StandaloneFunctionTranslationTest --verbose
```
**Expected**: All 12+ tests PASS

### Integration Test Verification (Run After Task 5)
```bash
# Test with real C++ program
./cpptoc examples/standalone_functions.cpp --output examples/standalone_functions.c
gcc examples/standalone_functions.c -o examples/standalone_functions
./examples/standalone_functions
# Expected: Program runs correctly
```

### CLI Verification (Run After Task 8)
```bash
./cpptoc --help | grep -i "standalone"
./cpptoc input.cpp --enable-standalone-functions=off --output output.c
# Expected: Flag accepted, transpilation controlled
```

### Documentation Verification (Run After Task 9)
```bash
# Check files exist and are complete
ls -la docs/examples/standalone-functions.md
grep "standalone" README.md
grep "standalone" website/src/pages/features.astro
```
**Expected**: All files updated with feature information

### Performance Verification (Run After Task 10)
```bash
# Measure transpilation time with/without standalone functions
time ./cpptoc large_program.cpp --enable-standalone-functions=on
time ./cpptoc large_program.cpp --enable-standalone-functions=off
# Expected: <5% overhead from standalone function feature
```

### Final Verification (Release Readiness)
```bash
# All checks
cmake --build . --target test  # All tests pass
clang-format --dry-run src/*.cpp include/*.h  # Format check
clang-tidy src/CppToCVisitor.cpp -- -I include  # Linting
git flow release finish v2.1.0  # Release workflow
git push origin main develop v2.1.0  # Push to GitHub
```
**Expected**: All checks pass, release created

## Success Criteria

### Functional Requirements
- [ ] `main()` function translates correctly (preserves no name mangling)
- [ ] Free functions with same name (overloading) translate with unique names
- [ ] Function calls resolve correctly (direct and through pointers)
- [ ] Linkage preserved (static, extern, inline keywords maintained)
- [ ] Function pointers work (address-of, dereference in calls)

### Quality Requirements
- [ ] 12+ standalone function tests pass (100%)
- [ ] Code coverage ≥95% for new code
- [ ] All linters pass (zero warnings)
- [ ] No performance regression (≤5% transpilation time overhead)
- [ ] Strong typing enforced (100%)

### Documentation Requirements
- [ ] CHANGELOG.md updated for v2.1.0
- [ ] README.md mentions standalone functions
- [ ] website/src/pages/features.astro updated
- [ ] docs/examples/standalone-functions.md with 5+ examples

### Integration Requirements
- [ ] Function translation integrates with existing statement translator
- [ ] Function calls work with existing expression translator
- [ ] Name mangling compatible with existing method name mangling
- [ ] Compatible with ACSL annotator (if enabled)
- [ ] Compatible with Phase 9 (virtual methods)

## Risk Assessment

### Technical Risks
| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Name collision in mangling | High | Medium | Track used names, comprehensive testing |
| Function pointer dereference bugs | Medium | Medium | Extensive testing of pointer scenarios |
| Static initialization order | Medium | Low | Functions resolved at link time (no issue) |
| Performance regression | Medium | Medium | Profile and optimize hot paths |

### Integration Risks
| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Conflicts with method translation | Medium | Low | Already separate code paths (VisitCXXMethodDecl) |
| ACSL annotation issues | Low | Low | Use existing annotator infrastructure |
| Overload mangling incompatible | Medium | Medium | Test all combinations extensively |

## Success Definition

This phase is **COMPLETE** when:

1. **Functionality**
   - `main()` function translates without name mangling
   - Overloaded functions translate with unique mangled names
   - Function calls work (direct and through pointers)
   - Linkage keywords preserved (static, extern, inline)

2. **Testing**
   - 15+ tests pass (12 base + 3 integration)
   - ≥95% code coverage
   - Integration with real C++ programs succeeds

3. **Code Quality**
   - Zero linting errors
   - No performance regression (≤5% overhead)
   - SOLID principles followed

4. **Documentation**
   - CHANGELOG.md updated
   - README.md mentions feature
   - Website features page updated
   - Examples document with 5+ examples

5. **Release**
   - Git-flow release v2.1.0 complete
   - GitHub release tagged and documented
   - Ready for Phase 9 (Virtual Methods)

## Dependencies

**Does NOT depend on**:
- Phase 6 (Memory Predicates) - independent ACSL feature
- Phase 7 (ACSL Integration) - optional enhancement
- Phase 9 (Virtual Methods) - independent C++ feature
- Phase 10 (Lambda Expressions) - lambdas build on standalone functions

**CAN run in parallel with**:
- Phase 6 (Memory Predicates)
- Phase 7 (ACSL Integration)
- Phase 9 (Virtual Methods)
- Phase 11 (Template Integration)
- Phase 12 (Exception Handling)
- Phase 13 (RTTI Integration)

**BLOCKS**:
- Phase 10 (Lambda Expressions) - depends on this for function generation

## Next Steps

1. **Immediate**: Review current `VisitFunctionDecl` (Task 1)
2. **Short-term**: Implement NameMangler extension (Task 2)
3. **Core work**: Enhance VisitFunctionDecl and VisitCallExpr (Tasks 3-5)
4. **Validation**: Create comprehensive test suite (Task 7)
5. **Release**: CLI integration and git-flow release (Tasks 8-11)

## Related Documents

- **ROADMAP.md**: Phase 8 overview (line 285-322)
- **BRIEF.md**: Project brief for C++ feature work
- **CppToCVisitor.cpp**: Core translation logic (line 523+)
- **NameMangler.cpp**: Name mangling infrastructure
- **Phase 6 PLAN.md**: Reference for PLAN format and structure
- **Phase 9 PLAN.md**: Next phase (Virtual Methods)

## Rollback Strategy

If critical issues encountered:
1. Revert to previous version (git reset --hard)
2. File GitHub issue with bug report
3. Plan fix in separate branch
4. Re-test before re-release

## Appendix: Glossary

| Term | Definition |
|------|-----------|
| Standalone function | Non-member function (free function) |
| Name mangling | Encoding function name with parameter types for overloading support |
| Linkage | External vs. static (internal) visibility |
| Function pointer | Pointer to function (callable through dereference) |
| RAII | Resource Acquisition Is Initialization (C++ pattern) |
| Forward declaration | Function declaration without body |
| Variadic function | Function accepting variable number of arguments (...) |


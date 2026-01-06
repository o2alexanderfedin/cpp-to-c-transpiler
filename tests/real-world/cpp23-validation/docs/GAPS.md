# Known Limitations and Gaps

**Project**: Hupyy C++ to C Transpiler
**Document Type**: Technical Limitations Analysis
**Last Updated**: December 24, 2025
**Related**: [FEATURE-MATRIX.md](FEATURE-MATRIX.md), [ROADMAP.md](ROADMAP.md)

---

## Executive Summary

This document catalogs the known limitations, architectural constraints, and gaps in C++23 feature support for the Hupyy C++ to C transpiler. Understanding these gaps is critical for setting realistic expectations and prioritizing future development.

### Current State
- **C++23 Support**: 0-5% (baseline not yet established)
- **C++20 Support**: 15-20%
- **C++11 Support**: 70-75%
- **Primary Target**: C++98/03 features (85-90% support)

### Key Finding
**The transpiler currently outputs C++ code with modern features still present, not valid C99 code.** This is a fundamental architectural gap affecting all C++11+ features.

---

## Architectural Constraints

### 1. Compile-Time vs Runtime Boundary

**Constraint**: The transpiler operates on the AST (Abstract Syntax Tree) after Clang has parsed C++, but cannot execute compile-time code.

**Impact**:
- ❌ `constexpr` functions cannot be evaluated at transpile-time
- ❌ `consteval` immediate functions not supported
- ❌ `if consteval` cannot be resolved
- ❌ Template metaprogramming limited to basic substitution
- ❌ `static_assert` with computed values may fail

**Why This Matters**: C++ has a powerful compile-time execution model. C has no equivalent. We can only convert compile-time C++ constructs to runtime C code, losing optimization opportunities.

**Example**:
```cpp
// C++23
constexpr int square(int x) { return x * x; }
constexpr int result = square(5);  // Evaluated at compile-time

// Transpiled C (current)
int square_constexpr(int x) { return x * x; }
int result = square_constexpr(5);  // Evaluated at runtime (worse performance)
```

**Workaround**: None for true compile-time execution. Can convert to runtime code but loses performance benefits.

---

### 2. Type System Complexity

**Constraint**: C++23's type system is vastly more expressive than C99. No direct mapping exists for many features.

**Impact**:
- ❌ Concepts (C++20/23) - no C equivalent
- ❌ Type constraints on templates
- ❌ `auto` type deduction for complex cases (lambdas, structured bindings)
- ❌ `decltype` in all contexts
- ⚠️ Template specialization (partial support)

**Why This Matters**: C has no generic programming model. We use monomorphization (generate concrete function for each template instantiation), but this doesn't scale to advanced template features.

**Example**:
```cpp
// C++23 with concepts
template<std::integral T>
T add(T a, T b) { return a + b; }

// No C equivalent - concepts don't exist
// Best we can do: generate separate functions per type
int add_int(int a, int b) { return a + b; }
long add_long(long a, long b) { return a + b; }
```

**Workaround**: Manual monomorphization works for simple templates. Complex template metaprogramming requires manual refactoring.

---

### 3. Object Model Mismatch

**Constraint**: C++ has a rich object model (classes, inheritance, polymorphism). C has only structs.

**Impact**:
- ⚠️ Classes → structs with function pointers (vtables)
- ⚠️ Virtual inheritance (complex offset calculations)
- ❌ Explicit object parameters (`this` deduction, P0847R7)
- ❌ Multiple inheritance with virtual bases (some edge cases)
- ⚠️ RTTI (typeid, dynamic_cast) - runtime overhead

**Why This Matters**: We can emulate C++ objects using vtables, but C++23's advanced object features (like deducing `this`) have no clean C mapping.

**Example**:
```cpp
// C++23 - Deducing this (P0847R7)
struct Container {
    template<typename Self>
    auto&& get(this Self&& self, int index) {
        return std::forward<Self>(self).data[index];
    }
};

// C - Cannot represent
// Would need separate functions for const/non-const/rvalue cases
struct Container {
    int* data;
};
int* Container_get(struct Container* self, int index);
const int* Container_get_const(const struct Container* self, int index);
```

**Workaround**: Manual expansion into separate const/non-const/rvalue functions.

---

### 4. Operator Overloading Limitations

**Constraint**: C has no operator overloading. We convert to named functions.

**Impact**:
- ❌ Multi-argument `operator[]` (C++23, P2128R6)
- ❌ Static `operator()` (C++23, P1169R4)
- ❌ Static `operator[]` (C++23)
- ❌ Spaceship operator `<=>` (C++20)
- ⚠️ Basic operators (+, -, *, /) converted to functions

**Why This Matters**: C++23 adds new operator overloading capabilities that have no function-based equivalent in C.

**Example**:
```cpp
// C++23 - Multidimensional subscript
struct Matrix {
    int& operator[](int row, int col);  // Two arguments!
};
Matrix m;
m[1, 2] = 42;

// C - Cannot represent comma operator in subscript
// Must use function call
struct Matrix { int* data; int cols; };
void Matrix_set(struct Matrix* m, int row, int col, int value) {
    m->data[row * m->cols + col] = value;
}
Matrix_set(&m, 1, 2, 42);  // Much less ergonomic
```

**Workaround**: Convert to named functions, but loses syntactic sugar.

---

### 5. Standard Library Dependency

**Constraint**: The transpiler does not transpile the C++ Standard Library (STL).

**Impact**:
- ❌ `std::expected` (C++23)
- ❌ `std::mdspan` (C++23)
- ❌ Ranges library (C++20/23)
- ❌ Format library (C++20)
- ❌ Any `#include <...>` from STL

**Why This Matters**: Many C++23 tests use STL types. Without STL transpilation, these tests cannot run.

**Example**:
```cpp
// C++23
#include <expected>
std::expected<int, Error> divide(int a, int b) {
    if (b == 0) return std::unexpected(Error::DivByZero);
    return a / b;
}

// C - No std::expected equivalent
// Must manually implement error handling
struct DivideResult {
    int value;
    int error_code;
    bool has_error;
};
struct DivideResult divide(int a, int b) {
    if (b == 0) return (struct DivideResult){0, 1, true};
    return (struct DivideResult){a / b, 0, false};
}
```

**Workaround**: Manually implement STL-equivalent types in C, or avoid STL dependencies.

---

## Feature-Specific Gaps

### C++23 Language Features

#### 1. Deducing This (P0847R7)
**Status**: ❌ Not Supported
**Tests**: 0/22 passing
**Gap**: Requires explicit object parameter syntax which has no C equivalent

**Technical Barrier**:
- C++23 allows `this` to be deduced as template parameter
- Enables perfect forwarding of `*this` without code duplication
- C has no equivalent mechanism

**Example Problem**:
```cpp
struct S {
    template<typename Self>
    auto&& value(this Self&& self) { return std::forward<Self>(self).m; }
};
```

**Workaround**: Manually write const/non-const/rvalue overloads (3x code duplication).

---

#### 2. if consteval (P1938R3)
**Status**: ❌ Not Supported
**Tests**: 0/13 passing
**Gap**: Compile-time branch selection not implementable in C

**Technical Barrier**:
- Requires compile-time evaluation to choose branch
- C has no compile-time execution model
- Cannot emit runtime equivalent without performance loss

**Example Problem**:
```cpp
constexpr int f() {
    if consteval {
        return compile_time_calculation();  // Only in constexpr context
    } else {
        return runtime_calculation();       // Only at runtime
    }
}
```

**Workaround**: None. Feature fundamentally incompatible with C.

---

#### 3. Multidimensional Subscript Operator (P2128R6)
**Status**: ❌ Not Supported
**Tests**: 0/16 passing
**Gap**: C's subscript operator `[]` accepts only one argument

**Technical Barrier**:
- C++23: `operator[](T1 t1, T2 t2, ...)`
- C: Only `array[index]` with single index
- No variadic subscript in C

**Example Problem**:
```cpp
struct Matrix {
    int& operator[](int row, int col) { return data[row][col]; }
};
Matrix m;
m[1, 2] = 42;  // C++23: valid
// C: No equivalent syntax
```

**Workaround**: Convert to function calls like `Matrix_at(&m, 1, 2)`.

---

#### 4. Static operator() and operator[] (P1169R4)
**Status**: ❌ Not Supported
**Tests**: 0/8 passing
**Gap**: C has no operator overloading, let alone static operators

**Technical Barrier**:
- C++23 allows `static operator()` for stateless callable objects
- C has no member functions, no static member functions
- Conversion to free functions possible but loses semantics

**Example Problem**:
```cpp
struct Multiplier {
    static int operator()(int a, int b) { return a * b; }
};
Multiplier::operator()(3, 4);  // C++23: static call
// C: No equivalent
```

**Workaround**: Convert to free function `Multiplier_call(3, 4)`.

---

#### 5. auto(x) and auto{x} Decay-Copy (P0849R8)
**Status**: ⚠️ Partial Support
**Tests**: 0/22 passing (untested)
**Gap**: Basic `auto` works, but decay-copy semantics not implemented

**Technical Barrier**:
- `auto(x)` should decay and copy `x`
- `auto{x}` should decay and direct-initialize
- Our `auto` type deduction may not handle all decay cases

**Example Problem**:
```cpp
int arr[5];
auto x = arr;     // x is int*
auto(y) = arr;    // y should be int* (decay-copy)
auto{z} = arr;    // z should be int* (decay-init)
```

**Workaround**: Explicit type annotations when decay is critical.

---

#### 6. Constexpr Enhancements (C++23)
**Status**: ❌ Not Supported
**Tests**: 0/19 passing
**Gap**: No compile-time execution engine

**Technical Barrier**:
- C++23 expands `constexpr` to more contexts (destructors, allocation, etc.)
- We cannot evaluate `constexpr` at transpile-time
- All `constexpr` becomes runtime code

**Example Problem**:
```cpp
constexpr std::vector<int> v = {1, 2, 3};  // C++23: compile-time vector
// C: No compile-time containers, must use runtime code
```

**Workaround**: Accept runtime evaluation (performance loss).

---

#### 7. [[assume]] Attribute (P1774R8)
**Status**: 🔍 Untested
**Tests**: 0/13 passing
**Gap**: Unknown - may be silently stripped

**Technical Barrier**:
- `[[assume(expr)]]` tells compiler to assume `expr` is true
- C has no equivalent (GCC has `__builtin_assume`, but not standard)
- May be safe to strip if not critical to semantics

**Example Problem**:
```cpp
void f(int* p) {
    [[assume(p != nullptr)]];
    *p = 42;  // Compiler can optimize without null check
}
// C: No equivalent, must emit null check or risk UB
```

**Workaround**: Strip attribute, emit conservative code.

---

#### 8. Class Template Argument Deduction with Inherited Constructors (P2582R1)
**Status**: ⚠️ Partial Support
**Tests**: 0/10 passing
**Gap**: Basic CTAD works, inheritance cases fail

**Technical Barrier**:
- C++23 extends CTAD to inherited constructors
- Our monomorphization may not handle inheritance chains correctly
- Complex deduction guides not implemented

**Example Problem**:
```cpp
template<typename T>
struct Base { Base(T); };

template<typename T>
struct Derived : Base<T> {
    using Base<T>::Base;  // Inherit constructor
};

Derived d(42);  // C++23: deduces Derived<int>
// Our transpiler: May fail to deduce type
```

**Workaround**: Explicit template arguments `Derived<int> d(42)`.

---

#### 9. Ranges Enhancements (P2678R0)
**Status**: ❌ Not Supported
**Tests**: 0/10 passing
**Gap**: Requires STL transpilation (not implemented)

**Technical Barrier**:
- Ranges are library features, not language features
- Depend on C++20 Ranges library
- No plan to transpile STL

**Example Problem**:
```cpp
#include <ranges>
auto even = std::views::iota(0, 100) | std::views::filter([](int x) { return x % 2 == 0; });
// C: No ranges library, must manually write loop
```

**Workaround**: Manual implementation of range operations.

---

#### 10. Labels at End of Compound Statements (P2324R0)
**Status**: 🔍 Untested
**Tests**: 0/19 passing
**Gap**: May already work, needs testing

**Technical Barrier**:
- C++23 allows `label:` at end of block before `}`
- C99 requires statement after label
- May need to emit empty statement `;`

**Example Problem**:
```cpp
void f() {
    goto end;
    // ...
end:  // C++23: valid
}     // C99: invalid (label must precede statement)
```

**Workaround**: Emit `end: ;` with empty statement.

---

## Category-Specific Limitations

### Templates (35% Support for C++11, 0% for C++23)

**Working**:
- ✅ Basic class template monomorphization
- ✅ Function templates (simple cases)
- ✅ Basic template specialization

**Not Working**:
- ❌ Variadic templates (partial support only)
- ❌ Template template parameters
- ❌ SFINAE (Substitution Failure Is Not An Error)
- ❌ Concepts (C++20/23)
- ❌ Advanced CTAD
- ❌ Fold expressions

**Technical Barrier**: Templates in C++ are Turing-complete metaprogramming. C has no equivalent. We use monomorphization (instantiate templates with concrete types), but this only works for basic cases.

---

### Constexpr/Consteval (0% Support)

**Working**:
- Nothing

**Not Working**:
- ❌ Compile-time evaluation of any kind
- ❌ `constexpr` variables
- ❌ `constexpr` functions
- ❌ `consteval` immediate functions
- ❌ `if consteval`
- ❌ `constinit`

**Technical Barrier**: We have no compile-time execution engine. All `constexpr` becomes runtime code. This is a fundamental architectural limitation.

---

### Lambdas (20% Support)

**Working**:
- ⚠️ Stateless lambdas (converted to function pointers)
- ⚠️ Simple captures

**Not Working**:
- ❌ Generic lambdas
- ❌ Template lambdas (C++20)
- ❌ Complex captures (mutable, init-captures)
- ❌ Lambda in unevaluated contexts

**Technical Barrier**: C has no closures. We convert lambdas to structs with function pointers, but this doesn't scale to advanced lambda features.

---

### Coroutines (15% Support, C++20)

**Working**:
- ⚠️ Basic `co_await` framework
- ⚠️ Basic `co_yield` framework

**Not Working**:
- ❌ Full promise type implementation
- ❌ Coroutine handles
- ❌ Symmetric transfer
- ❌ Exception handling in coroutines

**Technical Barrier**: C has no native coroutine support. We use manual stack transformation, but it's incomplete.

---

### Exception Handling (60% Support)

**Working**:
- ✅ `try`/`catch` blocks (converted to `setjmp`/`longjmp`)
- ✅ `throw` expressions
- ✅ Stack unwinding with destructors

**Not Working**:
- ⚠️ Exception specifications (partial)
- ⚠️ `noexcept` tracking (limited)
- ❌ Exception translation in inheritance hierarchies (edge cases)

**Technical Barrier**: C has no exceptions. We emulate with `setjmp`/`longjmp`, but it's fragile and has performance overhead.

---

### Standard Library Features (0% Support)

**Working**:
- Nothing

**Not Working**:
- ❌ All `<expected>`, `<mdspan>`, `<format>`, etc.
- ❌ Ranges library
- ❌ Concepts library
- ❌ Any C++20/23 STL additions

**Technical Barrier**: We do not transpile the STL. This is by design. STL transpilation would be a massive undertaking (10x+ the size of the language transpiler).

---

## Build and Runtime Gaps

### Build System Issues

1. **Header Dependency Resolution**: Incomplete separation of declarations/definitions
   - Impact: May generate duplicate symbols or missing declarations
   - Workaround: Manual header organization

2. **Name Mangling**: C++ name mangling not fully reversed
   - Impact: Linker errors when mixing transpiled and hand-written C
   - Workaround: Use `extern "C"` blocks

3. **CMake Integration**: Generated C code may not integrate cleanly with existing C projects
   - Impact: Build configuration complexity
   - Workaround: Manual CMakeLists.txt adjustment

### Runtime Issues

1. **Memory Management**: C++ RAII not perfectly emulated
   - Impact: Potential memory leaks if destructors don't run
   - Workaround: Manual resource tracking

2. **Exception Safety**: `setjmp`/`longjmp` not perfectly safe
   - Impact: Undefined behavior in some edge cases
   - Workaround: Avoid exceptions in critical paths

3. **Performance**: Vtable dispatch overhead, no devirtualization
   - Impact: Virtual calls slower than C++ (no inline optimization)
   - Workaround: Manual devirtualization

---

## Testing Gaps

### Validation Challenges

1. **No Baseline Metrics Yet**: Phase 33.5 will establish first measurements
   - Unknown: Actual pass rate for any C++23 feature
   - Unknown: Build success rate
   - Unknown: Output match rate

2. **Output Comparison Difficulties**: C and C++ may produce equivalent but textually different output
   - Example: Different floating-point formatting
   - Example: Pointer address differences
   - Solution: Intelligent normalization in compare.py

3. **Missing Test Coverage**: Only 130 of 261 GCC C++23 tests integrated
   - Gap: 131 tests not yet adapted
   - Gap: No MSVC or LLVM test coverage
   - Gap: No real-world C++23 project tests

---

## Documentation Gaps

1. **User Guide**: No comprehensive guide for using transpiler on C++23 code
2. **API Reference**: Limited documentation of transpiler flags and options
3. **Migration Guide**: No guide for adapting C++23 code to transpile successfully
4. **Error Messages**: Transpiler error messages not always clear about why feature is unsupported

---

## Ecosystem Gaps

### Tool Integration

1. **IDE Support**: No IDE integration for transpiler (no LSP server)
2. **Debugger**: No debugging support for mapping C code back to C++ source
3. **Profiler**: No profiling integration for performance analysis

### Platform Support

1. **WebAssembly**: WASM builds exist but untested with C++23 code
2. **Cross-compilation**: Limited testing on non-x86_64 platforms
3. **Embedded**: No embedded-specific optimizations

---

## Prioritization of Gaps

### Critical (Blocking C++23 Adoption)
1. ❌ Compile-time execution (constexpr/consteval)
2. ❌ Deducing this (P0847R7)
3. ❌ Template system limitations

### High Priority (Limiting C++20 Adoption)
1. ⚠️ Lambdas (generic, template)
2. ⚠️ Coroutines (full implementation)
3. ⚠️ Concepts (fundamental for modern C++)

### Medium Priority (Nice to Have)
1. 📋 Multidimensional subscript operator
2. 📋 Static operators
3. 📋 Ranges library support

### Low Priority (Can Work Around)
1. 📋 Attributes (most can be stripped)
2. 📋 Labels at end of statements
3. 📋 Standard library features

---

## Relationship to Roadmap

See [ROADMAP.md](ROADMAP.md) for planned improvements addressing these gaps.

**Key Insight**: Many C++23 gaps are **architectural limitations**, not implementation bugs. Some features (like compile-time execution, concepts, deducing this) may **never be fully supported** due to fundamental C vs C++ differences.

---

## How to Work With These Gaps

### For Users

1. **Check Feature Matrix First**: Before using C++23 features, verify support in [FEATURE-MATRIX.md](FEATURE-MATRIX.md)

2. **Use Workarounds**: Many gaps have documented workarounds (manual code expansion, explicit types, etc.)

3. **Target C++11**: Best support is for C++11 features. Stick to that subset when possible.

4. **Avoid STL**: Do not use C++20/23 STL features (expected, mdspan, ranges, format).

5. **Test Incrementally**: Use A/B testing framework to validate transpilation works before relying on it.

### For Contributors

1. **Document New Gaps**: When discovering unsupported features, add them here.

2. **Focus on High-Impact**: Prioritize closing gaps that affect the most users.

3. **Be Honest About Limitations**: Don't promise features that violate architectural constraints.

4. **Update This Document**: Keep GAPS.md current as implementation progresses.

---

## Related Documents

- **[FEATURE-MATRIX.md](FEATURE-MATRIX.md)**: What features are supported (current state)
- **[ROADMAP.md](ROADMAP.md)**: Plans to address gaps (future state)
- **[README.md](../README.md)**: Current validation suite status

---

## Conclusion

The Hupyy transpiler has fundamental architectural constraints that prevent full C++23 support. Many advanced C++ features have no clean C equivalent. Understanding these gaps is essential for:

1. **Setting realistic expectations** about transpiler capabilities
2. **Prioritizing development efforts** toward addressable gaps
3. **Guiding users** to write transpilable C++ code
4. **Designing workarounds** for common use cases

**Remember**: The goal is not to achieve 100% C++23 support (likely impossible), but to maximize practical utility for real-world C++ → C transpilation needs.

---

**Document Version**: 1.0
**Created**: December 24, 2025
**Maintained By**: Transpiler Development Team
**Status**: Living Document (update as gaps are discovered/closed)

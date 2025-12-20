# Lambda and Closure Translation Tests

**Stream 1: Lambdas & Closures**
**Test File**: `LambdaTranslatorTest.cpp`
**Test Count**: 60 comprehensive test functions
**Status**: Complete

---

## Overview

This test suite validates the C++ to C transpiler's ability to correctly translate lambda expressions into C closure implementations. Lambda support is critical for modern C++ code, requiring sophisticated closure generation, capture list handling, and function pointer management.

### Why This Matters

Lambda expressions are one of C++'s most powerful features, introduced in C++11 and enhanced in C++14/17/20. Transpiling lambdas to C requires:

1. **Closure Struct Generation**: Each lambda creates a unique closure type containing captured variables
2. **Capture Mechanism Translation**: By-value, by-reference, and mixed captures must preserve semantics
3. **Function Pointer Generation**: Captureless lambdas can convert to function pointers
4. **Lifetime Management**: Closure objects must have correct construction, copy, move, and destruction

---

## Test Statistics

| Category | Test Count | Coverage |
|----------|-----------|----------|
| **Basic Lambdas** | 10 tests | Simple lambdas, return types, parameters, mutable |
| **Capture Mechanisms** | 15 tests | By value, by reference, capture all, mixed, init captures |
| **Closure Generation** | 12 tests | Struct generation, function pointers, this-pointer, lifetime |
| **Lambda Types** | 10 tests | Auto variables, parameters, return values, std::function, generic |
| **Edge Cases** | 13 tests | Empty lambda, recursive, constexpr, template contexts |
| **Total** | **60 tests** | **Comprehensive lambda translation coverage** |

---

## Test Categories

### Category 1: Basic Lambdas (10 tests)

Tests fundamental lambda expression parsing and translation.

**Test Functions**:
1. `test_lambda_no_capture_simple` - Simple lambda without captures
2. `test_lambda_explicit_return_type` - Lambda with explicit return type
3. `test_lambda_with_parameters` - Lambda with parameters
4. `test_lambda_mutable` - Mutable lambda
5. `test_lambda_void_return` - Lambda returning void
6. `test_lambda_multiple_statements` - Lambda with multiple statements
7. `test_lambda_trailing_return_complex` - Trailing return type with complex expression
8. `test_lambda_immediately_invoked` - Lambda immediately invoked (IIFE)
9. `test_lambda_noexcept` - Lambda with noexcept specifier
10. `test_lambda_variadic_parameters` - Lambda with variadic parameters

**Key Scenarios**:
```cpp
// Simple lambda
auto lambda = []() { return 42; };

// Lambda with parameters and explicit return type
auto lambda = [](int x, int y) -> double { return x / y; };

// Mutable lambda
auto lambda = [x]() mutable { x++; };
```

---

### Category 2: Capture Mechanisms (15 tests)

Tests all capture list variations and semantics.

**Test Functions**:
1. `test_capture_by_value_single` - Capture by value (single variable)
2. `test_capture_by_value_multiple` - Capture by value (multiple variables)
3. `test_capture_by_reference_single` - Capture by reference (single variable)
4. `test_capture_by_reference_multiple` - Capture by reference (multiple variables)
5. `test_capture_all_by_value` - Capture all by value `[=]`
6. `test_capture_all_by_reference` - Capture all by reference `[&]`
7. `test_capture_mixed` - Mixed captures (value and reference)
8. `test_capture_init` - Init capture (C++14)
9. `test_capture_this` - Capture this pointer
10. `test_capture_this_by_copy` - Capture this by copy (C++17)
11. `test_capture_default_with_exception` - Default capture with exception
12. `test_capture_const_variable` - Capture const variable
13. `test_capture_nested_lambdas` - Nested lambda captures
14. `test_capture_structured_binding` - Capture with structured binding (C++17)
15. `test_capture_outer_scope` - Capture variable from outer scope

**Key Scenarios**:
```cpp
// Capture by value
int x = 42;
auto lambda = [x]() { return x; };

// Capture by reference
int x = 42;
auto lambda = [&x]() { x++; };

// Capture all
auto lambda = [=]() { return x + y; };  // All by value
auto lambda = [&]() { x = y = 0; };     // All by reference

// Init capture (C++14)
auto lambda = [x = 42]() { return x; };

// Capture this
class Foo {
    int member;
    void method() {
        auto lambda = [this]() { return member; };
    }
};
```

---

### Category 3: Closure Generation (12 tests)

Tests closure struct generation and implementation details.

**Test Functions**:
1. `test_closure_struct_generation` - Closure struct for lambda with captures
2. `test_closure_member_variables` - Closure with member variables for captures
3. `test_closure_function_pointer_conversion` - Function pointer conversion for captureless lambda
4. `test_closure_call_operator` - Call operator method generation
5. `test_closure_lifetime` - Closure lifetime and scope
6. `test_closure_reference_members` - Closure with reference captures
7. `test_closure_this_pointer` - Closure with this pointer member
8. `test_closure_empty_size` - Closure size optimization for empty lambda
9. `test_closure_copy_constructor` - Closure copy constructor
10. `test_closure_move_constructor` - Closure move constructor
11. `test_closure_complex_types` - Closure with complex captured types
12. `test_closure_destructor` - Closure destructor generation

**Key Translation Pattern**:
```cpp
// C++ Lambda
int x = 1, y = 2;
auto lambda = [x, y](int z) { return x + y + z; };

// Expected C Translation
struct __lambda_1 {
    int __x;  // Captured by value
    int __y;  // Captured by value
};

int __lambda_1_call(const struct __lambda_1* __closure, int z) {
    return __closure->__x + __closure->__y + z;
}

// Usage
struct __lambda_1 lambda = { .__x = 1, .__y = 2 };
int result = __lambda_1_call(&lambda, 3);
```

**Function Pointer Conversion**:
```cpp
// C++ Lambda (no captures)
auto lambda = [](int x) { return x * 2; };
int (*fptr)(int) = lambda;

// Expected C Translation
int __lambda_1(int x) {
    return x * 2;
}

int (*fptr)(int) = __lambda_1;
```

---

### Category 4: Lambda Types (10 tests)

Tests lambda type deduction, storage, and usage patterns.

**Test Functions**:
1. `test_lambda_auto_variable` - Lambda assigned to auto variable
2. `test_lambda_as_parameter` - Lambda passed as function parameter
3. `test_lambda_returned` - Lambda returned from function
4. `test_lambda_in_std_function` - Lambda stored in std::function
5. `test_lambda_generic` - Generic lambda (C++14)
6. `test_lambda_in_container` - Lambda in container
7. `test_lambda_decltype` - Lambda type deduction with decltype
8. `test_lambda_in_template` - Lambda in template context
9. `test_lambda_deduced_return` - Lambda with deduced return type
10. `test_lambda_stateless` - Stateless lambda optimization

**Key Scenarios**:
```cpp
// Auto variable
auto lambda = []() { return 42; };

// Function parameter
template<typename F>
void apply(F func) { func(); }
apply([]() { return 42; });

// std::function
std::function<int()> func = []() { return 42; };

// Generic lambda (C++14)
auto lambda = [](auto x) { return x + 1; };
```

---

### Category 5: Edge Cases (13 tests)

Tests corner cases, advanced features, and error conditions.

**Test Functions**:
1. `test_lambda_empty` - Empty lambda
2. `test_lambda_recursive` - Recursive lambda
3. `test_lambda_constexpr` - Lambda in constexpr context
4. `test_lambda_exception_spec` - Lambda with exception specification
5. `test_lambda_unevaluated_context` - Lambda in unevaluated context
6. `test_lambda_attributes` - Lambda with attribute specifier
7. `test_lambda_template_argument` - Lambda in template argument
8. `test_multiple_lambdas` - Multiple lambdas in single expression
9. `test_lambda_capture_trailing_comma` - Lambda with trailing comma in capture list
10. `test_lambda_complex_default_capture` - Lambda with complex default capture
11. `test_lambda_move_capture` - Lambda with move capture (C++14)
12. `test_lambda_if_init` - Lambda in if-init statement (C++17)
13. `test_lambda_parameter_pack` - Lambda with parameter pack (C++14)

**Key Scenarios**:
```cpp
// Recursive lambda
std::function<int(int)> fib = [&fib](int n) {
    return n < 2 ? n : fib(n-1) + fib(n-2);
};

// Constexpr lambda
constexpr auto lambda = []() { return 42; };
constexpr int value = lambda();

// Move capture
auto ptr = std::make_unique<int>(42);
auto lambda = [p = std::move(ptr)]() { return *p; };

// Generic lambda with parameter pack
auto lambda = [](auto... args) {
    return (args + ...);
};
```

---

## Test Infrastructure

### AST Parsing
```cpp
std::unique_ptr<ASTUnit> buildAST(const char *code);
```
Builds Clang AST from C++ code with C++17 standard.

### Lambda Finding
```cpp
LambdaExpr* findFirstLambda(ASTUnit* AST);
std::vector<LambdaExpr*> findAllLambdas(ASTUnit* AST);
```
Helper functions to locate lambda expressions in the AST.

### Test Macros
```cpp
TEST_START(name)  // Print test start
TEST_PASS(name)   // Print test pass
ASSERT(cond, msg) // Assert with message
```

---

## Building and Running

### Build
```bash
# Navigate to project root
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c

# Configure with CMake
cmake -B build -DCMAKE_BUILD_TYPE=Debug

# Build LambdaTranslatorTest
cmake --build build --target LambdaTranslatorTest
```

### Run Tests
```bash
# Run all lambda tests
./build/LambdaTranslatorTest

# Expected output:
# =============================================================
# Lambda and Closure Translation Test Suite
# Stream 1: Lambdas & Closures (60 tests)
# =============================================================
#
# Category 1: Basic Lambdas (10 tests)
# -------------------------------------------------------------
# Test: lambda_no_capture_simple ... PASS
# Test: lambda_explicit_return_type ... PASS
# ...
#
# All Lambda Tests Completed Successfully!
# Total: 60 test functions
# =============================================================
```

---

## Implementation Guidelines

### Closure Struct Generation

For each lambda with captures, the transpiler must generate:

1. **Closure Struct Definition**:
```c
struct __lambda_N {
    // Member for each capture
    int __captured_x;      // By-value capture
    int* __captured_y_ref; // By-reference capture
};
```

2. **Call Operator Function**:
```c
ReturnType __lambda_N_call(const struct __lambda_N* __closure, Params...) {
    // Lambda body with captures accessed via __closure->
}
```

3. **Constructor** (if needed):
```c
struct __lambda_N __lambda_N_create(int x, int* y_ref) {
    struct __lambda_N closure;
    closure.__captured_x = x;
    closure.__captured_y_ref = y_ref;
    return closure;
}
```

### Function Pointer Optimization

Captureless lambdas can be optimized to plain C functions:

```c
// No struct needed
ReturnType __lambda_N(Params...) {
    // Lambda body
}
```

---

## Test Coverage Summary

### Features Tested
- ✅ Simple lambdas without captures
- ✅ Lambdas with parameters and return types
- ✅ Mutable lambdas
- ✅ Capture by value (single and multiple)
- ✅ Capture by reference (single and multiple)
- ✅ Capture all by value `[=]`
- ✅ Capture all by reference `[&]`
- ✅ Mixed captures
- ✅ Init captures (C++14)
- ✅ This pointer capture
- ✅ Closure struct generation
- ✅ Function pointer conversion
- ✅ Call operator generation
- ✅ Generic lambdas (C++14)
- ✅ Recursive lambdas
- ✅ Constexpr lambdas
- ✅ Lambdas in templates
- ✅ Edge cases and corner cases

### C++ Standards Covered
- **C++11**: Basic lambdas, captures, mutable
- **C++14**: Init captures, generic lambdas, auto parameters
- **C++17**: `*this` capture, constexpr lambdas, if-init statements
- **C++20**: Parameter packs, fold expressions

---

## Success Criteria

All 60 tests must pass, validating:

1. **Correctness**: Lambda semantics preserved in C translation
2. **Completeness**: All capture mechanisms supported
3. **Efficiency**: Captureless lambdas optimized to function pointers
4. **Safety**: Closure lifetime and memory management correct
5. **Compatibility**: Works with all C++11/14/17/20 lambda features

---

## Related Documentation

- [Test Parallel Execution Plan](/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/docs/TEST_PARALLEL_EXECUTION_PLAN.md)
- [Test Suite Documentation](/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/docs/TEST_SUITE.md)
- [Project Guidelines](/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/CLAUDE.md)

---

## Next Steps

After Stream 1 completion:
- **Stream 2**: Move Semantics & Perfect Forwarding (40-60 tests)
- **Stream 3**: Smart Pointers & RAII (80-100 tests)
- **Stream 4**: Operator Overloading (50-60 tests)
- **Stream 5**: Type Traits & Metaprogramming (70-90 tests)
- **Stream 6**: Edge Cases & Integration (70-90 tests)

**Target**: 1,000+ total test functions across all streams

---

**Test Suite Status**: ✅ **Complete**
**Test Count**: 60/60 (100%)
**Categories**: 5/5 (100%)
**Last Updated**: 2025-12-18

*Generated with [Claude Code](https://claude.com/claude-code) | December 2025*

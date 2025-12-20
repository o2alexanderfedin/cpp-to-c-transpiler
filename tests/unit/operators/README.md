# Operator Overloading Test Suite

**Stream 4: Comprehensive Operator Overloading Tests**

## Overview

This directory contains comprehensive unit tests for C++ operator overloading translation in the C++ to C transpiler. Operator overloading is syntactic sugar in C++ that must be translated to explicit function calls in C, with proper name mangling to avoid conflicts.

## Test Coverage

### Total Tests: 62

The test suite covers all major operator categories:

### 1. Arithmetic Operators (15 tests)
Tests for mathematical operations:
- **Binary operators**: `+`, `-`, `*`, `/`, `%`
- **Unary operators**: unary `+`, unary `-`
- **Increment/Decrement**: `++` (prefix), `++` (postfix), `--` (prefix), `--` (postfix)
- **Compound assignment**: `+=`, `-=`, `*=`, `/=`

**Why it matters**: Arithmetic operators are the most common use case for operator overloading (e.g., Vector, Matrix, Complex number operations). Correct translation ensures mathematical operations maintain semantics.

### 2. Comparison Operators (10 tests)
Tests for relational operations:
- **Basic comparisons**: `==`, `!=`, `<`, `>`, `<=`, `>=`
- **Multiple operators**: Classes with multiple comparison operators
- **Different parameter types**: Overloads with different parameter types
- **Friend operators**: Non-member comparison operators
- **Const correctness**: Proper const qualification

**Why it matters**: Comparison operators are critical for sorting, searching, and conditional logic. The transpiler must generate distinct function names for each operator while preserving const semantics.

### 3. Subscript & Call Operators (12 tests)
Tests for array-like and function-like access:
- **Subscript operator**: `operator[]` with various parameter types
- **Const subscript**: `const operator[]` for read-only access
- **Overloaded subscript**: Multiple `operator[]` overloads
- **Call operator**: `operator()` with 0, 1, 2+ parameters
- **Overloaded call**: Multiple `operator()` signatures
- **Lambda-like behavior**: Functor patterns
- **Reference returns**: Operators returning references

**Why it matters**: These operators enable container and functor patterns. The transpiler must handle parameter count variations and const/non-const versions.

### 4. Special Operators (12 tests)
Tests for pointer-like and bitwise operations:
- **Smart pointer operators**: `operator->`, `operator*` (dereference)
- **Address operator**: `operator&`
- **Bitwise operators**: `~`, `&`, `|`, `^`
- **Shift operators**: `<<`, `>>`
- **Logical operators**: `!`, `&&`, `||`
- **Assignment operators**: `operator=`, move assignment
- **Comma operator**: `operator,`

**Why it matters**: Special operators enable smart pointers, iterators, and custom pointer semantics. Proper translation is critical for RAII patterns and resource management.

### 5. Conversion Operators (10 tests)
Tests for type conversion:
- **Implicit conversions**: `operator T()`
- **Explicit conversions**: `explicit operator T()`
- **Bool conversion**: `explicit operator bool()`
- **Pointer conversion**: `operator T*()`
- **Reference conversion**: `operator T&()`
- **User-defined type conversion**: `operator CustomType()`
- **Multiple conversions**: Classes with multiple conversion operators
- **Const conversions**: `operator const T*()`

**Why it matters**: Conversion operators enable natural type conversions. The transpiler must distinguish between implicit/explicit conversions and handle const correctness.

### 6. Stream Operators (3 tests)
Tests for I/O operations:
- **Output operator**: `operator<<`
- **Input operator**: `operator>>`
- **Friend stream operators**: Non-member stream operators

**Why it matters**: Stream operators are distinct from shift operators despite using the same symbols (`<<`, `>>`). Context-sensitive translation is required.

## Test File Structure

```
tests/unit/operators/
├── OperatorOverloadingTest.cpp  # Main test suite (62 tests)
└── README.md                     # This file
```

## Test Methodology

Each test follows this pattern:

1. **Parse C++ code** containing operator overloading
2. **Locate operator** in the AST using Clang's API
3. **Verify operator detection** (correct operator type, parameters)
4. **Name mangling** via `NameMangler` to generate C function name
5. **Assertions** on mangled names, operator properties

## Key Test Scenarios

### Name Mangling
- Different operators must produce unique mangled names
- Overloaded operators with different signatures must have distinct names
- Const and non-const versions must be distinguishable

### Parameter Handling
- Operators with different parameter counts (prefix vs postfix `++`)
- Operators with different parameter types (int vs double)
- Pass-by-value vs pass-by-reference parameters

### Return Types
- Value returns vs reference returns
- Const returns vs non-const returns
- Void returns (some compound assignment patterns)

### Const Correctness
- Const member functions
- Const parameters
- Const return types

### Friend Functions
- Friend operator declarations
- Non-member operator overloads

## Integration with Transpiler

The operator overloading tests validate the following transpiler components:

1. **NameMangler**: Generates unique C function names for operators
2. **CppToCVisitor**: Recognizes operator overloading in AST
3. **CodeGenerator**: Translates operator calls to C function calls

## Running the Tests

```bash
# Build test suite
cmake -B build
cmake --build build --target OperatorOverloadingTest

# Run tests
./build/OperatorOverloadingTest
```

## Expected Output

```
===============================================
C++ Operator Overloading Translation Test Suite
Stream 4: Comprehensive Operator Tests
===============================================

--- ARITHMETIC OPERATORS (15 tests) ---
Test: BinaryPlusOperator ... PASS
Test: BinaryMinusOperator ... PASS
...

--- COMPARISON OPERATORS (10 tests) ---
...

--- SUBSCRIPT & CALL OPERATORS (12 tests) ---
...

--- SPECIAL OPERATORS (12 tests) ---
...

--- CONVERSION OPERATORS (10 tests) ---
...

--- STREAM OPERATORS (3 tests) ---
...

===============================================
Test Results:
  PASSED: 62
  FAILED: 0
  TOTAL:  62
===============================================
```

## Test Quality Criteria

Each test validates:
- ✅ Operator is correctly detected in AST
- ✅ Operator type is correctly identified
- ✅ Parameter count and types are correct
- ✅ Const correctness is preserved
- ✅ Name mangling produces unique identifiers
- ✅ Overloaded operators have distinct mangled names

## Relationship to C Translation

### C++ Code
```cpp
class Vector {
    int x, y;
    Vector operator+(const Vector& other) const;
};
```

### Expected C Translation
```c
typedef struct Vector {
    int x, y;
} Vector;

Vector Vector_operator_plus_const_Vector_ref(const Vector* this, const Vector* other);
```

The test suite validates that:
1. `operator+` is recognized as an overloaded operator
2. The mangled name is unique and deterministic
3. The const qualification is preserved
4. The parameter types are correctly encoded

## Future Enhancements

Potential areas for additional tests:
- C++20 spaceship operator (`<=>`)
- Three-way comparison operators
- Custom literal operators (`operator""`)
- Array new/delete operators (`operator new[]`, `operator delete[]`)
- Placement new operators
- Co_await operator (C++20 coroutines)

## References

- C++ Standard: Operator overloading rules
- Clang AST: `CXXMethodDecl`, `CXXConversionDecl`, operator detection
- Name Mangling: Itanium C++ ABI for operator names
- SOLID Principles: Single Responsibility (each test validates one operator pattern)

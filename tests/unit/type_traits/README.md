# Type Traits & Template Metaprogramming Test Suite

## Overview

This test suite (Stream 5) provides comprehensive coverage of C++ type traits, SFINAE patterns, and template metaprogramming features. These tests validate that the C++ to C transpiler correctly evaluates compile-time template metaprogramming constructs and generates appropriate C code.

## Test Files

### TypeTraitsTest.cpp (40 tests)

Tests for type traits, SFINAE, and compile-time type manipulation:

**Section 1: Basic Type Traits (Tests 1-10)**
- `is_integral`, `is_pointer`, `is_const`, `is_reference`
- `is_floating_point`, `is_array`, `is_function`, `is_void`
- `is_class`, `is_enum`

**Section 2: Type Transformations (Tests 11-20)**
- `remove_const`, `add_pointer`, `remove_pointer`, `add_const`
- `remove_reference`, `decay`, `conditional`
- `underlying_type`, `make_signed`, `make_unsigned`

**Section 3: SFINAE and enable_if (Tests 21-30)**
- Basic `enable_if` usage and return type specialization
- Template parameter enable_if
- SFINAE with function overloading
- `enable_if_t` alias (C++14)
- SFINAE with class specialization
- Complex SFINAE expressions with multiple conditions
- `void_t` pattern (C++17)
- Nested enable_if patterns

**Section 4: Type Relationships & Compile-time Evaluation (Tests 31-40)**
- `is_same`, `is_base_of`, `is_convertible`, `is_constructible`
- `alignment_of`, `rank`, `extent`, `common_type`
- Compile-time type selection
- Complex trait composition

### MetaprogrammingTest.cpp (45 tests)

Tests for advanced template metaprogramming:

**Section 1: Variadic Template Basics (Tests 1-10)**
- Basic variadic templates and function templates
- Parameter pack expansion in function calls
- Variadic forwarding and `sizeof...` operator
- Variadic inheritance and braced initializers
- Non-type variadic parameters
- Mixed variadic and fixed parameters

**Section 2: Recursive Template Metaprogramming (Tests 11-20)**
- Compile-time factorial, fibonacci, power, GCD
- Recursive type list processing
- Recursive maximum computation
- List reversal, contains check, index lookup
- Nested recursive templates

**Section 3: constexpr Functions (Tests 21-30)**
- Basic constexpr functions with conditionals
- constexpr recursion and loops (C++14)
- Multiple return paths
- constexpr templates and constructors
- constexpr array and string operations
- Complex compile-time logic (prime checking)

**Section 4: Fold Expressions & Advanced Patterns (Tests 31-45)**
- Unary left/right fold expressions
- Binary fold expressions
- Logical AND/OR folds
- Fold with function calls
- Perfect forwarding with variadic templates
- Template template parameters
- `if constexpr` (C++17)
- Compile-time string hashing
- Type trait composition with variadic templates
- Compile-time tuple access
- Cartesian product computation

## Why These Tests Matter

Type traits and template metaprogramming are evaluated entirely at compile-time. For a C++ to C transpiler:

1. **Type Traits**: Must be evaluated during transpilation to determine the concrete types and generate appropriate C code
2. **SFINAE**: Controls which template instantiations are valid, affecting what C functions are generated
3. **constexpr**: All constexpr computations must be evaluated at transpile-time, not runtime
4. **Variadic Templates**: Must expand parameter packs into concrete function/struct definitions
5. **Recursive Templates**: Must fully evaluate recursion to generate non-recursive C code

## Building and Running

### Build Individual Tests

```bash
# Build TypeTraitsTest
cd build
cmake ..
make TypeTraitsTest

# Build MetaprogrammingTest
make MetaprogrammingTest
```

### Run Tests

```bash
# Run type traits tests
./TypeTraitsTest

# Run metaprogramming tests
./MetaprogrammingTest
```

### Expected Output

Both test suites should output:
- Section-by-section progress
- Individual test pass/fail status
- Final summary showing all tests passing

Example:
```
========================================
Stream 5: Type Traits Test Suite
Target: 40 comprehensive tests
========================================

=== SECTION 1: Basic Type Traits ===
Test: is_integral type trait ... PASS
Test: is_pointer type trait ... PASS
...

Test Results:
  Passed: 40 / 40
  Failed: 0 / 40
```

## Test Coverage Summary

| Category | Tests | Description |
|----------|-------|-------------|
| Basic Type Traits | 10 | Fundamental type checking traits |
| Type Transformations | 10 | Type modification and conversion |
| SFINAE & enable_if | 10 | Template substitution failure patterns |
| Type Relationships | 10 | Type comparison and compatibility |
| Variadic Templates | 10 | Parameter pack operations |
| Recursive Templates | 10 | Compile-time recursion patterns |
| constexpr Functions | 10 | Compile-time function evaluation |
| Fold & Advanced | 15 | C++17 features and complex patterns |
| **Total** | **85** | **Comprehensive metaprogramming coverage** |

## Key Features Tested

### Compile-Time Evaluation
- All `static_assert` statements must pass at compile-time
- constexpr functions evaluated during transpilation
- Template recursion must terminate with correct values

### SFINAE Patterns
- Function overload resolution based on type traits
- Class template specialization with enable_if
- Template parameter SFINAE

### Variadic Templates
- Parameter pack expansion in various contexts
- Fold expressions (C++17)
- Recursive variadic processing

### Type Traits Composition
- Combining multiple traits with logical operators
- Nested type transformations
- Complex trait predicates

## Integration with Transpiler

The transpiler must:

1. **Evaluate all type traits at transpile-time**: `is_integral<int>` → `true` (constant)
2. **Resolve SFINAE**: Only instantiate valid template specializations
3. **Compute constexpr**: All constexpr functions must produce compile-time constants
4. **Expand variadic templates**: Generate separate C functions for each instantiation
5. **Unroll recursive templates**: Convert recursive templates to iterative or direct computation

## Transpilation Examples

### Type Trait Evaluation
```cpp
// C++ with type trait
template<typename T>
std::enable_if_t<std::is_integral<T>::value, T>
increment(T x) { return x + 1; }

// Transpiled C (for int)
int increment_int(int x) { return x + 1; }
```

### constexpr Evaluation
```cpp
// C++ with constexpr
constexpr int factorial(int n) {
    return n <= 1 ? 1 : n * factorial(n-1);
}
constexpr int result = factorial(5);

// Transpiled C
#define result 120  // Evaluated at transpile-time
```

### Variadic Template Expansion
```cpp
// C++ variadic template
template<typename... Args>
auto sum(Args... args) { return (... + args); }

// Transpiled C (for specific instantiations)
int sum_int_int_int(int a, int b, int c) { return a + b + c; }
double sum_double_double(double a, double b) { return a + b; }
```

## Success Criteria

All tests must:
- ✅ Compile without errors
- ✅ All `static_assert` statements pass
- ✅ Runtime assertions succeed (where applicable)
- ✅ Generate semantically correct C code
- ✅ Preserve compile-time guarantees in C output

## Notes

- These tests use C++17 features (fold expressions, if constexpr)
- Some tests require standard library headers (`<type_traits>`, `<utility>`)
- The transpiler must have a complete understanding of the C++ type system
- Recursive templates must have proper termination conditions to avoid infinite expansion

## Related Test Suites

- `tests/TemplateExtractorTest.cpp` - Template instantiation extraction
- `tests/MonomorphizationTest.cpp` - Template to C conversion
- `tests/STLIntegrationTest.cpp` - STL container templates

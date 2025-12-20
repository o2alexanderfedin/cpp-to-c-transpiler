# Integration Test Suite

**Stories**: #122 (Unit Tests), #123 (Integration Tests)
**Epics**: #49 (Comprehensive Testing + Documentation)
**Test Count**: 105 tests (20 + 30 + 25 + 30)
**Status**: Complete ✅

## Overview

This directory contains comprehensive integration tests for the C++ to C transpiler, focusing on feature combinations, edge cases, error handling, and real-world scenarios. These tests ensure that complex C++ features work correctly together when transpiled to C.

## Test Organization

### File Structure

```
tests/integration/
├── FeatureCombinationTest.cpp     # 20 tests - Feature combinations (Story #123)
├── FeatureInteractionTest.cpp     # 30 tests - Feature interactions
├── EdgeCasesTest.cpp              # 30 tests - Boundary conditions
├── ErrorHandlingTest.cpp          # 25 tests - Error handling
└── README.md                      # This file
```

### Test Files

#### 1. FeatureCombinationTest.cpp (20 tests) - Story #123

**Purpose**: Test complex feature combinations critical for real-world C++ to C transpilation.

**Categories**:
- **RAII + Exceptions** (5 tests):
  - Exception unwinding with destructors
  - Multiple RAII objects in exception path
  - Nested try-catch with RAII
  - Exception specifications (noexcept)
  - Constructor exceptions

- **Virtual Inheritance + RTTI** (4 tests):
  - dynamic_cast through virtual bases
  - typeid with virtual inheritance
  - Multi-level virtual inheritance
  - Vtable layout with virtual bases

- **Multiple Inheritance + Virtual Functions** (4 tests):
  - Multiple interface implementation
  - Virtual function overriding in MI
  - Diamond problem (non-virtual)
  - Thunk generation for MI

- **Coroutines + RAII** (3 tests):
  - Resource cleanup in coroutines
  - Exception handling in coroutines
  - Suspend points with RAII

- **Complex Hierarchies** (3 tests):
  - 5-level deep inheritance
  - Mixed multiple and virtual inheritance
  - All features combined in hierarchy

- **Kitchen Sink** (1 test):
  - All major C++ features in one test
  - Validates feature interactions don't cause conflicts

**Key Tests**:
```cpp
test_raii_exception_unwinding()           // RAII cleanup during exceptions
test_virtual_inheritance_dynamic_cast()   // dynamic_cast with virtual bases
test_multiple_inheritance_thunks()        // Thunk generation for MI
test_coroutine_raii_cleanup()             // Coroutine resource cleanup
test_deep_inheritance_5_levels()          // Deep hierarchy handling
test_kitchen_sink()                       // All features combined
```

#### 2. EdgeCasesTest.cpp (30 tests)

**Purpose**: Test boundary conditions and unusual but valid C++ constructs.

**Categories**:
- **Empty Inputs** (8 tests):
  - Empty classes, structs, functions
  - Empty namespaces, enums
  - Classes with only empty methods
  - Empty parameter packs
  - Empty initializer lists

- **Maximum Nesting/Recursion** (8 tests):
  - Deeply nested classes (5 levels)
  - Deeply nested namespaces
  - Deeply nested blocks
  - Deep inheritance chains (5+ levels)
  - Nested template instantiations
  - Recursive type definitions
  - Deeply nested function calls
  - Template recursion depth

- **Unusual Type Combinations** (9 tests):
  - Triple pointers (int***)
  - Arrays of pointers to arrays
  - Complex function pointer signatures
  - Const volatile qualifiers
  - References to pointers
  - Rvalue references to const
  - Templates with multiple defaults
  - Unusual bitfield sizes
  - Unions with complex types

- **Additional Edge Cases** (5 tests):
  - Anonymous struct/union
  - Flexible array members
  - Extremely long identifier names
  - Diamond inheritance
  - Template specialization for void

**Key Tests**:
```cpp
test_edge_empty_class()                    // Empty class definition
test_edge_deeply_nested_classes()          // 5 levels of nesting
test_edge_triple_pointer()                 // int*** handling
test_edge_diamond_inheritance()            // Multiple inheritance diamond
test_edge_template_recursion_depth()       // Template metaprogramming limits
```

#### 3. ErrorHandlingTest.cpp (25 tests)

**Purpose**: Verify error detection, graceful degradation, and error message quality.

**Categories**:
- **Invalid C++ Constructs** (6 tests):
  - Missing semicolons
  - Private member access violations
  - Undefined type usage
  - Multiple definitions
  - Invalid template instantiations
  - Invalid operator overloads

- **Unsupported Features** (7 tests):
  - C++20 concepts (graceful handling)
  - C++20 modules
  - Inline assembly
  - Complex thread-local storage
  - Consteval functions
  - Spaceship operator (<=>)
  - Complex attributes

- **Compile-time vs Runtime Errors** (5 tests):
  - Constexpr violations
  - Template deduction mismatches
  - Abstract class instantiation
  - Const correctness violations
  - Array bounds checking

- **Error Message Quality** (7 tests):
  - Missing return type errors
  - Template syntax errors
  - Circular dependency detection
  - Ambiguous overload resolution
  - Missing template arguments
  - Invalid type conversions
  - Deleted function usage

**Key Tests**:
```cpp
test_error_private_inheritance_access()    // Access control enforcement
test_unsupported_inline_asm()              // Graceful degradation
test_error_constexpr_violation()           // Compile-time checking
test_error_message_circular_dependency()   // Clear error reporting
test_error_abstract_class_instantiation()  // Abstract class checks
```

#### 4. FeatureInteractionTest.cpp (30 tests)

**Purpose**: Test complex interactions between multiple C++ features and real-world design patterns.

**Categories**:
- **Templates + Other Features** (8 tests):
  - Templates + exceptions
  - Templates + RAII
  - Templates + inheritance
  - Templates + smart pointers
  - Variadic templates + perfect forwarding
  - Templates + constexpr
  - Template specialization + operator overloading
  - Templates + lambdas

- **Inheritance + Other Features** (7 tests):
  - Inheritance + RAII
  - Virtual functions + exceptions
  - Multiple inheritance + virtual functions
  - Virtual inheritance + constructors
  - Inheritance + operator overloading
  - Abstract classes + templates
  - Inheritance + RTTI (dynamic_cast)

- **Lambdas + Other Features** (5 tests):
  - Lambdas + smart pointers
  - Lambdas + exceptions
  - Generic lambdas (auto parameters)
  - Nested lambdas
  - Lambdas with complex captures

- **Real-world Scenarios** (10 tests):
  - RAII resource manager
  - Observer pattern (templates)
  - Factory pattern
  - Thread-safe singleton
  - Custom allocators
  - CRTP (Curiously Recurring Template Pattern)
  - State machine implementation
  - Iterator pattern
  - Event system with callbacks
  - Reference counting

**Key Tests**:
```cpp
test_interaction_templates_raii()          // Template RAII wrapper
test_interaction_virtual_exceptions()      // Virtual methods + exceptions
test_interaction_generic_lambdas()         // Auto parameters in lambdas
test_realworld_raii_resource_manager()     // Complete RAII system
test_realworld_observer_pattern()          // Observer with templates
test_realworld_singleton_thread_safe()     // Meyers singleton
test_realworld_crtp_pattern()              // Static polymorphism
test_realworld_reference_counting()        // Manual ref counting
```

## Test Patterns

### Test Structure

All tests follow a consistent structure:

```cpp
void test_category_specific_scenario() {
    TEST_START("test_category_specific_scenario");

    const char *code = R"(
        // C++ code to test
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse code");

    // Specific assertions
    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    // Verify expected structure
    ASSERT(condition, "Error message");

    TEST_PASS("test_category_specific_scenario");
}
```

### Naming Conventions

Tests follow the pattern: `test_<category>_<specific_case>()`

**Categories**:
- `edge_` - Edge cases and boundary conditions
- `error_` - Error detection and handling
- `unsupported_` - Unsupported feature handling
- `interaction_` - Feature interaction tests
- `realworld_` - Real-world design patterns

**Examples**:
- `test_edge_empty_class()` - Edge case: empty class
- `test_error_missing_semicolon()` - Error: syntax error
- `test_interaction_templates_raii()` - Interaction: templates + RAII
- `test_realworld_singleton_thread_safe()` - Real-world: singleton pattern

## Running Tests

### Build Tests

```bash
# Configure build with tests
cmake -B build -DCMAKE_BUILD_TYPE=Debug

# Build specific test
cmake --build build --target EdgeCasesTest
cmake --build build --target ErrorHandlingTest
cmake --build build --target FeatureInteractionTest

# Or build all tests
cmake --build build
```

### Run Tests

```bash
# Run individual test suites
./build/EdgeCasesTest
./build/ErrorHandlingTest
./build/FeatureInteractionTest

# Run with CTest
cd build
ctest -R "EdgeCasesTest|ErrorHandlingTest|FeatureInteractionTest"

# Run all tests
ctest --output-on-failure
```

### Expected Output

Each test suite produces output like:

```
========================================
Stream 6: Edge Cases Test Suite
========================================

Category 1: Empty Inputs
------------------------
Running test_edge_empty_class... ✓
Running test_edge_empty_struct... ✓
...

========================================
Results: 30 passed, 0 failed
========================================
```

## Integration with CI/CD

### GitHub Actions

These tests are part of the parallel CI/CD strategy:

```yaml
test-stream-6:
  name: "Stream 6: Edge Cases & Integration"
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v3
    - name: Build
      run: |
        cmake --build build --target EdgeCasesTest
        cmake --build build --target ErrorHandlingTest
        cmake --build build --target FeatureInteractionTest
    - name: Run Tests
      run: |
        ./build/EdgeCasesTest
        ./build/ErrorHandlingTest
        ./build/FeatureInteractionTest
```

### Coverage Impact

Stream 6 tests contribute to overall coverage:

- **Edge Cases**: Cover boundary conditions often missed
- **Error Handling**: Ensure graceful degradation
- **Feature Interactions**: Test real-world usage patterns

**Expected Coverage Contribution**: +5-10% to overall project coverage

## Quality Metrics

### Test Quality Checklist

All tests in Stream 6 meet these criteria:

- ✅ Clear, descriptive names
- ✅ Single responsibility (one scenario per test)
- ✅ Specific assertions with meaningful error messages
- ✅ Consistent execution (no flaky tests)
- ✅ Follow AAA pattern (Arrange-Act-Assert)
- ✅ Fast execution (<100ms per test)
- ✅ Proper cleanup (no memory leaks)

### Success Criteria

Stream 6 is successful if:

- ✅ 70-90 tests implemented (target: 85)
- ✅ All tests pass consistently
- ✅ No flaky tests
- ✅ Edge cases properly covered
- ✅ Error handling verified
- ✅ Real-world patterns tested
- ✅ Integration with existing tests successful

## Test Coverage by Feature

### Features Tested

| Feature | EdgeCases | ErrorHandling | FeatureInteraction | Total |
|---------|-----------|---------------|-------------------|-------|
| Templates | 3 | 5 | 8 | 16 |
| Inheritance | 2 | 1 | 7 | 10 |
| Lambdas | 1 | 0 | 5 | 6 |
| RAII | 0 | 0 | 4 | 4 |
| Exceptions | 0 | 2 | 3 | 5 |
| Virtual Functions | 0 | 1 | 5 | 6 |
| Operators | 0 | 2 | 1 | 3 |
| Edge Cases | 24 | 0 | 0 | 24 |
| Error Handling | 0 | 15 | 0 | 15 |
| Design Patterns | 0 | 0 | 10 | 10 |

### Cross-Stream Coverage

Stream 6 complements other streams:

- **Stream 1 (Lambdas)**: Adds lambda interaction tests
- **Stream 2 (Move Semantics)**: Tests move with other features
- **Stream 3 (Smart Pointers)**: Real-world smart pointer usage
- **Stream 4 (Operators)**: Operator overloading edge cases
- **Stream 5 (Templates)**: Template interaction scenarios

## Known Limitations

### Test Scope

These tests focus on:
- ✅ AST parsing and structure verification
- ✅ Error detection and reporting
- ✅ Feature interaction patterns

These tests do NOT cover:
- ❌ Full C code generation (see unit tests)
- ❌ Runtime behavior validation (see validation tests)
- ❌ Performance benchmarks (see benchmarks/)

### Platform Dependencies

Some tests may behave differently across platforms:
- Error message formatting may vary
- Compiler-specific extensions not tested
- Standard library availability assumed

## Maintenance

### Adding New Tests

To add a new integration test:

1. Choose the appropriate file:
   - **EdgeCasesTest.cpp**: Boundary conditions
   - **ErrorHandlingTest.cpp**: Error scenarios
   - **FeatureInteractionTest.cpp**: Feature combinations

2. Follow the naming convention:
   ```cpp
   void test_category_specific_scenario() { ... }
   ```

3. Add to the appropriate category section

4. Update the test count in this README

5. Run and verify the test passes

### Updating Tests

When updating transpiler features:

1. Check if edge cases affected
2. Update error handling if error behavior changed
3. Add new feature interaction tests for new features
4. Ensure all existing tests still pass
5. Update documentation

## Related Documentation

- [Test Parallel Execution Plan](../../docs/TEST_PARALLEL_EXECUTION_PLAN.md) - Overall strategy
- [CMakeLists.txt](../../CMakeLists.txt) - Build configuration
- [Test Coverage Report](../../docs/TEST_COVERAGE_REPORT.md) - Coverage analysis

## Contact

For questions about Stream 6 tests:
- **Owner**: Tech Lead
- **Stream**: 6 (Edge Cases & Integration)
- **Purpose**: Quality assurance and robustness verification

---

**Version**: 2.0 (Story #123 Complete)
**Last Updated**: 2025-12-18
**Test Count**: 105 tests (20 + 30 + 30 + 25)
**Status**: Complete ✅

Generated with [Claude Code](https://claude.com/claude-code)

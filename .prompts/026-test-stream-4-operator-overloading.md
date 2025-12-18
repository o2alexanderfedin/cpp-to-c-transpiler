<objective>
Implement comprehensive unit tests for C++ operator overloading in the C++ to C transpiler.

This is Stream 4 of the parallel test expansion plan, targeting 50-60 high-quality unit tests covering arithmetic, comparison, subscript, call, and conversion operators. These tests validate that the transpiler correctly translates operator syntax to C function calls.
</objective>

<context>
**Project**: C++ to C Transpiler
**Work Stream**: Stream 4 - Operator Overloading
**Owner**: Mid-Level Developer
**Timeline**: Week 1-3 (days 3-21)
**Current State**: 492 test functions exist
**Target**: Add 50-60 tests

Read @docs/TEST_PARALLEL_EXECUTION_PLAN.md for coordination.
Read @CLAUDE.md for project conventions.

**Why This Matters**: Operator overloading is syntactic sugar that must translate to explicit function calls in C. Tests ensure correct operator-to-function mapping, proper parameter passing, and return value handling.
</context>

<requirements>
Create test file `tests/unit/operators/OperatorOverloadingTest.cpp` with 50-60 tests:

1. **Arithmetic Operators** (12-15 tests):
   - Binary: +, -, *, /, % (5 tests)
   - Unary: ++, --, +, -, ~ (5 tests)
   - Compound assignment: +=, -=, *=, /= (2-5 tests)

2. **Comparison Operators** (8-10 tests):
   - ==, !=, <, >, <=, >= (6 tests)
   - <=> spaceship operator (C++20) (2-4 tests)

3. **Subscript & Call Operators** (10-12 tests):
   - operator[] (array subscript) (5-7 tests)
   - operator() (function call) (5-7 tests)

4. **Special Operators** (10-12 tests):
   - operator-> (member access) (3-4 tests)
   - operator* (dereference) (3-4 tests)
   - operator new/delete (4-6 tests)

5. **Conversion Operators** (8-10 tests):
   - operator T() (type conversion) (5-7 tests)
   - explicit conversion (3-5 tests)

6. **Stream Operators** (2-3 tests):
   - operator<< and operator>> (if applicable)
</requirements>

<implementation>
**Test Structure**:
```cpp
void test_binary_plus_operator() {
    // C++: obj1 + obj2
    // Expected C: class_add(&obj1, &obj2)
}

void test_subscript_operator_array_access() {
    // C++: container[5]
    // Expected C: container_subscript(&container, 5)
}

void test_conversion_operator_explicit() {
    // Test explicit operator bool() translation
}
```

**Assertions**:
- Correct function name generation (operator_add, operator_subscript, etc.)
- Proper parameter passing (by value, by reference)
- Return value handling
- Const-correctness preserved

**WHY These Tests**: Each operator has unique calling conventions and semantics. Comprehensive testing prevents subtle bugs in operator translation.
</implementation>

<integration>
- Owns `tests/unit/operators/` directory
- Uses shared fixtures library
- Branch: `test-stream-4-operators`
- No conflicts (independent directory)
</integration>

<output>
- `./tests/unit/operators/OperatorOverloadingTest.cpp` - 50-60 tests
- Update `./CMakeLists.txt`
- `./tests/unit/operators/README.md`
</output>

<verification>
1. 50-60 test functions ✓
2. All tests pass ✓
3. All operator categories covered ✓
4. Generated C code compiles and runs ✓
5. Code review approved ✓

Verify:
```bash
cmake --build build --target OperatorOverloadingTest
./build/tests/unit/operators/OperatorOverloadingTest
```
</verification>

<success_criteria>
- 50-60 passing tests for operator overloading
- All operator categories covered
- Correct C function generation verified
- Follows conventions
- Stream 4 deliverable complete ✓
</success_criteria>

<objective>
Implement comprehensive unit tests for C++ lambdas and closures in the C++ to C transpiler.

This is Stream 1 of the parallel test expansion plan, targeting 40-60 high-quality unit tests covering lambda expression translation, closure implementation, and capture mechanisms. These tests validate that the transpiler correctly handles one of C++'s most powerful features.
</objective>

<context>
**Project**: C++ to C Transpiler
**Work Stream**: Stream 1 - Lambdas & Closures
**Owner**: Senior Developer
**Timeline**: Week 1-3 (days 3-21)
**Current State**: 492 test functions exist across 66 test files
**Target**: Add 40-60 tests to reach partial goal toward 1,000+ total

Read @docs/TEST_PARALLEL_EXECUTION_PLAN.md for the full parallel execution strategy.
Read @docs/TEST_SUITE.md for existing test organization patterns.
Read @CLAUDE.md for project conventions.

**Why This Matters**: Lambda support is critical for modern C++ code. Transpiling lambdas to C requires sophisticated closure generation, capture list handling, and function pointer management. These tests ensure correctness across all lambda scenarios.
</context>

<requirements>
Create test file `tests/unit/lambdas/LambdaTranslatorTest.cpp` with 40-60 test cases covering:

1. **Basic Lambdas** (8-10 tests):
   - Simple lambda without captures: `[]() { return 42; }`
   - Lambda with return type: `[]() -> int { return 42; }`
   - Lambda with parameters: `[](int x) { return x * 2; }`
   - Mutable lambda: `[]() mutable { }`

2. **Capture Mechanisms** (12-15 tests):
   - Capture by value: `[x]() { return x; }`
   - Capture by reference: `[&x]() { x++; }`
   - Capture all by value: `[=]() { }`
   - Capture all by reference: `[&]() { }`
   - Mixed captures: `[x, &y]() { }`
   - Init captures (C++14): `[x = 42]() { return x; }`
   - Generalized captures: `[ptr = std::move(ptr)]() { }`

3. **Closure Generation** (10-12 tests):
   - Closure struct generation with captured variables
   - Function pointer generation for lambda body
   - This-pointer handling in closures
   - Closure lifetime management
   - Nested closures

4. **Lambda Types** (8-10 tests):
   - Assigned to auto variable
   - Passed as function parameter
   - Returned from function
   - Stored in std::function
   - Generic lambda (C++14): `[](auto x) { return x; }`

5. **Edge Cases** (2-5 tests):
   - Empty lambda: `[]() {}`
   - Recursive lambda
   - Lambda in template context
   - Constexpr lambda (C++17)
</requirements>

<implementation>
**Test Framework**: Follow existing pattern from @tests/unit/ - use custom test functions with manual assertions.

**Test Structure** (consistent with existing tests):
```cpp
// tests/unit/lambdas/LambdaTranslatorTest.cpp

void test_simple_lambda_no_capture() {
    // Setup: C++ code with simple lambda
    // Execute: Transpile to C
    // Assert: Verify closure struct and function pointer generated
}

void test_capture_by_value() {
    // Test lambda with value captures generates correct closure
}

// ... 40-60 total test functions
```

**Naming Convention**: `test_<feature>_<scenario>`

**Assertions**: Use existing assertion helpers from other test files. Check for:
- Correct closure struct with member variables
- Function pointer typedef
- Proper capture initialization
- Correct function body translation

**WHY these patterns**:
- Manual test functions maintain consistency with 492 existing tests
- Explicit assertions make failures easy to debug
- One assertion per key requirement enables precise failure identification
</implementation>

<integration>
**Shared Infrastructure** (from fixtures library - Day 1-2):
- Use shared test utilities from `tests/fixtures/`
- Lambda test data generators
- Common closure verification helpers

**Avoid Conflicts**:
- This stream owns `tests/unit/lambdas/` directory exclusively
- No modifications to shared source files during development
- Use feature branches: `test-stream-1-lambdas`

**Coordination**:
- Daily standup: Report test count progress
- Code review: 2-person review before merge
- Quality gate: All tests must pass before stream completion
</integration>

<output>
Create these files with relative paths:
- `./tests/unit/lambdas/LambdaTranslatorTest.cpp` - Main test file (40-60 test functions)
- Update `./CMakeLists.txt` - Add new test executable target
- Create `./tests/unit/lambdas/README.md` - Document test organization

Each test should follow this structure:
1. Setup: Create AST for C++ lambda expression
2. Execute: Run transpiler translation
3. Assert: Verify generated C code correctness
4. Cleanup: Release resources
</output>

<verification>
Before declaring complete, verify:
1. **Test count**: 40-60 test functions implemented ✓
2. **All tests pass**: Run `make LambdaTranslatorTest && ./LambdaTranslatorTest` ✓
3. **Coverage**: Check that all 5 requirement categories are covered ✓
4. **Code quality**: No compiler warnings, follows project style ✓
5. **Documentation**: README.md explains test organization ✓
6. **Integration**: Tests build with existing suite ✓

Run these commands to verify:
```bash
cmake --build build --target LambdaTranslatorTest
./build/tests/unit/lambdas/LambdaTranslatorTest
grep -c "^void test_" tests/unit/lambdas/LambdaTranslatorTest.cpp  # Should be 40-60
```
</verification>

<success_criteria>
- 40-60 test functions implemented and passing
- All lambda translation scenarios covered (basic, captures, closures, types, edge cases)
- Tests follow existing project patterns and conventions
- No merge conflicts with other streams
- Code review approved by 2 developers
- Documentation complete
- Stream 1 deliverable: 40-60 tests toward 1,000+ goal ✓
</success_criteria>

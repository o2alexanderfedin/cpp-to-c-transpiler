<objective>
Run the complete test suite for the C++ to C transpiler project, identify all failing tests, and fix them using Test-Driven Development (TDD) principles.

This ensures the codebase maintains high quality, all features work correctly after recent changes (Stories #122 and #123 added 437+ new tests), and the project remains in a deployable state.
</objective>

<context>
**Project**: C++ to C Transpiler
**Current State**:
- 933+ unit tests across 77 test files
- 105 integration tests
- Total: 1,038+ tests
- Recent additions: Parallel test expansion (6 streams) + integration tests

**Tech Stack**: C++17, CMake, Clang/LLVM tooling, Custom test framework

Read @CLAUDE.md for project conventions including:
- TDD workflow (write test first → implement → refactor)
- SOLID principles
- Type safety requirements
- Linting requirements before completion

**Why This Matters**: The test suite is the project's safety net. After significant test expansion, we need to ensure all tests pass and fix any issues discovered. This validates that the transpiler correctly handles all C++ features.
</context>

<requirements>
1. **Discover All Tests**:
   - Find all test executables in the build directory
   - Identify all test targets from CMakeLists.txt
   - Count total number of test executables

2. **Run Complete Test Suite**:
   - Execute ALL test executables sequentially
   - Capture output from each test run
   - Track pass/fail status for each test suite
   - Record which specific test functions fail (not just which files)

3. **Analyze Failures**:
   - For each failing test, identify:
     - Test name and location
     - Failure reason (assertion, compilation error, runtime error)
     - Root cause (missing implementation, incorrect logic, environment issue)
   - Categorize failures by type (compilation, assertion, crash, timeout)

4. **Fix Failures Using TDD**:
   - For each failure, follow TDD cycle:
     - **Red**: Understand why the test fails (already done - it's failing)
     - **Green**: Implement minimal code to make test pass
     - **Refactor**: Clean up implementation while keeping test green
   - Fix one test at a time, verifying the fix before moving to the next
   - Re-run the specific test after each fix to confirm it passes
   - Re-run the full suite periodically to catch regressions

5. **Handle Different Failure Types**:
   - **Compilation errors**: Fix syntax, missing includes, type errors
   - **Assertion failures**: Fix logic errors in implementation
   - **Missing implementations**: Implement required functionality
   - **Environment issues**: Document and skip if cannot be fixed (e.g., missing system headers)

6. **Verification**:
   - After all fixes, run complete test suite again
   - Confirm 100% pass rate (or document acceptable skips)
   - Verify no regressions introduced by fixes
</requirements>

<implementation>
**Phase 1: Test Discovery**
```bash
# Find all test executables
find build -type f -executable -name "*Test" | sort

# Or use CMake to list targets
cmake --build build --target help | grep Test
```

**Phase 2: Run All Tests**
```bash
# Run each test and capture output
for test in build/*Test; do
    echo "Running $test..."
    $test 2>&1 | tee logs/${test##*/}.log
done

# Or use CTest if configured
cd build && ctest --output-on-failure --verbose
```

**Phase 3: TDD Fix Cycle**

For each failing test:

1. **Understand the failure**:
   - Read the test code to understand what it's testing
   - Read the error message carefully
   - Identify the expected vs actual behavior

2. **Implement the fix**:
   - Make minimal changes to pass the test
   - Don't over-engineer or add extra features
   - Follow existing code patterns in the project

3. **Verify the fix**:
   ```bash
   # Rebuild if needed
   cmake --build build --target <TestName>

   # Run the specific test
   ./build/<TestName>

   # Verify it passes
   ```

4. **Refactor if needed**:
   - Clean up code while keeping test green
   - Follow SOLID principles
   - Maintain type safety

5. **Run related tests**:
   ```bash
   # Run tests that might be affected by this change
   ./build/<RelatedTest1>
   ./build/<RelatedTest2>
   ```

**Common Failure Patterns**:

- **Missing headers**: Test includes `<memory>`, `<typeinfo>`, `<coroutine>` but they're not found
  - These are often intentional (testing parser, not compilation)
  - Mark as expected behavior if test still passes

- **Unimplemented features**: Test expects functionality not yet implemented
  - Implement minimal version following TDD
  - Or mark test as TODO if feature is out of scope

- **Type errors**: Incorrect types, missing const, etc.
  - Fix to satisfy type checker
  - Ensure changes maintain type safety

- **Logic errors**: Test assertions fail due to incorrect implementation
  - Fix the logic to match expected behavior
  - Consider edge cases

**WHY TDD Matters Here**:
- Tests already exist and define expected behavior clearly
- We're in the "Red" phase (tests failing)
- Our job is to get to "Green" (tests passing) with minimal changes
- This ensures we fix actual issues without introducing new ones
</implementation>

<constraints>
- **DO NOT** modify tests to make them pass (fix implementation instead)
- **DO NOT** skip tests without documenting why
- **DO NOT** introduce new features beyond what tests require
- **DO** follow existing code patterns and conventions
- **DO** maintain type safety and run linters
- **DO** commit fixes incrementally (per test or per category)
- **DO** use parallel test execution where safe (independent test suites)
</constraints>

<output>
1. **Test Run Report**: `./test-results-before.log`
   - List of all tests run
   - Pass/fail status for each
   - Summary statistics

2. **Failure Analysis**: `./test-failures-analysis.md`
   - Categorized list of failures
   - Root cause for each
   - Fix strategy for each

3. **Fixed Code**: Modified source files as needed
   - Follow existing project structure
   - Maintain code quality

4. **Final Report**: `./test-results-after.log`
   - Complete test run after all fixes
   - Verification that all tests pass
   - Summary of changes made

5. **Git Commits**: Incremental commits for each fix
   - Descriptive commit messages
   - Group related fixes together
</output>

<verification>
Before declaring complete, verify:

1. ✓ All test executables discovered and run
2. ✓ All failures documented with root cause
3. ✓ All fixable failures fixed using TDD cycle
4. ✓ Each fix verified individually before moving to next
5. ✓ Full test suite run after all fixes
6. ✓ Pass rate is 100% (or acceptable with documented skips)
7. ✓ No regressions introduced (tests that passed before still pass)
8. ✓ Code follows project conventions (SOLID, type safety, etc.)
9. ✓ Linters pass on all modified code
10. ✓ Changes committed with clear messages

Final command to run:
```bash
# Rebuild everything
cmake --build build

# Run all tests
find build -type f -executable -name "*Test" -exec {} \; | tee final-test-results.log

# Verify success
echo "Tests passed: $(grep -c 'passed' final-test-results.log)"
echo "Tests failed: $(grep -c 'failed' final-test-results.log)"
```
</verification>

<success_criteria>
- All test executables identified and run
- All failing tests analyzed with root cause documented
- All fixable failures fixed following TDD principles (Red → Green → Refactor)
- Test pass rate: 100% or documented acceptable level with reasons
- No regressions (previously passing tests still pass)
- Code quality maintained (SOLID, type safety, conventions followed)
- All changes committed with descriptive messages
- Final test report shows comprehensive results
- Project is in deployable state
</success_criteria>

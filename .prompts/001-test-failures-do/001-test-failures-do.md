# Fix All Failing Tests to Achieve 100% Pass Rate

<objective>
Fix all 95 failing tests to achieve 100% test pass rate (904/904 tests passing).

Purpose: Ensure complete test coverage and code correctness as mandated by user requirement: "89% tests pass rate is not acceptable. All tests **must** pass!"

Output: Modified source files and test files to fix all failures, with comprehensive test fix report
</objective>

<context>
Current project: C++ to C transpiler using 3-stage pipeline (C++ AST → C AST → C code)
Architecture: Dispatcher pattern (Chain of Responsibility) for AST node handling
Testing framework: Google Test (GTest)
LLVM version: 15
Build system: CMake

Current test status:
- Total tests: 904
- Passing: 809 (89%)
- Failing: 95 (11%)
- Disabled: 45 (E2E tests, not included in failure count)

Test output from most recent run: !`cd build && ctest --output-on-failure 2>&1 | tail -200 > /tmp/test_output.txt && cat /tmp/test_output.txt`
</context>

<requirements>

## Functional Requirements

1. **All tests must pass**: Achieve 904/904 (100%) pass rate
2. **No disabled tests**: Tests must be fixed or deleted (not disabled per user directive)
3. **No regression**: Fixes must not break currently passing tests
4. **Maintain architecture**: Follow SOLID principles, TDD methodology, dispatcher pattern

## Quality Requirements

1. **TDD cycle**: For each fix:
   - Understand why test fails (RED)
   - Implement minimal fix (GREEN)
   - Refactor if needed while keeping tests green (REFACTOR)

2. **Code quality**:
   - Follow existing code conventions
   - Maintain type safety (use explicit types, avoid `any` equivalent in C++)
   - Document complex fixes with comments

3. **Verification**:
   - Run full test suite after each category of fixes
   - Ensure pass rate increases monotonically
   - Build must complete without warnings or errors

## Constraints

1. **LLVM 15 compatibility**: If test requires C++23 features not in LLVM 15, delete the test
2. **Architecture preservation**: Do not change dispatcher pattern or 3-stage pipeline architecture
3. **Pipeline separation**: Maintain separation between:
   - Stage 1: Clang parsing (C++ AST generation)
   - Stage 2: Translation (C++ AST → C AST) - CppToCVisitor
   - Stage 3: Emission (C AST → C code) - CodeGenerator
4. **No AST mixing**: Never mix C++ ASTContext nodes with C ASTContext nodes
</requirements>

<implementation>

## Strategy

### Phase 1: Investigation and Categorization
1. Run failing tests individually with verbose output
2. Categorize failures by root cause:
   - Missing features
   - LLVM 15 API incompatibilities
   - Test infrastructure issues
   - Implementation bugs
   - C++23 features unavailable in LLVM 15

3. Create TodoWrite task list with all failure categories

### Phase 2: Priority-Ordered Fixes

Fix categories in this order (to minimize conflicts):

1. **Priority 1: RecordHandler Tests (7 failures)**
   - Core struct/class translation functionality
   - Files: tests/unit/dispatch/RecordHandlerDispatcherTest.cpp
   - Likely issue: Dispatcher integration, singleton mappers

2. **Priority 2: CodeGenerator Tests (6 failures)**
   - Output stage (Stage 3 of pipeline)
   - Files: tests/unit/CodeGeneratorTest.cpp
   - Likely issue: API changes, output format expectations

3. **Priority 3: Module Rejection Tests (3 failures)**
   - Error handling for unsupported C++20 modules
   - Files: tests/integration/Phase61ModuleRejectionTest_gtest.cpp
   - Critical: These MUST reject module declarations/exports/partitions

4. **Priority 4: Integration Tests (15 failures)**
   - HandlerIntegrationTest, StaticDataMemberIntegrationTest, etc.
   - Cross-handler cooperation tests
   - Likely issue: Mapper state, AST context mixing

5. **Priority 5: C++23 Feature Tests (37 failures)**
   - MultidimSubscriptTranslator (8 tests)
   - AssumeAttributeHandler (13 tests)
   - ConstevalIfTranslator (10 tests)
   - AutoDecayCopyTranslator (11 tests)
   - Check LLVM 15 API availability
   - If unavailable: DELETE tests (per user directive: "No disabling tests!!!")

6. **Priority 6: E2E Tests (27 failures)**
   - GlobalVariablesE2ETest (8 tests)
   - PointersE2ETest (7 tests)
   - StructsE2ETest (12 tests)
   - Full pipeline integration tests
   - Likely issue: Generated C code execution, runtime behavior

### Phase 3: Fix Implementation Pattern

For each failing test:

```cpp
// 1. Run test individually
ctest -R TestName --output-on-failure

// 2. Identify root cause
// - Read test expectations
// - Check what's being tested
// - Run with debugger if needed

// 3. Implement minimal fix
// - Find the source file responsible
// - Make smallest change that fixes the issue
// - Follow existing patterns

// 4. Verify fix
ctest -R TestName  // Passes now
ctest              // No regression in other tests
```

### Phase 4: Verification After Each Priority

After each priority level:
1. Run full test suite: `ctest`
2. Verify pass rate increased
3. Check no new failures introduced
4. Commit with message: `fix(tests): Fix [category] tests ([N] failures resolved)`

### Phase 5: Final Verification

After all fixes:
1. Clean build: `rm -rf build && mkdir build && cd build && cmake .. && make`
2. Full test run: `ctest`
3. Verify: 904/904 tests passing (100%)
4. No warnings in build output
5. Create comprehensive test-fix-report.md

## What to Avoid and WHY

1. **DO NOT disable tests**: User explicitly stated "No disabling tests!!!"
2. **DO NOT mix ASTContexts**: Critical architecture violation - causes segfaults
3. **DO NOT change CodeGenerator to make translation decisions**: Violates pipeline separation (Stage 2 does translation, Stage 3 only emits)
4. **DO NOT use `std::make_unique()` for singleton mappers**: DeclMapper, TypeMapper, ExprMapper, StmtMapper use `getInstance()`
5. **DO NOT assume array indices exist**: Use safe access patterns with bounds checking

## Integration Points

1. **Dispatcher Pattern**: All handlers register with CppToCVisitorDispatcher using predicate+visitor pairs
2. **Singleton Mappers**: DeclMapper, TypeMapper, ExprMapper, StmtMapper - use `getInstance()` and `reset()` for test isolation
3. **Test Helpers**: UnitTestHelper.h and DispatcherTestHelper.h provide test infrastructure
4. **CMakeLists.txt**: Tests registered here - may need updates for new test files

</implementation>

<output>

Create/modify the following:

1. **Source files** (as needed to fix failing tests):
   - Likely: src/dispatch/*.cpp (handler implementations)
   - Likely: src/CodeGenerator.cpp (output stage fixes)
   - Likely: include/dispatch/*.h (handler declarations)
   - Possibly: src/*.cpp (core translation logic)

2. **Test files** (fixes or deletions):
   - tests/unit/dispatch/RecordHandlerDispatcherTest.cpp
   - tests/unit/CodeGeneratorTest.cpp
   - tests/integration/Phase61ModuleRejectionTest_gtest.cpp
   - tests/integration/HandlerIntegrationTest.cpp
   - tests/integration/StaticDataMemberIntegrationTest.cpp
   - tests/unit/MultidimSubscriptTranslatorTest.cpp (check LLVM 15 availability, may delete)
   - tests/unit/AssumeAttributeHandlerTest.cpp (check LLVM 15 availability, may delete)
   - tests/unit/ConstevalIfTranslatorTest.cpp (check LLVM 15 availability, may delete)
   - tests/unit/AutoDecayCopyTranslatorTest.cpp (check LLVM 15 availability, may delete)
   - tests/e2e/GlobalVariablesE2ETest.cpp
   - tests/e2e/PointersE2ETest.cpp
   - tests/e2e/StructsE2ETest.cpp
   - (Other test files as identified during investigation)

3. **CMakeLists.txt** (if tests deleted or added)

4. **Comprehensive report**: `.prompts/001-test-failures-do/test-fix-report.md`

   Structure:
   ```markdown
   # Test Fix Report

   ## Executive Summary
   - Initial: 809/904 (89%)
   - Final: 904/904 (100%)
   - Tests fixed: 95
   - Tests deleted: [N] (C++23 features unavailable in LLVM 15)

   ## Priority 1: RecordHandler Tests (7 failures)
   ### Root Cause
   [Detailed description of what was wrong]

   ### Fixes Applied
   - **File**: src/dispatch/RecordHandler.cpp
     - **Change**: [specific change made]
     - **Reasoning**: [why this fix was correct]
     - **Lines**: [line numbers]

   ### Tests Affected
   - RecordHandlerDispatcherTest.Registration: FIXED
   - RecordHandlerDispatcherTest.BasicStruct: FIXED
   - [...]

   ## Priority 2: [...]
   [Same structure for each priority]

   ## C++23 Features Analysis
   - MultidimSubscriptTranslator: [DELETED | FIXED] - [reasoning]
   - AssumeAttributeHandler: [DELETED | FIXED] - [reasoning]
   - ConstevalIfTranslator: [DELETED | FIXED] - [reasoning]
   - AutoDecayCopyTranslator: [DELETED | FIXED] - [reasoning]

   ## Verification Results
   - Clean build: SUCCESS
   - Full test suite: 904/904 PASS (100%)
   - No regressions: VERIFIED
   - Build warnings: NONE

   ## Files Modified
   1. [file path] - [brief description of changes]
   2. [...]

   ## Files Deleted
   1. [file path] - [reason for deletion]
   2. [...]

   ## Commits
   1. [commit hash] - fix(tests): Fix RecordHandler dispatcher tests (7 failures)
   2. [commit hash] - fix(tests): Fix CodeGenerator output tests (6 failures)
   3. [commit hash] - fix(tests): Fix module rejection error handling (3 failures)
   4. [commit hash] - fix(tests): Delete C++23 feature tests unavailable in LLVM 15 (37 tests)
   5. [commit hash] - fix(tests): Fix E2E integration tests (27 failures)
   6. [commit hash] - fix(tests): Achieve 100% test pass rate (904/904)
   ```

5. **SUMMARY.md**: `.prompts/001-test-failures-do/SUMMARY.md` (see summary_requirements below)

</output>

<verification>

Before declaring complete:

1. **Build verification**:
   ```bash
   rm -rf build
   mkdir build && cd build
   cmake ..
   make -j8
   # Must complete without errors or warnings
   ```

2. **Test verification**:
   ```bash
   cd build
   ctest --output-on-failure
   # Must show: 100% tests passed, 0 tests failed out of 904
   ```

3. **No disabled tests**:
   ```bash
   grep -r "DISABLED_" tests/
   grep -r "#if 0" tests/
   # Must not find any disabled tests
   ```

4. **Git verification**:
   ```bash
   git status
   # All changes committed
   git log --oneline -10
   # Shows commits for each priority level
   ```

5. **Documentation verification**:
   - test-fix-report.md exists and is comprehensive
   - SUMMARY.md exists with all required sections
   - All fixes documented with reasoning

6. **Architecture verification**:
   - No AST context mixing (verify with code review)
   - Pipeline separation maintained (CodeGenerator only emits, doesn't translate)
   - Singleton mappers used correctly (getInstance(), not make_unique())

</verification>

<summary_requirements>

Create `.prompts/001-test-failures-do/SUMMARY.md` with the following structure:

```markdown
# Test Fix Summary

**[One-liner describing outcome, e.g., "All 95 failing tests fixed - 100% pass rate achieved (904/904)"]**

## Version
v1 - Initial complete fix of all failing tests

## Key Findings
• RecordHandler failures due to [specific root cause]
• CodeGenerator failures due to [specific root cause]
• Module rejection tests failing to reject C++20 modules - [specific fix]
• C++23 features: [deleted/fixed] - [count] tests affected
• E2E test failures due to [specific root cause]

## Files Created
- `.prompts/001-test-failures-do/test-fix-report.md` - Comprehensive fix documentation
- [List any new test files created]

## Files Modified
- [Count] source files modified to fix test failures
- [Count] test files modified/deleted
- CMakeLists.txt updated for [specific changes]

## Files Deleted
- [List deleted test files with brief reasoning]

## Decisions Needed
None - all tests passing, ready for production

## Blockers
None - 100% pass rate achieved

## Next Step
Run validation suite on real-world C++ codebases to verify transpiler correctness
```

**Critical**: The one-liner must be substantive, not generic. It should describe the actual outcome (e.g., "Module rejection fixed, C++23 tests deleted, RecordHandler dispatcher integrated" not just "Tests fixed").

</summary_requirements>

<success_criteria>

1. **100% test pass rate**: 904/904 tests passing
2. **No disabled tests**: All tests either pass or deleted (with documented reasoning)
3. **Clean build**: No warnings or errors
4. **Documentation complete**:
   - test-fix-report.md with comprehensive analysis
   - SUMMARY.md with substantive one-liner and complete sections
5. **All changes committed**: With descriptive commit messages per priority level
6. **Architecture maintained**: SOLID principles, TDD methodology, dispatcher pattern preserved
7. **No regression**: All previously passing tests still pass

</success_criteria>

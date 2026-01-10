# Fix All Failing Tests to Achieve 100% Pass Rate

## Objective

Fix all 95 failing tests to achieve 100% test pass rate (904/904 tests passing).

## Context

Current test status:
- **Total tests**: 904
- **Passing**: 809 (89%)
- **Failing**: 95 (11%)
- **Disabled**: 45 (E2E tests)

The failing tests fall into the following categories:

### Category 1: RecordHandler Tests (7 failures)
- RecordHandlerDispatcherTest.Registration (Subprocess aborted)
- RecordHandlerDispatcherTest.BasicStruct
- RecordHandlerDispatcherTest.ClassToStruct
- RecordHandlerDispatcherTest.ForwardDeclaration
- RecordHandlerDispatcherTest.FieldTypes
- RecordHandlerDispatcherTest.NestedStruct
- RecordHandlerDispatcherTest.DuplicateDetection

### Category 2: CodeGenerator Tests (5 failures)
- CodeGeneratorTest.PrintStructDecl
- CodeGeneratorTest.PrintTranslationUnit
- CodeGeneratorTest.OutputToFile
- CodeGeneratorTest.StructKeyword
- CodeGeneratorTest.LineDirectivePresent
- CodeGeneratorTest.MultipleDeclarationsWithLines

### Category 3: C++23 Feature Tests (37 failures)
- MultidimSubscriptTranslatorTest.* (8 tests)
- AssumeAttributeHandlerTest.* (13 tests)
- ConstevalIfTranslatorTest.* (10 tests)
- AutoDecayCopyTranslatorTest.* (11 tests)

### Category 4: E2E Integration Tests (31 failures)
- GlobalVariablesE2ETest.* (8 tests)
- PointersE2ETest.* (7 tests)
- StructsE2ETest.* (12 tests)
- EnumE2ETest.StateMachineWithScopedEnum (1 test)
- HandlerIntegrationTest.* (3 tests)

### Category 5: Module Rejection Tests (3 failures)
- ErrorHandlingTestFixture.RejectModuleDeclaration
- ErrorHandlingTestFixture.RejectModuleExport
- ErrorHandlingTestFixture.RejectModulePartition

### Category 6: Other Tests (12 failures)
- NamespaceHandlerDispatcherTest.ClassInNamespace
- StaticOperatorTranslatorTest.StaticOperatorCallOnInstance
- DeclContextTest.CrossTUAddDecl
- StaticDataMemberIntegrationTest.ConstStaticWithInClassInitializer

## Requirements

Follow TDD principles and SOLID architecture. For each category:

1. **Investigate root cause** of failures
   - Run failing tests individually with verbose output
   - Identify common patterns within each category
   - Determine if failures are due to:
     - Missing features
     - LLVM 15 API incompatibilities
     - Test infrastructure issues
     - Regression from recent changes
     - Implementation bugs

2. **Fix by category** in priority order:
   - **Priority 1**: RecordHandler tests (core functionality)
   - **Priority 2**: CodeGenerator tests (output stage)
   - **Priority 3**: Module rejection tests (error handling)
   - **Priority 4**: Other integration tests
   - **Priority 5**: C++23 feature tests (may need feature flags or deletion)
   - **Priority 6**: E2E tests (comprehensive scenarios)

3. **For each fix**:
   - Write failing test first (if not already failing)
   - Implement minimal code to pass
   - Refactor while keeping tests green
   - Verify no regression in other tests
   - Document what was fixed and why

4. **Special handling for C++23 features**:
   - Check if features are available in LLVM 15
   - If not available: Delete tests (per user directive: "No disabling tests!!!")
   - If available but unimplemented: Decide whether to implement or delete based on project scope

5. **Verification**:
   - After each category: Run full test suite
   - Ensure pass rate increases monotonically
   - No new failures introduced
   - Final verification: 100% pass rate (904/904)

## Output

Create comprehensive report in `.prompts/060-fix-all-failing-tests/test-fix-report.md`:

```markdown
# Test Fix Report

## Summary
- Initial: 809/904 (89%)
- Final: 904/904 (100%)
- Tests fixed: 95

## Category 1: RecordHandler Tests
### Root Cause
[Description of issue]

### Fixes Applied
- File: [path]
  - Change: [description]
  - Reasoning: [why this fix]

### Tests Affected
- RecordHandlerDispatcherTest.Registration: FIXED
- [...]

## Category 2: [...]
[Same structure for each category]

## Verification
- Full test suite run: PASS (904/904)
- No regressions introduced: VERIFIED
- Build clean: VERIFIED

## Files Modified
1. [file path] - [brief description]
2. [...]

## Commits
1. [commit hash] - fix(record-handler): [description]
2. [...]
```

Also create `SUMMARY.md` with:

```markdown
# Test Fix Summary

**All 95 failing tests fixed - 100% pass rate achieved (904/904)**

## Key Findings
• RecordHandler failures due to [root cause]
• CodeGenerator failures due to [root cause]
• C++23 features [deleted/implemented] based on LLVM 15 availability
• Module rejection tests fixed by [solution]

## Decisions Needed
None - all tests passing

## Blockers
None

## Next Step
Commit and push all fixes with message: "fix(tests): Fix all 95 failing tests to achieve 100% pass rate"
```

## Success Criteria

1. **All tests passing**: 904/904 (100%)
2. **No disabled tests**: All tests either pass or deleted (if obsolete/unavailable)
3. **Build clean**: No warnings or errors
4. **Documentation complete**: test-fix-report.md and SUMMARY.md created
5. **Committed and pushed**: Changes in git repository
6. **Code quality**: All fixes follow SOLID principles and TDD

## Strategy

1. Create TodoWrite task list for all categories
2. Spawn parallel subtasks for investigation (one per category)
3. Collect results and determine execution order
4. Fix categories sequentially (to avoid conflicts)
5. Verify and commit after each category
6. Final verification: 100% pass rate
7. Create comprehensive report
8. Commit and push

## Critical Notes

- **User mandate**: "89% tests pass rate is not acceptable. All tests **must** pass!"
- **No disabling tests**: Tests must be fixed or deleted, not disabled
- **TDD required**: Follow RED-GREEN-REFACTOR cycle
- **SOLID principles**: Maintain architecture quality
- **100% or nothing**: Do not stop until all 904 tests pass

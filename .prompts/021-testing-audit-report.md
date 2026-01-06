# Testing Audit Report - work-items-project Scripts
## Date: 2025-12-15

## Executive Summary

This audit assesses the test coverage and quality of 56 production bash scripts in `~/.claude/skills/lib/work-items-project/`. The directory contains a comprehensive GitHub Projects v2 management toolkit with minimal test coverage.

### Key Findings

- **Total Scripts**: 56 production scripts + 1 common library
- **Existing Test Files**: 10 test files (2 BATS, 8 shell scripts)
- **Current Coverage**: ~12% (7 scripts with some tests out of 56)
- **Failing Tests**: 2 out of 2 BATS tests are failing
- **Root Cause**: Tests reference old script names (`gh-epic-create.sh` vs `epic-create.sh`)

### Coverage Gaps

**Critical**: 49 scripts have ZERO test coverage (87%)
**Partial**: Tests exist but many are marked "skip" (TDD RED phase)
**Quality**: Existing tests use proper mocking patterns but need fixes

---

## Script Inventory

### 1. Epic Management (9 scripts)
- epic-create.sh
- epic-delete.sh
- epic-link.sh
- epic-list.sh
- epic-update.sh
- epic-to-todo.sh
- epic-to-in-progress.sh
- epic-to-done.sh
- epic-to-blocked.sh

**Test Status**:
- ✅ epic-create: Has test file (FAILING - wrong path)
- ❌ epic-delete: NO TESTS
- ❌ epic-link: NO TESTS
- ❌ epic-list: NO TESTS
- ✅ epic-update: Partial (via item_update_test.bats)
- ❌ epic-to-*: NO TESTS (4 status transition scripts)

### 2. Story Management (9 scripts)
- story-create.sh
- story-delete.sh
- story-link.sh
- story-list.sh
- story-update.sh
- story-to-todo.sh
- story-to-in-progress.sh
- story-to-done.sh
- story-to-blocked.sh

**Test Status**: ❌ ALL UNTESTED (9 scripts)

### 3. Task Management (9 scripts)
- task-create.sh
- task-delete.sh
- task-link.sh
- task-list.sh
- task-update.sh
- task-to-todo.sh
- task-to-in-progress.sh
- task-to-done.sh
- task-to-blocked.sh

**Test Status**: ❌ ALL UNTESTED (9 scripts)

### 4. Spike Management (8 scripts)
- spike-create.sh
- spike-delete.sh
- spike-list.sh
- spike-update.sh
- spike-to-todo.sh
- spike-to-in-progress.sh
- spike-to-done.sh
- spike-to-blocked.sh

**Test Status**: ❌ ALL UNTESTED (8 scripts)

### 5. Bug Management (10 scripts)
- bug-create.sh
- bug-delete.sh
- bug-list.sh
- bug-close.sh
- bug-reopen.sh
- bug-update.sh
- bug-to-todo.sh
- bug-to-in-progress.sh
- bug-to-done.sh
- bug-to-blocked.sh

**Test Status**: ❌ ALL UNTESTED (10 scripts)

### 6. Project Management (9 scripts)
- project-init.sh
- project-create.sh
- project-delete.sh
- project-list.sh
- project-update.sh
- project-link.sh
- project-clone.sh
- project-export-to-template.sh
- project-import-from-template.sh

**Test Status**:
- ✅ project-init: Has test (gh-project-init_test.sh)
- ✅ project-create: Has test (gh-project-create_test.sh)
- ✅ project-delete: Has test (gh-project-delete_test.sh)
- ✅ project-list: Has test (gh-project-list_test.sh)
- ✅ project-update: Has test (gh-project-update_test.sh)
- ❌ project-link: NO TESTS
- ❌ project-clone: NO TESTS
- ❌ project-export-to-template: NO TESTS
- ❌ project-import-from-template: NO TESTS

### 7. Utility Scripts (2 scripts)
- create-status-transitions.sh (meta-script for generating status transition scripts)
- lib/gh-project-common.sh (shared library)

**Test Status**:
- ✅ lib/gh-project-common.sh: Partial (common_test.sh, gh_wrapper_test.sh)
- ❌ create-status-transitions.sh: NO TESTS

---

## Existing Test Analysis

### Test Files Inventory

| Test File | Type | Status | Issues |
|-----------|------|--------|--------|
| gh-epic-create_test.bats | BATS | FAILING | Wrong script path reference |
| item_update_test.bats | BATS | FAILING | Missing arg validation |
| gh-project-create_test.sh | Shell | UNKNOWN | Uses @test (should be BATS) |
| gh-project-delete_test.sh | Shell | UNKNOWN | Uses @test (should be BATS) |
| gh-project-init_test.sh | Shell | UNKNOWN | Uses @test (should be BATS) |
| gh-project-list_test.sh | Shell | UNKNOWN | Uses @test (should be BATS) |
| gh-project-update_test.sh | Shell | UNKNOWN | Uses @test (should be BATS) |
| common_test.sh | Shell | UNKNOWN | Manual test runner |
| gh_wrapper_test.sh | Shell | UNKNOWN | Manual test runner |
| high_level_test.sh | Shell | UNKNOWN | Integration test |

### Test Quality Assessment

**Strengths**:
1. ✅ test_helper.bash has good mocking infrastructure
2. ✅ Mock gh CLI to prevent real API calls
3. ✅ Proper setup/teardown for test isolation
4. ✅ Test fixtures and config mocking in place
5. ✅ Good test organization with descriptive test names

**Weaknesses**:
1. ❌ Incorrect script path references (gh-epic-create.sh vs epic-create.sh)
2. ❌ Many tests marked as "skip" (TDD RED phase never completed)
3. ❌ Mix of BATS and shell test formats (inconsistent)
4. ❌ Shell test files incorrectly use BATS syntax (@test)
5. ❌ No test runner script to execute all tests
6. ❌ Limited edge case coverage

---

## Root Causes of Failing Tests

### Issue 1: Script Name Mismatch
**File**: gh-epic-create_test.bats
**Problem**: References `gh-epic-create.sh` but actual script is `epic-create.sh`
**Impact**: 2/2 active tests fail with "Command not found" (exit 127)
**Fix**: Update SCRIPT path in setup() function

### Issue 2: Shell Tests Use BATS Syntax
**Files**: gh-project-*.sh test files
**Problem**: Shell scripts (.sh) use BATS @test syntax
**Impact**: Cannot run with bash (syntax errors)
**Fix**: Either convert to .bats or rewrite as pure shell tests

### Issue 3: Skipped Tests Never Implemented
**Files**: Both BATS test files
**Problem**: Many tests marked "skip" from TDD RED phase
**Impact**: Low actual test coverage despite test file existence
**Fix**: Implement skipped tests with proper mocking

---

## Test Coverage by Script Type

### Pattern Analysis

Scripts follow consistent patterns by type:

1. **Create scripts** (6): epic/story/task/spike/bug-create.sh
   - Common: title arg, --body, --status, --priority, --labels, --format json, --dry-run
   - Unique: epic/story-create can have linked items

2. **List scripts** (5): epic/story/task/spike/bug-list.sh
   - Common: --status filter, --priority filter, --limit, --format json

3. **Update scripts** (5): epic/story/task/spike/bug-update.sh
   - Common: issue_number, --status, --priority, --title, --body, --dry-run

4. **Delete scripts** (5): epic/story/task/spike/bug-delete.sh
   - Common: issue_number, --archive, -y (skip confirm)

5. **Status transitions** (20): *-to-todo/in-progress/done/blocked.sh
   - All are simple wrappers calling *-update.sh with --status

6. **Link scripts** (3): epic/story/task-link.sh
   - Common: parent issue, child issue

7. **Special bug scripts** (2): bug-close.sh, bug-reopen.sh
   - Specific to bug lifecycle

8. **Project scripts** (9): Complex operations with templates and cloning

---

## Prioritized Test Creation Plan

### Phase 1: Fix Existing Tests (Priority: CRITICAL)
**Estimated Time**: 2 hours

1. Fix gh-epic-create_test.bats script path reference
2. Fix item_update_test.bats argument validation test
3. Convert gh-project-*.sh tests to proper BATS format
4. Un-skip and implement skipped tests in epic-create
5. Verify all existing tests pass

**Expected Output**: 10 passing test files

### Phase 2: Core CRUD Operations (Priority: HIGH)
**Estimated Time**: 6 hours

Create comprehensive tests for:
1. All create scripts (6): epic/story/task/spike/bug-create.sh
2. All list scripts (5): epic/story/task/spike/bug-list.sh
3. All update scripts (5): epic/story/task/spike/bug-update.sh
4. All delete scripts (5): epic/story/task/spike/bug-delete.sh

**Expected Output**: 21 test files covering core operations

### Phase 3: Status Transitions (Priority: MEDIUM)
**Estimated Time**: 2 hours

Create tests for all 20 status transition scripts:
- These are simple wrappers, so tests can follow a template
- Test argument forwarding and status value setting

**Expected Output**: 4 test files (one per status: todo/in-progress/done/blocked)

### Phase 4: Specialized Scripts (Priority: MEDIUM)
**Estimated Time**: 3 hours

1. Link scripts (3): epic/story/task-link.sh
2. Bug lifecycle (2): bug-close.sh, bug-reopen.sh
3. Utility (1): create-status-transitions.sh

**Expected Output**: 6 test files

### Phase 5: Project Management (Priority: LOW)
**Estimated Time**: 4 hours

Complete tests for complex project scripts:
1. project-clone.sh
2. project-export-to-template.sh
3. project-import-from-template.sh
4. project-link.sh

**Expected Output**: 4 test files

### Phase 6: Common Library Enhancement (Priority: LOW)
**Estimated Time**: 2 hours

Expand coverage for lib/gh-project-common.sh:
- GraphQL query execution
- Field cache operations
- ID resolution functions
- Retry logic

**Expected Output**: Enhanced common library tests

---

## Test Strategy & Patterns

### Standard Test Structure (Per Script Type)

#### Create Scripts Test Template
```bats
@test "script-name: shows help with --help"
@test "script-name: requires title argument"
@test "script-name: creates with title only"
@test "script-name: creates with body"
@test "script-name: creates with status"
@test "script-name: creates with priority"
@test "script-name: creates with assignee"
@test "script-name: creates with labels"
@test "script-name: outputs JSON with --format json"
@test "script-name: dry-run mode shows preview"
@test "script-name: sets Type field correctly"
@test "script-name: handles body-file option"
@test "script-name: fails on invalid status"
@test "script-name: fails on invalid priority"
```

#### List Scripts Test Template
```bats
@test "script-name: shows help with --help"
@test "script-name: lists all items by default"
@test "script-name: filters by status"
@test "script-name: filters by priority"
@test "script-name: limits results with --limit"
@test "script-name: outputs JSON with --format json"
@test "script-name: handles empty results"
@test "script-name: shows only Type=X items"
```

#### Update Scripts Test Template
```bats
@test "script-name: shows help with --help"
@test "script-name: requires issue number"
@test "script-name: requires at least one field"
@test "script-name: updates status"
@test "script-name: updates priority"
@test "script-name: updates title"
@test "script-name: updates body"
@test "script-name: updates multiple fields"
@test "script-name: dry-run shows preview"
@test "script-name: handles non-existent issue"
```

#### Status Transition Test Template
```bats
@test "script-name: shows help with --help"
@test "script-name: forwards to update script"
@test "script-name: sets correct status value"
@test "script-name: preserves additional arguments"
```

### Mocking Strategy

1. **gh CLI mocking** (critical):
   - Mock all gh commands in test_helper.bash
   - Return realistic JSON responses
   - Simulate errors for negative tests

2. **Config mocking**:
   - Use temporary test directory
   - Pre-populate with test config.json
   - Include field cache with test data

3. **File system mocking**:
   - All tests use $TEST_TEMP_DIR
   - Clean up in teardown()
   - No side effects on real filesystem

### Edge Cases to Test

1. **Input Validation**:
   - Missing required arguments
   - Invalid status values
   - Invalid priority values
   - Non-existent files (--body-file)

2. **Error Handling**:
   - Config not initialized
   - Network failures (API errors)
   - Non-existent issue numbers
   - Permission errors
   - Malformed JSON responses

3. **Special Cases**:
   - Empty strings
   - Very long inputs
   - Special characters in titles
   - Unicode in descriptions

---

## Test Infrastructure Improvements

### 1. Unified Test Runner
Create `run_all_tests.sh`:
```bash
#!/bin/bash
cd "$(dirname "$0")"
bats *.bats
```

### 2. Enhanced test_helper.bash
Add:
- More comprehensive gh CLI mocks
- Assertion helpers (assert_success, assert_failure, assert_output)
- Fixture loading utilities
- Better error messages

### 3. Test Fixtures
Create fixtures/ with:
- Sample GraphQL responses
- Sample config files
- Sample issue data
- Error responses

### 4. CI Integration
Create `.github/workflows/test-work-items.yml` for:
- Run tests on every commit
- Fail on any test failure
- Report coverage metrics

---

## Success Metrics

### Target Coverage Goals

- **Overall Coverage**: 100% (56/56 scripts with tests)
- **Test Pass Rate**: 100% (all tests passing)
- **Edge Case Coverage**: 80% (major edge cases tested)
- **Test Execution Time**: < 10 seconds for full suite
- **Test Isolation**: 100% (no external dependencies)

### Definition of "Tested"

A script is considered "tested" when it has:
1. ✅ Help flag test (--help returns usage)
2. ✅ Required argument validation tests
3. ✅ Happy path test (core functionality works)
4. ✅ At least 3 edge case tests
5. ✅ Dry-run test (if supported)
6. ✅ Error handling test (at least one failure case)

### Quality Criteria

- ✅ No real gh API calls in tests
- ✅ All tests are repeatable
- ✅ Tests run in < 10 seconds total
- ✅ Clear test names describing what is tested
- ✅ Proper setup/teardown for isolation
- ✅ Assertions verify behavior, not implementation

---

## Risk Assessment

### High Risk Areas

1. **Project Import/Export**: Complex JSON manipulation
   - Risk: Templates might not match current schema
   - Mitigation: Extensive fixture-based testing

2. **GraphQL Queries**: Complex field cache operations
   - Risk: Schema changes break queries
   - Mitigation: Mock all GraphQL responses

3. **Status Transitions**: 20 nearly-identical scripts
   - Risk: Copy-paste errors
   - Mitigation: Template-based testing approach

### Low Risk Areas

1. **Status Transition Scripts**: Simple wrappers
2. **Help Text**: Static content
3. **Argument Parsing**: Well-established patterns

---

## Recommendations

### Immediate Actions (This Sprint)

1. ✅ Fix failing BATS tests (1 hour)
2. ✅ Create test coverage for create scripts (4 hours)
3. ✅ Create test coverage for list scripts (3 hours)
4. ✅ Create test coverage for update scripts (3 hours)
5. ✅ Create test coverage for delete scripts (3 hours)

**Total**: ~14 hours for 80% coverage

### Future Improvements

1. Add integration tests with real (test) GitHub project
2. Add performance benchmarks
3. Add linting checks (shellcheck) to tests
4. Create test coverage report generator
5. Add mutation testing for robustness

### Technical Debt

1. Standardize test format (all BATS, no shell scripts)
2. Remove obsolete test files
3. Update all test references to use correct script names
4. Add code coverage metrics
5. Document testing patterns in README

---

## Appendix: Test File Naming Convention

**Current**: Inconsistent mix of patterns
**Proposed**: Standardize to match script names

| Script | Test File |
|--------|-----------|
| epic-create.sh | epic-create_test.bats |
| epic-list.sh | epic-list_test.bats |
| epic-update.sh | epic-update_test.bats |
| *-to-todo.sh | status-transitions_test.bats |
| lib/gh-project-common.sh | gh-project-common_test.bats |

**Benefits**:
- Easy to find corresponding test
- Alphabetically adjacent in listings
- Clear 1:1 mapping

---

## Conclusion

The work-items-project script library is production-quality code with minimal test coverage. Existing tests demonstrate good practices (mocking, isolation) but need fixes and expansion. With systematic effort, we can achieve 100% coverage within 15-20 hours using the phased approach outlined above.

**Next Steps**:
1. Execute Phase 1 (Fix existing tests)
2. Execute Phase 2 (Core CRUD operations)
3. Re-assess coverage and adjust plan

**Estimated Total Effort**: 19 hours for complete coverage
**Estimated Completion**: End of week (with focused effort)

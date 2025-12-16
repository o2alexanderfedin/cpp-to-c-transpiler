<objective>
Conduct a comprehensive testing audit of all scripts in ~/.claude/skills/lib/work-items-project/ and ensure complete unit test coverage using the BATS (Bash Automated Testing System) framework.

This testing work will:
1. Fix any failing existing tests
2. Add missing test coverage for all 70+ scripts
3. Ensure all scripts are thoroughly tested and production-ready
4. Provide confidence for future refactoring and maintenance

This is critical for maintaining code quality and preventing regressions as the script library evolves.
</objective>

<context>
The work-items-project directory contains 70+ production bash scripts for managing GitHub Projects v2:
- Core operations: epic, story, task, spike, bug (create, list, update, delete)
- Status transitions: 20 convenience scripts (*-to-todo.sh, *-to-in-progress.sh, etc.)
- Project management: init, export, import, clone, link
- Common library: lib/gh-project-common.sh with shared functions

Existing test infrastructure:
- Test directory: ~/.claude/skills/lib/work-items-project/tests/
- Framework: BATS (Bash Automated Testing System) already in use
- Existing test files with varying coverage

Read CLAUDE.md for project conventions including TDD requirements.
</context>

<requirements>
<audit_phase>
1. **Inventory all scripts**:
   - List all executable .sh files in work-items-project/
   - Categorize by type (epic, story, task, spike, bug, project, status-transition)
   - Count total scripts to test

2. **Assess existing test coverage**:
   - Run all existing tests in tests/ directory
   - Document which tests pass and which fail
   - Identify scripts with NO test coverage
   - Identify scripts with PARTIAL coverage (missing edge cases)
   - Calculate current coverage percentage

3. **Analyze test quality**:
   - Review existing test files for best practices
   - Check for proper mocking (gh CLI, jq, etc.)
   - Verify tests are isolated (no external dependencies)
   - Identify brittle tests that depend on real GitHub API
</audit_phase>

<fix_phase>
4. **Fix all failing tests**:
   - For each failing test, identify root cause
   - Update tests to work with renamed directory (gh-projects → work-items-project)
   - Fix path references in test helper files
   - Ensure mocking is correct and comprehensive
   - Re-run tests to verify fixes
</fix_phase>

<implementation_phase>
5. **Create comprehensive test coverage**:
   For EACH script type, create unit tests covering:

   **Common patterns for all scripts:**
   - Help flag (--help) returns usage information
   - Missing required arguments shows error
   - Invalid arguments show appropriate errors
   - Dry-run mode works correctly (--dry-run)
   - Script sources common library successfully
   - Environment variable handling

   **Type-specific tests:**

   **Create scripts** (epic-create.sh, story-create.sh, etc.):
   - Creates item with required fields
   - Sets custom fields (Type, Status, Priority)
   - Handles optional fields (body, labels, assignee)
   - Links to parent if specified (--epic, --story)
   - Returns issue number correctly
   - JSON output format works

   **List scripts** (epic-list.sh, story-list.sh, etc.):
   - Lists items of correct type
   - Filters by status work correctly
   - Filters by priority work correctly
   - Limit parameter works
   - JSON vs table output formats
   - Handles empty results gracefully

   **Update scripts** (*-update.sh):
   - Updates status field
   - Updates priority field
   - Updates multiple fields simultaneously
   - Handles non-existent issue numbers
   - Dry-run shows changes without applying

   **Delete scripts** (*-delete.sh):
   - Removes item from project
   - Archive option works (--archive)
   - Confirmation prompt works
   - Skip confirmation flag works (-y)
   - Handles already-deleted items

   **Status transition scripts** (*-to-*.sh):
   - Forwards arguments correctly to *-update.sh
   - Sets correct status value
   - Preserves additional arguments
   - Help flag works

   **Project scripts** (project-init.sh, project-export-to-template.sh, etc.):
   - Configuration file creation/loading
   - Field cache functionality
   - Template export/import
   - Project cloning
   - Error handling for missing projects

   **Common library** (lib/gh-project-common.sh):
   - Logging functions (log_success, log_error, etc.)
   - GraphQL query execution with retry
   - Field cache operations
   - ID resolution functions
   - Prerequisite validation

6. **Test organization**:
   - Group related tests in appropriately named files
   - Use BATS setup() and teardown() for test isolation
   - Create reusable test fixtures and helper functions
   - Follow existing test file naming: [script-name]_test.bats or [script-name]_test.sh
</implementation_phase>
</requirements>

<implementation_approach>
**Testing strategy:**

1. **Use mocking extensively** - Tests should NOT make real GitHub API calls:
   - Mock `gh` CLI commands using bash function overrides
   - Mock `jq` for JSON processing if needed
   - Create test fixtures for sample GraphQL responses
   - Use temporary directories for config files

2. **Test isolation**:
   - Each test should be independent (no shared state)
   - Use BATS setup() to create clean test environment
   - Use teardown() to clean up after tests
   - Never rely on external services or real project state

3. **Edge cases to test**:
   - Empty inputs
   - Invalid issue numbers
   - Missing configuration
   - Network failures (for retry logic)
   - Malformed JSON responses
   - Permission errors
   - Already-deleted items

4. **Follow existing patterns**:
   - Examine existing test files in tests/ directory
   - Use same mocking approach as existing tests
   - Maintain consistent assertion style
   - Use test_helper.bash if it exists

**Test file structure example:**
```bash
#!/usr/bin/env bats

load test_helper

setup() {
  # Create clean test environment
  export TEST_DIR="$(mktemp -d)"
  export HOME="$TEST_DIR"
  # Mock gh CLI
  gh() { echo "mocked gh command" }
  export -f gh
}

teardown() {
  rm -rf "$TEST_DIR"
}

@test "script-name shows help with --help flag" {
  run script-name.sh --help
  assert_success
  assert_output --partial "Usage:"
}

@test "script-name requires issue number" {
  run script-name.sh
  assert_failure
  assert_output --partial "required"
}
```
</implementation_approach>

<output>
Create/update the following files:

1. **Test audit report**: `./.prompts/021-testing-audit-report.md`
   - Summary of all scripts and their test status
   - List of failing tests with root causes
   - Coverage gaps identified
   - Prioritized test creation plan

2. **Test files** in `~/.claude/skills/lib/work-items-project/tests/`:
   - Fix existing test files
   - Create new test files for untested scripts
   - Update test_helper.bash if needed for shared utilities
   - Ensure all test files follow BATS conventions

3. **Test execution summary**: `./.prompts/021-test-results.md`
   - Results of running complete test suite
   - Coverage statistics (scripts tested / total scripts)
   - Any remaining gaps or known issues
   - Instructions for running tests
</output>

<verification>
Before declaring complete, verify your work by:

1. **Run the complete test suite**:
   ```bash
   cd ~/.claude/skills/lib/work-items-project/tests
   bats *.bats
   ```
   All tests should PASS.

2. **Coverage check**:
   - Count total scripts: `find ~/.claude/skills/lib/work-items-project -name "*.sh" -type f ! -path "*/tests/*" | wc -l`
   - Count scripts with tests: Review audit report
   - Target: 100% coverage (every script has at least basic tests)

3. **Test quality**:
   - No tests should make real GitHub API calls
   - All tests should be isolated and repeatable
   - Tests should run quickly (< 5 seconds for full suite)
   - No hardcoded paths or assumptions about environment

4. **Documentation**:
   - Test execution instructions are clear
   - Any test dependencies (bats installation) are documented
   - Known limitations or gaps are noted
</verification>

<success_criteria>
- All existing tests pass (0 failures)
- Every script in work-items-project/ has at least basic unit tests
- Tests use proper mocking (no real API calls)
- Tests are isolated and repeatable
- Coverage report shows 100% of scripts tested
- Test suite runs successfully on clean system
- Clear documentation for running and maintaining tests
</success_criteria>

<constraints>
- Use BATS framework exclusively (already in project)
- Follow existing test patterns and structure
- Do NOT make real GitHub API calls in tests
- Tests must work in isolation (no external dependencies)
- All test files must be executable and properly formatted
- Maintain backward compatibility with existing test infrastructure
</constraints>

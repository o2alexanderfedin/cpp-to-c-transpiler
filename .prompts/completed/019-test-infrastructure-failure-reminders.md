<objective>
Create comprehensive tests for the infrastructure failure reminder functionality to ensure all work-item scripts properly display the failure protocol reminder when errors occur.

This verifies that the infrastructure failure handling protocol is consistently enforced across all scripts, ensuring failures cannot be silently ignored.
</objective>

<context>
The work-items-project script library has been enhanced with infrastructure failure reminders (see prompt 018). Every script failure must now display a prominent reminder message instructing users to:
1. Pause execution
2. Spawn a task to investigate
3. Fix the root cause
4. Resume after verification

These tests ensure this critical safety mechanism is working correctly across all 45+ scripts in ~/.claude/skills/lib/work-items-project/.

Key implementation details:
- Helper function: `emit_infrastructure_failure_reminder()` in gh-project-common.sh
- All failures should go through `die()` which calls the reminder
- Reminder must appear on stderr with clear box formatting
- Original error messages must be preserved (reminder is additive)
</context>

<requirements>

**1. Test Suite Structure**

Create a BATS test suite at:
`~/.claude/skills/lib/work-items-project/tests/infrastructure-failure-reminders.bats`

**2. Test Coverage**

The test suite must verify:

**A. Helper Function Existence**
- `emit_infrastructure_failure_reminder()` function exists in gh-project-common.sh
- Function is properly defined (no syntax errors)
- Function can be called successfully

**B. die() Function Integration**
- `die()` function calls `emit_infrastructure_failure_reminder()`
- Reminder appears after error message
- Output goes to stderr (not stdout)

**C. Reminder Content Validation**
- Reminder contains all required elements:
  - "INFRASTRUCTURE FAILURE DETECTED" header
  - "PAUSE execution immediately"
  - "SPAWN a separate task to investigate"
  - "FIX the root cause (no workarounds)"
  - "RESUME only after fix is verified"
  - "No attempts to hide the problem!"
  - Box formatting (═══ borders)

**D. Real-World Failure Scenarios**
Test actual script failures to ensure reminders appear:
- Invalid story number (story-view.sh with non-existent ID)
- Missing project configuration
- GitHub API failures (simulated)
- Invalid field values

**E. Stderr vs Stdout**
- Error messages go to stderr
- Reminder box goes to stderr
- No reminder pollution on stdout

**F. Box Formatting Integrity**
- Box borders render correctly (═══)
- Line lengths are consistent
- Visual structure is preserved

**3. Test Implementation Patterns**

Use these BATS patterns:

```bash
@test "emit_infrastructure_failure_reminder function exists" {
  source ~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh

  # Verify function is defined
  type emit_infrastructure_failure_reminder

  # Should return 0 (function exists)
  [ $? -eq 0 ]
}

@test "die() calls infrastructure failure reminder" {
  source ~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh

  # Capture stderr
  output=$(die "Test error" 2>&1 || true)

  # Should contain error message
  [[ "$output" == *"Test error"* ]]

  # Should contain reminder
  [[ "$output" == *"INFRASTRUCTURE FAILURE DETECTED"* ]]
  [[ "$output" == *"PAUSE execution immediately"* ]]
}

@test "reminder appears on stderr not stdout" {
  source ~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh

  # Capture stdout and stderr separately
  stdout=$(emit_infrastructure_failure_reminder 2>/dev/null)
  stderr=$(emit_infrastructure_failure_reminder 2>&1 1>/dev/null)

  # Stdout should be empty
  [ -z "$stdout" ]

  # Stderr should contain reminder
  [[ "$stderr" == *"INFRASTRUCTURE FAILURE DETECTED"* ]]
}

@test "reminder contains all required protocol steps" {
  source ~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh

  output=$(emit_infrastructure_failure_reminder 2>&1)

  # Verify all protocol steps present
  [[ "$output" == *"1. PAUSE execution immediately"* ]]
  [[ "$output" == *"2. SPAWN a separate task to investigate"* ]]
  [[ "$output" == *"3. FIX the root cause (no workarounds)"* ]]
  [[ "$output" == *"4. RESUME only after fix is verified"* ]]
  [[ "$output" == *"No attempts to hide the problem!"* ]]
}

@test "real script failure shows reminder" {
  # Test with actual script that will fail
  output=$(~/.claude/skills/lib/work-items-project/story-view.sh 99999 2>&1 || true)

  # Should contain infrastructure failure reminder
  [[ "$output" == *"INFRASTRUCTURE FAILURE DETECTED"* ]]
}
```

**4. Edge Cases to Test**

- Multiple sequential failures (reminder appears each time)
- Nested function calls (reminder appears at top level)
- Signal interruption (Ctrl+C handling)
- Reminder doesn't break script exit codes (should still exit 1)

**5. Performance Check**

- Reminder emission should be fast (<100ms)
- No significant overhead on script execution time

</requirements>

<implementation>

**Step 1: Create Test Directory**

Ensure ~/.claude/skills/lib/work-items-project/tests/ exists:
```bash
mkdir -p ~/.claude/skills/lib/work-items-project/tests/
```

**Step 2: Create BATS Test Suite**

Create comprehensive test file:
`~/.claude/skills/lib/work-items-project/tests/infrastructure-failure-reminders.bats`

**Step 3: Organize Tests into Logical Sections**

```bash
#!/usr/bin/env bats

# Section 1: Function Existence Tests
@test "..." { }

# Section 2: Integration Tests
@test "..." { }

# Section 3: Content Validation Tests
@test "..." { }

# Section 4: Real-World Scenarios
@test "..." { }

# Section 5: Edge Cases
@test "..." { }
```

**Step 4: Add Test Utilities**

Create helper functions for common test operations:

```bash
# Helper: Capture stderr
capture_stderr() {
  "$@" 2>&1 1>/dev/null
}

# Helper: Count reminder occurrences
count_reminders() {
  local output="$1"
  echo "$output" | grep -c "INFRASTRUCTURE FAILURE DETECTED" || echo "0"
}
```

**Step 5: Create Test Runner Script**

Create `~/.claude/skills/lib/work-items-project/tests/run-failure-reminder-tests.sh`:

```bash
#!/bin/bash
set -euo pipefail

cd ~/.claude/skills/lib/work-items-project

echo "Running Infrastructure Failure Reminder Tests..."
echo ""

bats tests/infrastructure-failure-reminders.bats

echo ""
echo "Test suite complete!"
```

Make it executable:
```bash
chmod +x ~/.claude/skills/lib/work-items-project/tests/run-failure-reminder-tests.sh
```

</implementation>

<validation>

**Integration with Existing Tests**

Ensure these new tests integrate with the existing test infrastructure:
- Check if there's a main test runner that should include this suite
- Update test coverage reporting if it exists
- Add to CI/CD pipeline if present

**Test the Tests**

Before declaring complete:
1. Run the test suite: `bats ~/.claude/skills/lib/work-items-project/tests/infrastructure-failure-reminders.bats`
2. All tests should PASS (assuming prompt 018 was executed first)
3. If prompt 018 hasn't been executed, tests should FAIL appropriately (showing what's missing)

**Coverage Report**

After running tests, generate a simple coverage summary showing:
- Total tests: X
- Passed: Y
- Failed: Z
- Coverage areas: function existence, integration, content, real-world, edge cases

</validation>

<verification>

Before declaring complete, verify:

1. **Test file created**: `ls -la ~/.claude/skills/lib/work-items-project/tests/infrastructure-failure-reminders.bats`

2. **Test file is executable**: BATS can load and parse it

3. **All test categories covered**:
   - Function existence (3+ tests)
   - die() integration (2+ tests)
   - Content validation (4+ tests)
   - Real-world scenarios (3+ tests)
   - Edge cases (2+ tests)
   - Stderr/stdout separation (2+ tests)

4. **Tests are runnable**: Execute the test suite and confirm it runs without errors

5. **Tests are meaningful**: Each test verifies a specific requirement, not just existence

6. **Test output is clear**: Failures provide actionable information about what's wrong

</verification>

<output>

Create these files:
- `~/.claude/skills/lib/work-items-project/tests/infrastructure-failure-reminders.bats` - Main test suite
- `~/.claude/skills/lib/work-items-project/tests/run-failure-reminder-tests.sh` - Test runner script

Update if exists:
- Test coverage report
- Main test runner (to include new suite)

</output>

<success_criteria>

- Comprehensive BATS test suite created with 15+ tests
- All aspects of infrastructure failure reminders are tested:
  - Function existence and definition
  - Integration with die()
  - Complete protocol message content
  - Stderr vs stdout behavior
  - Real-world failure scenarios
  - Edge cases and error conditions
- Tests pass when prompt 018 implementation is present
- Tests fail meaningfully when implementation is missing
- Test runner script created and executable
- Clear documentation of what each test verifies
- Tests can be run independently or as part of larger suite

This ensures the critical infrastructure failure reminder mechanism is thoroughly validated and will continue to work correctly as the codebase evolves.

</success_criteria>

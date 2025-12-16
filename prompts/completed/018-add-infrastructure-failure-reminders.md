<objective>
Add infrastructure failure reminder messages to all work-item scripts to ensure failures are properly investigated rather than hidden.

This implements a critical requirement: when any script in ~/.claude/skills/lib/work-items-project/ fails, it must emit a clear reminder message instructing the user (or Claude) to pause execution, spawn a separate task to investigate and fix the failure, then resume. This ensures infrastructure problems are systematically addressed rather than being worked around or ignored.
</objective>

<context>
The work-items-project script library at ~/.claude/skills/lib/work-items-project/ contains 45+ bash scripts for managing GitHub Project work items (stories, epics, tasks, bugs).

Recent issues have shown that script failures can be silently ignored or worked around, leading to delayed fixes. The user has established a protocol:

**"In case of any infrastructure/script failure - pause the execution, spawn a separate task to investigate the failure and fix, then resume. No attempts to hide the problem!"**

This protocol must be enforced at the script level through clear, visible reminder messages.

Key files to examine:
- @~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh - Core library functions
- @~/.claude/skills/lib/work-items-project/*.sh - All script entry points (story-*, epic-*, task-*, bug-*)
</context>

<requirements>

**1. Standardized Failure Reminder Message**

Create a standard reminder message that all scripts must emit on failure:

```bash
echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "⚠️  INFRASTRUCTURE FAILURE DETECTED"
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo "**IMPORTANT**: In case of any infrastructure/script failure:"
echo ""
echo "  1. PAUSE execution immediately"
echo "  2. SPAWN a separate task to investigate the failure"
echo "  3. FIX the root cause (no workarounds)"
echo "  4. RESUME only after fix is verified"
echo ""
echo "No attempts to hide the problem!"
echo ""
echo "═══════════════════════════════════════════════════════════════"
echo ""
```

**2. Implementation Pattern**

Add this reminder to all error exit points:

- After `die()` function calls in gh-project-common.sh
- In script-specific error handlers
- Before `exit 1` statements
- In trap handlers for critical failures

**3. Scope**

Apply to all scripts in:
- ~/.claude/skills/lib/work-items-project/*.sh (entry point scripts)
- ~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh (core library)

**4. Preserve Existing Error Messages**

Do NOT replace existing error messages - ADD the reminder after them:

```bash
# BEFORE
die "Story #$story_num not found in project"

# AFTER
die "Story #$story_num not found in project"
emit_infrastructure_failure_reminder
```

**5. Create Helper Function**

Add to gh-project-common.sh:

```bash
# Emit infrastructure failure reminder
emit_infrastructure_failure_reminder() {
  echo "" >&2
  echo "═══════════════════════════════════════════════════════════════" >&2
  echo "⚠️  INFRASTRUCTURE FAILURE DETECTED" >&2
  echo "═══════════════════════════════════════════════════════════════" >&2
  echo "" >&2
  echo "**IMPORTANT**: In case of any infrastructure/script failure:" >&2
  echo "" >&2
  echo "  1. PAUSE execution immediately" >&2
  echo "  2. SPAWN a separate task to investigate the failure" >&2
  echo "  3. FIX the root cause (no workarounds)" >&2
  echo "  4. RESUME only after fix is verified" >&2
  echo "" >&2
  echo "No attempts to hide the problem!" >&2
  echo "" >&2
  echo "═══════════════════════════════════════════════════════════════" >&2
  echo "" >&2
}
```

</requirements>

<implementation>

**Step 1: Add Helper Function to gh-project-common.sh**

Add `emit_infrastructure_failure_reminder()` function to ~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh near other utility functions (after `log_*` functions).

**Step 2: Update die() Function**

Modify the `die()` function in gh-project-common.sh to automatically call the reminder:

```bash
die() {
  log_error "$@" >&2
  emit_infrastructure_failure_reminder
  exit 1
}
```

**Step 3: Add to Script-Specific Error Handlers**

For each script that has custom error handling (not using die()), add the reminder before exit:

```bash
# Example pattern
if [[ condition_that_should_not_fail ]]; then
  echo "ERROR: Unexpected condition" >&2
  emit_infrastructure_failure_reminder
  exit 1
fi
```

**Step 4: Add to Critical Function Failures**

For critical functions in gh-project-common.sh that can fail silently, add explicit checks and reminders:

- `get_item_by_issue()` - if item not found
- `set_item_field()` - if field update fails
- `item_view()` - if GraphQL query fails

**Step 5: Test the Implementation**

Create a test script that triggers a failure to verify the reminder appears:

```bash
#!/bin/bash
source ~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh
die "Test infrastructure failure"
```

Expected output: Error message followed by the formatted reminder box.

</implementation>

<verification>

Before declaring complete, verify:

1. **Helper function exists**: `grep -n "emit_infrastructure_failure_reminder" ~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh`

2. **die() function updated**: Check that die() calls emit_infrastructure_failure_reminder

3. **Test actual failure**: Run a script with known failure condition (e.g., `story-view.sh 99999`) and confirm:
   - Original error message appears
   - Reminder box appears after error
   - Messages go to stderr (>&2)
   - Box formatting is intact

4. **No broken scripts**: Source gh-project-common.sh in a clean shell to ensure no syntax errors

5. **All entry points covered**: Check that major scripts (story-*, epic-*, task-*, bug-*) properly source gh-project-common.sh and will inherit the behavior

</verification>

<output>

Modified files:
- `~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh` - Add helper function and update die()
- Any scripts with custom error handlers - Add reminder calls

No new files created - this is an enhancement to existing error handling.

</output>

<success_criteria>

- emit_infrastructure_failure_reminder() function added to gh-project-common.sh
- die() function updated to call the reminder automatically
- All script failures now display the infrastructure failure reminder
- Reminder message is clearly visible (box formatting with ═══ borders)
- Messages go to stderr (>&2) not stdout
- Existing error messages preserved (reminder is additive)
- No scripts broken by the changes
- Manual test confirms reminder appears on actual failure

This ensures that every infrastructure failure triggers a clear, visible protocol reminder that cannot be missed.

</success_criteria>

# Meta-Prompt: PreToolUse Hook Enforcement Experimentation

## Objective

Implement and thoroughly test three different approaches to enforcing script abstraction usage in Claude Code skills via PreToolUse hooks. Compare approaches based on effectiveness, maintainability, and usability. Provide a comprehensive recommendation.

## Context

**Problem**: Skills can bypass the script abstraction layer (`~/.claude/skills/lib/work-items-project/*.sh`) by directly calling `gh` CLI commands, violating the portability and maintainability architecture.

**Script Library**: 61 production scripts providing:
- Epic operations: `epic-*.sh`
- Story operations: `story-*.sh`
- Task operations: `task-*.sh`
- Bug operations: `bug-*.sh`
- Spike operations: `spike-*.sh`
- Project operations: `project-*.sh`

**Target Skills** (must use script abstractions):
- `execute-user-story`
- `suggest-next-story`
- `execute-next-story`
- `epic-to-user-stories`
- `prd-to-epics`

## Three Approaches to Implement

### Approach 1: Self-Scoping by Command Pattern
- Hook validates ALL Bash commands
- Checks if command uses `gh` CLI directly
- Exempts commands calling script library
- Simple pattern matching, no skill detection

### Approach 2: Transcript-Based Skill Detection
- Hook reads session transcript to detect active skill
- Only enforces for skills in allowlist
- Precise control per skill
- More complex implementation

### Approach 3: Description Field Markers
- Skills add `[ENFORCE_ABSTRACTIONS]` marker to Bash descriptions
- Hook checks description field for marker
- Explicit opt-in per command
- Requires skill modifications

## Implementation Requirements

### Phase 1: Setup (Research)
1. Create directory structure:
   ```
   ~/.claude/hooks/
   ├── validators/
   │   ├── approach1-self-scoping.sh
   │   ├── approach2-transcript-based.sh
   │   ├── approach3-description-markers.sh
   │   └── common-validation-lib.sh
   ├── configs/
   │   ├── approach1-config.json
   │   ├── approach2-config.json
   │   └── approach3-config.json
   └── tests/
       ├── test-approach1.sh
       ├── test-approach2.sh
       └── test-approach3.sh
   ```

2. Research PreToolUse hook capabilities:
   - Read `~/.claude/skills/create-hooks/references/hook-types.md`
   - Understand input schema: `session_id`, `transcript_path`, `cwd`, `tool_name`, `tool_input`
   - Understand output schema: `decision`, `reason`, `systemMessage`, `updatedInput`
   - Review existing hooks in `~/.claude/.githooks/`

### Phase 2: Implement Approach 1 (Self-Scoping)

**Validator Script**: `~/.claude/hooks/validators/approach1-self-scoping.sh`

Requirements:
- Accept command as `$1`
- Detect `gh issue`, `gh pr`, `gh project`, `gh api` patterns
- Exempt commands containing `~/.claude/skills/lib/work-items-project/`
- Return JSON: `{"decision": "approve|block", "reason": "...", "systemMessage": "..."}`
- Include helpful error messages with correct script alternatives
- Handle edge cases: comments, subshells, pipes

**Hook Config**: `~/.claude/hooks/configs/approach1-config.json`

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/hooks/validators/approach1-self-scoping.sh \"$tool_input.command\""
          }
        ]
      }
    ]
  }
}
```

**Test Cases**: `~/.claude/hooks/tests/test-approach1.sh`

Test scenarios:
1. ✅ Direct `gh issue list` → BLOCK
2. ✅ Direct `gh issue view 48` → BLOCK
3. ✅ Direct `gh project item-list` → BLOCK
4. ✅ Script call `story-list.sh --epic 48` → APPROVE
5. ✅ Script call `~/.claude/skills/lib/work-items-project/story-view.sh 123` → APPROVE
6. ✅ Non-gh command `npm install` → APPROVE
7. ✅ Git command `git status` → APPROVE
8. ✅ Commented gh `# gh issue list` → APPROVE (false positive acceptable)
9. ✅ Complex command `cd /tmp && gh issue list` → BLOCK

**Documentation**: `~/.claude/hooks/validators/approach1-README.md`
- How it works
- Pros and cons
- Installation instructions
- Troubleshooting guide

### Phase 3: Implement Approach 2 (Transcript-Based)

**Validator Script**: `~/.claude/hooks/validators/approach2-transcript-based.sh`

Requirements:
- Accept command as `$1`, transcript path as `$2`
- Parse transcript to identify active skill
- Check if skill is in enforcement list
- Only validate gh commands if skill requires it
- Handle transcript parsing errors gracefully
- Cache skill detection to avoid repeated parsing

**Skill Detection Logic**:
```bash
# Extract active skill from transcript
ACTIVE_SKILL=$(grep -o '"skill":\s*"[^"]*"' "$TRANSCRIPT_PATH" | tail -1 | cut -d'"' -f4)

# Enforced skills list
ENFORCED_SKILLS=(
  "execute-user-story"
  "suggest-next-story"
  "execute-next-story"
  "epic-to-user-stories"
  "prd-to-epics"
)
```

**Hook Config**: `~/.claude/hooks/configs/approach2-config.json`

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/hooks/validators/approach2-transcript-based.sh \"$tool_input.command\" \"$transcript_path\""
          }
        ]
      }
    ]
  }
}
```

**Test Cases**: `~/.claude/hooks/tests/test-approach2.sh`

Test scenarios:
1. ✅ In `execute-user-story` skill, direct gh → BLOCK
2. ✅ In `execute-user-story` skill, script call → APPROVE
3. ✅ In different skill (not enforced), direct gh → APPROVE
4. ✅ No active skill, direct gh → APPROVE
5. ✅ Transcript parse error → APPROVE (fail open)
6. ✅ Empty transcript → APPROVE

**Documentation**: `~/.claude/hooks/validators/approach2-README.md`

### Phase 4: Implement Approach 3 (Description Markers)

**Validator Script**: `~/.claude/hooks/validators/approach3-description-markers.sh`

Requirements:
- Accept command as `$1`, description as `$2`
- Check for `[ENFORCE_ABSTRACTIONS]` marker
- Only validate if marker present
- Provide clear feedback about marker usage

**Hook Config**: `~/.claude/hooks/configs/approach3-config.json`

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/hooks/validators/approach3-description-markers.sh \"$tool_input.command\" \"$tool_input.description\""
          }
        ]
      }
    ]
  }
}
```

**Skill Modification Example**:

Update `suggest-next-story/SKILL.md` to document marker usage:

```xml
<bash_command_requirements>
All Bash commands in this skill MUST include the `[ENFORCE_ABSTRACTIONS]` marker in descriptions:

```python
# ✅ CORRECT
Bash(
  command="~/.claude/skills/lib/work-items-project/story-list.sh --epic 48 --format json",
  description="[ENFORCE_ABSTRACTIONS] Load stories for Epic 48"
)

# ❌ INCORRECT - Will be blocked if direct gh used
Bash(
  command="gh issue list",
  description="List issues"
)
```

The PreToolUse hook will enforce script abstraction usage for any command with this marker.
</bash_command_requirements>
```

**Test Cases**: `~/.claude/hooks/tests/test-approach3.sh`

Test scenarios:
1. ✅ With marker, direct gh → BLOCK
2. ✅ With marker, script call → APPROVE
3. ✅ Without marker, direct gh → APPROVE
4. ✅ Without marker, script call → APPROVE
5. ✅ Empty description, direct gh → APPROVE
6. ✅ Marker in wrong position → Still detect

**Documentation**: `~/.claude/hooks/validators/approach3-README.md`

### Phase 5: Common Validation Library

Create `~/.claude/hooks/validators/common-validation-lib.sh`:

```bash
#!/bin/bash
# Common validation functions used by all approaches

# Check if command uses gh CLI directly
is_direct_gh_command() {
  local cmd="$1"
  [[ "$cmd" =~ gh[[:space:]]+(issue|pr|project|api) ]]
}

# Check if command uses script library
uses_script_library() {
  local cmd="$1"
  [[ "$cmd" == *"~/.claude/skills/lib/work-items-project/"* ]]
}

# Generate block response
generate_block_response() {
  local command="$1"
  local reason="$2"

  # Suggest correct script based on gh command
  local suggestion=""
  case "$command" in
    *"gh issue list"*) suggestion="story-list.sh --epic NUM --format json" ;;
    *"gh issue view"*) suggestion="story-view.sh STORY_NUM" ;;
    *"gh project"*) suggestion="project-*.sh (see ~/.claude/skills/lib/work-items-project/)" ;;
  esac

  cat <<EOF
{
  "decision": "block",
  "reason": "$reason",
  "systemMessage": "⛔ BLOCKED: Direct gh CLI usage\\n\\nUse script abstraction instead:\\n  $suggestion\\n\\nAll scripts: ~/.claude/skills/lib/work-items-project/"
}
EOF
}

# Generate approve response
generate_approve_response() {
  local reason="${1:-OK}"
  echo "{\"decision\": \"approve\", \"reason\": \"$reason\"}"
}
```

### Phase 6: Testing Framework

Create comprehensive test suite for each approach:

**Test Script Template**: `~/.claude/hooks/tests/test-approach-template.sh`

```bash
#!/bin/bash
set -euo pipefail

APPROACH="${1:-1}"
VALIDATOR="$HOME/.claude/hooks/validators/approach${APPROACH}-*.sh"

echo "Testing Approach $APPROACH..."

# Test counter
TOTAL=0
PASSED=0
FAILED=0

test_case() {
  local name="$1"
  local command="$2"
  local expected_decision="$3"
  shift 3
  local extra_args=("$@")

  TOTAL=$((TOTAL + 1))
  echo -n "Test $TOTAL: $name ... "

  result=$("$VALIDATOR" "$command" "${extra_args[@]}" 2>/dev/null || echo '{"decision":"error"}')
  decision=$(echo "$result" | jq -r '.decision')

  if [[ "$decision" == "$expected_decision" ]]; then
    echo "✅ PASSED"
    PASSED=$((PASSED + 1))
  else
    echo "❌ FAILED (expected: $expected_decision, got: $decision)"
    FAILED=$((FAILED + 1))
  fi
}

# Run tests
test_case "Block direct gh issue list" "gh issue list" "block"
test_case "Block direct gh issue view" "gh issue view 48" "block"
test_case "Approve script library call" "~/.claude/skills/lib/work-items-project/story-list.sh --epic 48" "approve"
test_case "Approve non-gh command" "npm install" "approve"
test_case "Approve git command" "git status" "approve"

# Summary
echo ""
echo "=========================================="
echo "Test Results: $PASSED/$TOTAL passed"
if [[ $FAILED -gt 0 ]]; then
  echo "FAILED: $FAILED tests"
  exit 1
else
  echo "SUCCESS: All tests passed"
  exit 0
fi
```

### Phase 7: Comparison and Analysis

Create `~/.claude/hooks/COMPARISON.md` with detailed analysis:

**Comparison Matrix**:

| Criterion | Approach 1 | Approach 2 | Approach 3 |
|-----------|------------|------------|------------|
| **Setup Complexity** | Low | Medium | Medium |
| **Skill Modifications Required** | None | None | Yes (descriptions) |
| **Precision** | Global | Per-skill | Per-command |
| **Maintainability** | High | Medium | Low |
| **Performance** | Fast | Slow (transcript parsing) | Fast |
| **False Positives** | Low | Very Low | Very Low |
| **Error Handling** | Simple | Complex | Simple |
| **Debugging** | Easy | Moderate | Easy |
| **Extensibility** | Medium | High | High |
| **User Experience** | Clear errors | Context-aware errors | Explicit opt-in |

**Evaluation Criteria**:

1. **Effectiveness**: Does it prevent unauthorized gh usage?
2. **Precision**: Does it only block what it should?
3. **Maintainability**: How easy to update/extend?
4. **Performance**: Impact on command execution time?
5. **User Experience**: Quality of error messages?
6. **Debuggability**: How easy to troubleshoot?
7. **Flexibility**: Can it adapt to new requirements?
8. **Robustness**: How does it handle edge cases?

**Test Each Approach**:

1. Install hook configuration
2. Run test suite
3. Manually test with real skills:
   - `/suggest-next-story 48` (should use scripts)
   - Try to bypass with direct gh (should block)
   - Verify normal operations work
4. Measure performance (time overhead per command)
5. Test error scenarios:
   - Missing script library
   - Malformed commands
   - Transcript corruption (Approach 2)
   - Missing description (Approach 3)

### Phase 8: Documentation Deliverables

Create comprehensive documentation:

1. **Installation Guide**: `~/.claude/hooks/INSTALLATION.md`
   - Prerequisites
   - Step-by-step setup for each approach
   - Verification steps
   - Troubleshooting

2. **User Guide**: `~/.claude/hooks/USER-GUIDE.md`
   - How enforcement works
   - What to do when blocked
   - How to use script library
   - Common errors and solutions

3. **Developer Guide**: `~/.claude/hooks/DEVELOPER-GUIDE.md`
   - How to add new scripts to library
   - How to modify enforcement rules
   - How to add new enforced skills
   - Hook debugging techniques

4. **Comparison Report**: `~/.claude/hooks/COMPARISON.md`
   - Detailed comparison of all three approaches
   - Test results and metrics
   - Pros/cons for each
   - Recommendation with rationale

5. **Architecture Document**: `~/.claude/hooks/ARCHITECTURE.md`
   - System overview
   - Component interactions
   - Data flow diagrams
   - Security considerations

## Success Criteria

✅ All three approaches implemented and tested
✅ Test suites created with 100% pass rate for each approach
✅ Performance measured (< 50ms overhead acceptable)
✅ Complete documentation for all approaches
✅ Comparison matrix filled with objective data
✅ Clear recommendation with rationale
✅ Installation scripts ready for deployment
✅ Real-world testing with target skills completed
✅ Edge cases identified and documented
✅ Migration path documented for chosen approach

## Deliverables

1. Three working validator scripts
2. Three hook configurations
3. Three test suites
4. Common validation library
5. Comprehensive documentation (5 documents)
6. Comparison matrix with test results
7. Final recommendation report
8. Installation/deployment scripts

## Execution Guidelines

- Use parallel Task agents where applicable for independent work
- Follow TDD: write tests before implementing validators
- Document as you go, not at the end
- Test each approach thoroughly before moving to comparison
- Use real skills for integration testing
- Consider edge cases and failure modes
- Measure and document performance impact
- Get user feedback on error message quality

## Timeline Estimate

- Phase 1 (Setup): 30 minutes
- Phase 2 (Approach 1): 1 hour
- Phase 3 (Approach 2): 1.5 hours
- Phase 4 (Approach 3): 1.5 hours
- Phase 5 (Common lib): 30 minutes
- Phase 6 (Testing): 1 hour
- Phase 7 (Comparison): 1 hour
- Phase 8 (Documentation): 1.5 hours

Total: ~8 hours of focused work

## Notes

- Fail-safe: Validators should approve on errors (fail open), not block
- Logging: All decisions should be logged for analysis
- Backwards compatibility: Existing skills must continue working
- Performance: Minimal impact on command execution critical
- User experience: Error messages must be helpful, not frustrating

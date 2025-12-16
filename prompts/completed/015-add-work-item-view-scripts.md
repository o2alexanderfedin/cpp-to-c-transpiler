<objective>
Add type-specific view/query scripts for work items (epic/story/task/spike/bug) to the work-items-project script suite.

These scripts will query detailed information for specific work items by issue number, returning full JSON data including Project custom fields and repository issue metadata. This fills a gap in the current script suite which has create/list/update/delete/status-transition scripts but lacks individual item query capabilities.

The scripts will be used by Claude Code skills (execute-user-story, execute-epic, etc.) and by users who need to inspect work item details programmatically.
</objective>

<context>
**Current state:**
- Script location: `~/.claude/skills/lib/work-items-project/`
- Existing patterns: Type-specific scripts (epic-*, story-*, task-*, spike-*, bug-*)
- Testing framework: BATS (Bash Automated Testing System)
- Test location: `~/.claude/skills/lib/work-items-project/tests/`
- Documentation: `~/.claude/skills/execute-user-story/references/script-usage.md`

**Current gap:**
Users currently use native `gh issue view` for querying work item details, but we need work-items-project wrapper scripts that:
1. Follow the same conventions as other type-specific scripts
2. Provide consistent error handling and validation
3. Support both JSON and human-readable text output
4. Can be easily tested and mocked in BATS tests

**Related files to examine:**
@~/.claude/skills/lib/work-items-project/epic-list.sh
@~/.claude/skills/lib/work-items-project/story-list.sh
@~/.claude/skills/lib/work-items-project/tests/test_epic_scripts.bats
@~/.claude/skills/lib/work-items-project/tests/test_helper.bash
@~/.claude/skills/execute-user-story/references/script-usage.md
</context>

<requirements>

## Functional Requirements

1. **Create 5 view scripts** (one per type):
   - `epic-view.sh ISSUE_NUM [--format json|text] [--json FIELDS]`
   - `story-view.sh ISSUE_NUM [--format json|text] [--json FIELDS]`
   - `task-view.sh ISSUE_NUM [--format json|text] [--json FIELDS]`
   - `spike-view.sh ISSUE_NUM [--format json|text] [--json FIELDS]`
   - `bug-view.sh ISSUE_NUM [--format json|text] [--json FIELDS]`

2. **Script behavior**:
   - Accept issue number as positional argument (required)
   - Support `--format` flag: `json` (default) or `text` (human-readable)
   - Support `--json FIELDS` flag: comma-separated list of specific fields to return
   - Query both GitHub Project custom fields AND repository issue data
   - Return unified JSON combining Project + Issue data
   - Validate that issue exists and is the correct type
   - Exit with error if issue not found or wrong type

3. **Output format (JSON)**:
   ```json
   {
     "number": 109,
     "title": "Story title",
     "body": "Story description...",
     "state": "OPEN",
     "status": "In Progress",
     "type": "User Story",
     "storyPoints": 5,
     "epic": "Epic #42",
     "labels": [{"name": "enhancement"}],
     "assignees": [{"login": "username"}],
     "url": "https://github.com/owner/repo/issues/109",
     "createdAt": "2025-12-01T10:00:00Z",
     "updatedAt": "2025-12-14T15:30:00Z"
   }
   ```

4. **Output format (text)**:
   ```
   Story #109: Story title

   Project Status: In Progress
   Issue State: OPEN
   Type: User Story
   Story Points: 5
   Epic: Epic #42

   URL: https://github.com/owner/repo/issues/109
   Created: 2025-12-01T10:00:00Z
   Updated: 2025-12-14T15:30:00Z

   Labels: enhancement

   Body:
   ---
   Story description...
   ---
   ```

5. **Error handling**:
   - Exit code 1 with clear error message if:
     - Issue number not provided
     - Issue not found in repository
     - Issue not found in Project
     - Issue exists but is wrong type (e.g., asking for story-view on an Epic)
   - All error messages go to stderr

## Testing Requirements

6. **Create comprehensive BATS tests**:
   - Test file: `~/.claude/skills/lib/work-items-project/tests/test_view_scripts.bats`
   - Test all 5 scripts (epic-view, story-view, task-view, spike-view, bug-view)
   - Mock `gh` CLI commands (follow existing test_helper.bash patterns)
   - Test scenarios:
     - Success: Valid issue number returns correct JSON
     - Success: --format text returns human-readable output
     - Success: --json fields returns only requested fields
     - Error: Missing issue number
     - Error: Issue not found
     - Error: Wrong type (e.g., story-view.sh on Epic #1)
   - All tests must pass without making real GitHub API calls
   - Follow existing BATS test patterns from test_epic_scripts.bats

## Documentation Requirements

7. **Update script-usage.md**:
   - Add section for view scripts under appropriate category
   - Document parameters, return values, examples, error handling
   - Follow existing documentation patterns
   - Include "When to Use" guidance

8. **Update skills**:
   - Review execute-user-story skill for places that use `gh issue view`
   - Assess whether to replace with new type-specific view scripts
   - Document rationale (when to use native `gh issue view` vs wrapper scripts)

</requirements>

<implementation>

## Design Patterns to Follow

**SOLID Principles:**
- **Single Responsibility**: Each script queries one type of work item
- **Open/Closed**: Extend via new scripts, don't modify existing ones
- **DRY**: Extract common logic to lib/gh-project-common.sh if needed

**KISS (Keep It Simple):**
- Straightforward wrapper around `gh issue view` and `gh project item-list`
- Minimal complexity - these are query scripts, not mutation scripts
- Use native `gh` commands where possible

**Portable Paths:**
- All paths use `~/.claude/skills/lib/work-items-project/`
- Never expand home directory in script references

**Testing:**
- Mock all `gh` commands in tests
- No real API calls during test execution
- Fast, isolated, repeatable tests

## Implementation Approach

1. **Study existing patterns** by examining:
   - `epic-list.sh` for query pattern
   - `epic-to-done.sh` for parameter parsing
   - `test_epic_scripts.bats` for testing patterns
   - `test_helper.bash` for mocking utilities

2. **Implement scripts sequentially**:
   - Start with epic-view.sh (use as template)
   - Copy pattern to story-view.sh, task-view.sh, spike-view.sh, bug-view.sh
   - Adjust type validation for each

3. **Add common logic to lib/gh-project-common.sh** if needed:
   - Function for merging Project + Issue data
   - Function for formatting text output
   - Only add if multiple scripts need the same logic (DRY)

4. **Create comprehensive tests**:
   - Start test file with setup/teardown
   - Add gh command mocks to test_helper.bash
   - Write tests for each script following existing patterns

5. **Update documentation**:
   - Add view scripts section to script-usage.md
   - Follow existing doc structure precisely
   - Include complete examples

## What to Avoid (and WHY)

- ❌ **Don't use direct GraphQL mutations** - These are query scripts, read-only, use native `gh` commands
- ❌ **Don't make real API calls in tests** - Tests must be fast and isolated, use mocks
- ❌ **Don't duplicate code across scripts** - Extract common logic to shared functions (DRY)
- ❌ **Don't skip error handling** - Users need clear feedback when things fail
- ❌ **Don't use non-portable paths** - Always use ~/.claude/ prefix, never expand home directory

</implementation>

<output>
Create/modify the following files with relative paths:

**New scripts:**
- `~/.claude/skills/lib/work-items-project/epic-view.sh` - View Epic details
- `~/.claude/skills/lib/work-items-project/story-view.sh` - View Story details
- `~/.claude/skills/lib/work-items-project/task-view.sh` - View Task details
- `~/.claude/skills/lib/work-items-project/spike-view.sh` - View Spike details
- `~/.claude/skills/lib/work-items-project/bug-view.sh` - View Bug details

**New test file:**
- `~/.claude/skills/lib/work-items-project/tests/test_view_scripts.bats` - Comprehensive tests for all view scripts

**Modified files:**
- `~/.claude/skills/lib/work-items-project/tests/test_helper.bash` - Add gh command mocks if needed
- `~/.claude/skills/lib/work-items-project/lib/gh-project-common.sh` - Add shared functions if needed
- `~/.claude/skills/execute-user-story/references/script-usage.md` - Add documentation for view scripts

**Optional (assess during implementation):**
- `~/.claude/skills/execute-user-story/SKILL.md` - Update if view scripts replace gh issue view usage
- `~/.claude/skills/execute-user-story/workflows/execute-user-story.md` - Update examples if needed

</output>

<verification>
Before declaring complete, verify your work:

1. **Script functionality**:
   - Run each script manually with test issue numbers
   - Verify JSON output is valid and complete
   - Verify text output is human-readable
   - Verify error handling works (try invalid issue numbers)

2. **Test coverage**:
   - Run: `cd ~/.claude/skills/lib/work-items-project/tests && bats test_view_scripts.bats`
   - Verify all tests pass
   - Verify no real API calls are made (tests run in < 5 seconds)
   - Verify test coverage includes success and error scenarios

3. **Documentation**:
   - Read updated script-usage.md section
   - Verify examples are clear and complete
   - Verify "When to Use" guidance is included

4. **Consistency**:
   - All 5 scripts follow the same pattern
   - Parameter parsing is consistent
   - Error messages are consistent
   - Output formats match specification

5. **Integration**:
   - Check if execute-user-story skill needs updates
   - Verify portable paths used throughout
   - Verify no home directory expansion

</verification>

<success_criteria>

**Scripts created and working:**
- ✅ All 5 view scripts exist and are executable
- ✅ Scripts accept issue number as positional argument
- ✅ Scripts support --format and --json flags
- ✅ Scripts return valid JSON by default
- ✅ Scripts return human-readable text with --format text
- ✅ Scripts validate issue type and exit with error if wrong type
- ✅ Scripts use portable paths (~/claude/)

**Tests comprehensive and passing:**
- ✅ test_view_scripts.bats created with 30+ tests (6+ per script type)
- ✅ All tests pass without real API calls
- ✅ Tests cover success and error scenarios
- ✅ Tests use mocked gh commands from test_helper.bash
- ✅ Test execution time < 5 seconds

**Documentation complete:**
- ✅ script-usage.md updated with view scripts section
- ✅ Documentation includes parameters, return values, examples
- ✅ "When to Use" guidance included
- ✅ Skills updated or rationale documented for not updating

**Quality standards met:**
- ✅ SOLID principles followed (SRP, DRY)
- ✅ KISS principle applied (simple, clear code)
- ✅ Error handling comprehensive
- ✅ No code duplication across scripts
- ✅ Consistent with existing script patterns

</success_criteria>

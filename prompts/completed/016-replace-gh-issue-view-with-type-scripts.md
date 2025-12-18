<objective>
Replace all references to native `gh issue view` with appropriate type-specific view scripts from the work-items-project suite.

This refactoring improves consistency across skills and documentation by using the newly created view scripts (epic-view.sh, story-view.sh, task-view.sh, spike-view.sh, bug-view.sh) instead of the native GitHub CLI command. The type-specific scripts provide type validation, unified Project + Issue data, and consistent error handling.

This will be used by all Claude Code skills that query work item details.
</objective>

<context>
**Recent work:**
- Just completed: Created 5 type-specific view scripts (prompt 015)
- Scripts location: `~/.claude/skills/lib/work-items-project/`
- Available scripts: epic-view.sh, story-view.sh, task-view.sh, spike-view.sh, bug-view.sh

**Current state:**
- Skills and documentation currently reference `gh issue view ISSUE_NUM` for querying work items
- The execute-user-story skill explicitly notes "native GitHub CLI, read-only approved"
- Recently updated documentation in script-usage.md mentions both approaches

**Files to examine:**
@~/.claude/skills/execute-user-story/SKILL.md
@~/.claude/skills/execute-user-story/workflows/execute-user-story.md
@~/.claude/skills/execute-user-story/references/script-usage.md
@~/.claude/skills/execute-user-story/references/error-handling.md
@~/.claude/skills/execute-user-story/references/state-management.md
@~/.claude/skills/execute-epic/
@~/.claude/skills/execute-next-story/
@~/.claude/skills/epic-to-user-stories/
</context>

<requirements>

## Replacement Strategy

1. **Context-aware replacement**:
   - When context clearly indicates User Story → `~/.claude/skills/lib/work-items-project/story-view.sh`
   - When context clearly indicates Epic → `~/.claude/skills/lib/work-items-project/epic-view.sh`
   - When context clearly indicates Task → `~/.claude/skills/lib/work-items-project/task-view.sh`
   - When context clearly indicates Spike → `~/.claude/skills/lib/work-items-project/spike-view.sh`
   - When context clearly indicates Bug → `~/.claude/skills/lib/work-items-project/bug-view.sh`
   - When type is generic/variable → Keep reference to type-agnostic pattern: `{type}-view.sh`

2. **Pattern matching**:
   - Find: `gh issue view $ISSUE_NUM`
   - Find: `gh issue view "$ISSUE_NUM"`
   - Find: `gh issue view $STORY_NUM`
   - Find: `gh issue view 42` (literal numbers in examples)
   - Find: References in documentation explaining usage

3. **Preserve functionality**:
   - Maintain all command-line flags (--format, --json)
   - Preserve piping and jq usage patterns
   - Keep error handling logic intact
   - Update comments to reflect new approach

## Files to Update

**Priority 1 - execute-user-story skill:**
- `~/.claude/skills/execute-user-story/SKILL.md`
  - Update "Script Library Authority" section
  - Update "Quick Start" examples
- `~/.claude/skills/execute-user-story/workflows/execute-user-story.md`
  - Replace usage in workflow steps
- `~/.claude/skills/execute-user-story/references/script-usage.md`
  - Update examples to use type-specific scripts
  - Maintain "When to Use" guidance with updated recommendations
- `~/.claude/skills/execute-user-story/references/error-handling.md`
  - Update error handling examples
- `~/.claude/skills/execute-user-story/references/state-management.md`
  - Update state verification examples

**Priority 2 - Other skills:**
- Search all skills in `~/.claude/skills/` for `gh issue view` usage
- Update: execute-epic, execute-next-story, execute-next-epic, epic-to-user-stories
- Follow same replacement strategy

**Priority 3 - Project documentation:**
- Check main project for any references in README, docs/, etc.

## Replacement Examples

### Before:
```bash
gh issue view 109 --format json
```

### After (in story context):
```bash
~/.claude/skills/lib/work-items-project/story-view.sh 109 --format json
```

### Before:
```bash
STATUS=$(gh issue view "$STORY_NUM" --format json | jq -r '.status')
```

### After:
```bash
STATUS=$(~/.claude/skills/lib/work-items-project/story-view.sh "$STORY_NUM" --format json | jq -r '.status')
```

### Before (generic context):
```bash
gh issue view $ISSUE_NUM
```

### After (type-agnostic):
```bash
~/.claude/skills/lib/work-items-project/{type}-view.sh $ISSUE_NUM
```

## Constraints

**What to update:**
- ✅ All skill files (SKILL.md, workflows/, references/)
- ✅ Documentation examples showing usage
- ✅ Comments explaining the commands
- ✅ Error handling patterns

**What NOT to change:**
- ❌ Test files that explicitly test native gh CLI behavior
- ❌ Historical documentation about what was used before
- ❌ Comments explaining why we moved away from gh issue view
- ❌ Git commit messages or changelogs

**Why this matters:**
- **Consistency**: All skills use the same approach for querying work items
- **Type safety**: Type-specific scripts validate issue types, preventing errors
- **Maintainability**: Centralized error handling and validation logic
- **Documentation accuracy**: Examples match actual usage patterns

</requirements>

<implementation>

## Step-by-Step Approach

1. **Search and inventory**:
   ```bash
   grep -r "gh issue view" ~/.claude/skills/execute-user-story/
   grep -r "gh issue view" ~/.claude/skills/execute-epic/
   grep -r "gh issue view" ~/.claude/skills/execute-next-story/
   grep -r "gh issue view" ~/.claude/skills/epic-to-user-stories/
   ```

2. **Analyze each occurrence**:
   - Determine work item type from context (story, epic, task, spike, bug)
   - Check if replacement is appropriate (not in historical docs or test files)
   - Note any special flags or piping

3. **Replace systematically**:
   - Start with execute-user-story skill (highest priority)
   - Update SKILL.md first (authoritative script list)
   - Update workflows and references
   - Move to other skills
   - Verify each change preserves functionality

4. **Update documentation narrative**:
   - Revise "When to Use" sections to recommend type-specific scripts
   - Update rationale for using view scripts vs native gh commands
   - Ensure examples are consistent and clear

5. **Verify changes**:
   - Read modified files to ensure context makes sense
   - Check that all portable paths use ~/.claude/ prefix
   - Verify no home directory expansion
   - Ensure error handling examples still work

## Design Principles

**SOLID:**
- Single Responsibility - Each script handles one type
- Open/Closed - Extending via new types, not modifying existing

**KISS:**
- Simple find-and-replace with context awareness
- No complex logic - straightforward updates

**DRY:**
- Extract common patterns where multiple files need same change
- Use consistent replacement patterns

**Portable Paths:**
- Always use ~/.claude/skills/lib/work-items-project/
- Never expand home directory

</implementation>

<output>
Modify the following files:

**execute-user-story skill:**
- `~/.claude/skills/execute-user-story/SKILL.md`
- `~/.claude/skills/execute-user-story/workflows/execute-user-story.md`
- `~/.claude/skills/execute-user-story/references/script-usage.md`
- `~/.claude/skills/execute-user-story/references/error-handling.md`
- `~/.claude/skills/execute-user-story/references/state-management.md`

**Other skills (if they contain gh issue view references):**
- `~/.claude/skills/execute-epic/`
- `~/.claude/skills/execute-next-story/`
- `~/.claude/skills/execute-next-epic/`
- `~/.claude/skills/epic-to-user-stories/`
- `~/.claude/skills/suggest-next-story/`

**Project documentation (if applicable):**
- Main project README or docs/ folder

All changes should use portable paths and maintain consistency with the work-items-project script suite.
</output>

<verification>
Before declaring complete, verify your work:

1. **Search verification**:
   - Run: `grep -r "gh issue view" ~/.claude/skills/execute-user-story/`
   - Verify no remaining inappropriate references (historical/test files excepted)
   - Check that all work item types are covered

2. **Consistency check**:
   - All story contexts use story-view.sh
   - All epic contexts use epic-view.sh
   - All task contexts use task-view.sh
   - Generic contexts use {type}-view.sh pattern

3. **Path verification**:
   - All new references use ~/.claude/skills/lib/work-items-project/
   - No expanded home directories (/Users/...)
   - Portable paths throughout

4. **Functionality preserved**:
   - Flags (--format, --json) still work in examples
   - Piping and jq patterns intact
   - Error handling logic unchanged

5. **Documentation quality**:
   - Examples are clear and executable
   - "When to Use" guidance updated and accurate
   - Rationale for using type-specific scripts is clear

</verification>

<success_criteria>

**Complete replacement:**
- ✅ All appropriate `gh issue view` references replaced with type-specific scripts
- ✅ Story contexts use story-view.sh
- ✅ Epic contexts use epic-view.sh
- ✅ Task/Spike/Bug contexts use appropriate scripts
- ✅ Generic contexts use {type}-view.sh pattern

**Consistency:**
- ✅ All portable paths (~/claude/) used
- ✅ No home directory expansion
- ✅ Consistent replacement pattern across all files

**Documentation quality:**
- ✅ Examples updated and executable
- ✅ "When to Use" guidance reflects new approach
- ✅ Clear rationale for using type-specific scripts
- ✅ Script Library Authority section updated

**Functionality preserved:**
- ✅ All command flags preserved
- ✅ Piping and jq patterns intact
- ✅ Error handling unchanged
- ✅ No broken examples or references

**Skills updated:**
- ✅ execute-user-story skill completely updated
- ✅ Other skills searched and updated if needed
- ✅ All changes follow SOLID, KISS, DRY principles

</success_criteria>

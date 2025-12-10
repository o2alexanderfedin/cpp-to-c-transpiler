<objective>
Update the epic-to-user-stories skill to use our production-ready GitHub Projects scripts instead of custom bash scripts with raw gh CLI commands.

This eliminates duplicate functionality, leverages battle-tested scripts with error handling and atomic operations, and ensures consistency across all GitHub Projects workflows.
</objective>

<context>
Current state:
- epic-to-user-stories skill has custom scripts in ~/.claude/skills/epic-to-user-stories/scripts/
- Uses raw gh CLI commands and manual GraphQL mutations
- Hardcoded to project #13
- No error handling, retry logic, or atomic operations
- Duplicates functionality already in our production scripts
- Race conditions with GitHub API propagation

Desired state:
- Skill uses production scripts from ~/.claude/bin/gh-projects/
- Leverages gh-project-create for atomic issue creation
- Uses gh-project-link for native sub-issue Epic→Story linking
- Works with any project (not hardcoded)
- Benefits from error handling, retry logic, field caching
- Consistent with github-project-setup and other skills

Why this matters:
- Eliminates duplicate code and maintenance burden
- Provides robust error handling and retry logic users expect
- Atomic operations prevent partial state and race conditions
- Field caching improves performance
- Consistency across all GitHub Projects skills
- Single source of truth for GitHub Projects operations
</context>

<requirements>
1. **Replace custom scripts with production scripts**
   - Remove references to custom scripts: process-user-story.sh, add-to-project.sh, link-to-epic.sh, create-user-story.sh
   - Use gh-project-create for User Story creation (atomic draft→convert)
   - Use gh-project-link for Epic→Story linking (native sub-issue API)
   - Use gh-project-update for field updates if needed
   - Remove hardcoded project #13, make it configurable

2. **Update skill workflows**
   - Review and update ~/.claude/skills/epic-to-user-stories/workflows/create-user-stories.md
   - Replace raw gh CLI commands with script calls
   - Update batch creation logic to use production scripts
   - Remove manual field ID lookups (scripts handle this via cache)
   - Update error handling to leverage script retry logic

3. **Update SKILL.md documentation**
   - Update scripts_index to reference production scripts
   - Remove custom script references
   - Update troubleshooting section with new script usage
   - Add notes about global script availability
   - Update success criteria to match production script behavior

4. **Remove obsolete custom scripts**
   - Mark ~/.claude/skills/epic-to-user-stories/scripts/ as deprecated
   - Add README explaining migration to production scripts
   - Keep directory for reference but mark as unused

5. **Update templates and examples**
   - Update user-story-template.md if it references custom scripts
   - Update batch-creation-template.md with new script usage
   - Ensure examples use production script syntax
</requirements>

<implementation>
## Step 1: Read current workflow to understand logic

Read:
- ~/.claude/skills/epic-to-user-stories/workflows/create-user-stories.md

Understand:
- How User Stories are currently created
- Batch creation logic
- Field setting process
- Epic linking process
- Error handling approach

## Step 2: Update create-user-stories.md workflow

Replace patterns:

**OLD: Custom script for User Story creation**
```bash
gh issue create \
  --title "User Story: ..." \
  --body "..." \
  --label "user-story"

./scripts/process-user-story.sh {issue_number} {epic_number} 13
```

**NEW: Production script with atomic operation**
```bash
# Create User Story (atomic draft→convert with fields)
gh-project-create \
  --title "Story: ..." \
  --body "..." \
  --type story \
  --priority {priority} \
  --status Todo

# Link to Epic using native sub-issue API
gh-project-link --parent {epic_number} --child {story_number}
```

**OLD: Manual field setting**
```bash
PROJECT_ID=$(gh project view 13 --owner @me --format json | jq -r '.id')
TYPE_FIELD_ID=$(gh project field-list 13 --owner @me --format json | jq -r '.fields[] | select(.name == "Type") | .id')
gh project item-edit --id "$ITEM_ID" --project-id "$PROJECT_ID" --field-id "$TYPE_FIELD_ID" ...
```

**NEW: Scripts handle field caching automatically**
```bash
# Fields are cached and set automatically by gh-project-create
# No manual field lookups needed
```

**OLD: Batch linking with custom script**
```bash
for issue in 39 40 41 42 43 44; do
  ./scripts/process-user-story.sh $issue 7 13
done
```

**NEW: Batch linking with production script**
```bash
# Link multiple stories to Epic at once
gh-project-link --parent 7 --children 39,40,41,42,43,44
```

## Step 3: Update SKILL.md

### Update scripts_index section:
```markdown
<scripts_index>
## Production Scripts (Global)

Located at `~/.claude/bin/gh-projects/`:

**gh-project-create** - Create User Story with atomic draft→convert workflow
**gh-project-link** - Link User Story to Epic using native sub-issue API
**gh-project-update** - Update User Story fields (status, priority, etc.)
**gh-project-list** - Query User Stories by parent Epic

### Legacy Scripts (Deprecated)
The skill previously used custom scripts in `scripts/`. These are now deprecated in favor of production scripts with better error handling and atomic operations.
</scripts_index>
```

### Update troubleshooting section:
Replace all custom script references with production script equivalents:

**OLD:**
```bash
./scripts/link-to-epic.sh 8 1
```

**NEW:**
```bash
gh-project-link --parent 1 --child 8
```

**OLD:**
```bash
./scripts/process-user-story.sh {issue} {epic} 13
```

**NEW:**
```bash
# Create with Epic reference in body
gh-project-create --title "Story: ..." --type story --body "Part of #{epic}"

# Then link
gh-project-link --parent {epic} --child {story}
```

## Step 4: Mark custom scripts as deprecated

Create ~/.claude/skills/epic-to-user-stories/scripts/README.md:

```markdown
# Deprecated Scripts

These custom scripts are deprecated as of [date] in favor of production scripts located at `~/.claude/bin/gh-projects/`.

## Migration Guide

| Old Script | New Script | Benefits |
|------------|------------|----------|
| process-user-story.sh | gh-project-create + gh-project-link | Atomic operations, error handling |
| add-to-project.sh | (built into gh-project-create) | Field caching, retry logic |
| link-to-epic.sh | gh-project-link | Native sub-issue API |
| create-user-story.sh | gh-project-create | Atomic draft→convert |

## Why Migrated?

- **Error Handling**: Production scripts include comprehensive error handling and retry logic
- **Atomic Operations**: All-or-nothing operations prevent partial state
- **Field Caching**: Automatic field caching improves performance
- **Native API**: Uses GitHub's native sub-issue API for Epic→Story linking
- **Consistency**: All skills use the same production scripts
- **Maintenance**: Single source of truth for GitHub Projects operations

## Production Scripts Documentation

See: `~/.claude/bin/gh-projects/README.md`
```

## Step 5: Update templates with new syntax

If templates reference custom scripts, update them:

**user-story-template.md** - Update any script references
**batch-creation-template.md** - Update batch operations to use production scripts
</implementation>

<script_usage_patterns>
Use these production script patterns in updated workflows:

**Single User Story Creation:**
```bash
# Create User Story with all fields set atomically
gh-project-create \
  --title "Story: Implement feature X" \
  --body "As a user, I want to... [acceptance criteria]. Part of Epic #{epic_number}" \
  --type story \
  --priority high \
  --status Todo

# Output will show: Issue: #{story_number}

# Link to Epic
gh-project-link --parent {epic_number} --child {story_number}
```

**Batch User Story Creation:**
```bash
# Create multiple stories (note: each gets unique issue number)
for title in "Story: Setup" "Story: Implementation" "Story: Testing"; do
  gh-project-create --title "$title" --type story --priority medium
  # Capture output to get issue number for linking
done

# Then batch link (collect all story numbers first)
gh-project-link --parent {epic_number} --children {story1},{story2},{story3}
```

**Query User Stories for Epic:**
```bash
# List all User Stories linked to Epic
gh-project-list --parent {epic_number} --type story
```

**Update User Story Status:**
```bash
# Move story to In Progress
gh-project-update --issue {story_number} --status "In Progress"
```

**Dry-run Mode:**
```bash
# Preview what would be created without executing
gh-project-create --title "Story: Test" --type story --dry-run
gh-project-link --parent 7 --children 39,40 --dry-run
```
</script_usage_patterns>

<output>
Modified files:
1. ~/.claude/skills/epic-to-user-stories/workflows/create-user-stories.md (updated)
2. ~/.claude/skills/epic-to-user-stories/SKILL.md (updated scripts_index and troubleshooting)
3. ~/.claude/skills/epic-to-user-stories/scripts/README.md (created - deprecation notice)
4. ~/.claude/skills/epic-to-user-stories/templates/*.md (updated if they reference custom scripts)

Verification commands to include in output:
```bash
# Verify production scripts accessible
which gh-project-create
which gh-project-link

# Test dry-run mode
gh-project-create --title "Story: Test" --type story --dry-run
gh-project-link --parent 1 --child 2 --dry-run

# Test actual creation (if desired)
gh-project-create --title "Story: Test User Story" --type story --priority low
```
</output>

<verification>
Before declaring complete, verify:

1. **Workflow updated:**
   - [ ] create-user-stories.md uses gh-project-create
   - [ ] create-user-stories.md uses gh-project-link
   - [ ] No references to custom scripts remain in workflow
   - [ ] Batch operations use production scripts
   - [ ] Project number is not hardcoded to 13

2. **SKILL.md updated:**
   - [ ] scripts_index references production scripts
   - [ ] Troubleshooting section uses production script syntax
   - [ ] No references to custom scripts in main docs
   - [ ] Deprecation notice added for custom scripts

3. **Custom scripts deprecated:**
   - [ ] README.md created in scripts/ directory
   - [ ] Migration guide provided
   - [ ] Benefits of production scripts explained

4. **Templates updated:**
   - [ ] No references to custom scripts in templates
   - [ ] Examples use production script syntax

5. **Integration works:**
   - [ ] Production scripts accessible (in PATH or via absolute path)
   - [ ] Dry-run commands execute successfully
   - [ ] Script syntax is correct in all updated files
</verification>

<success_criteria>
- All workflow files updated to use production scripts
- SKILL.md documentation reflects production script usage
- Custom scripts marked as deprecated with migration guide
- Templates updated with production script syntax
- No hardcoded project numbers (configurable)
- Dry-run mode works for testing
- Skill maintains all original functionality with better robustness
- Integration with production scripts verified
</success_criteria>

<constraints>
- Do NOT delete custom scripts (mark as deprecated)
- Preserve skill functionality (same user experience)
- Maintain backward compatibility where possible
- Use absolute paths if scripts not in PATH: ~/.claude/bin/gh-projects/gh-project-*
- Keep all original templates and references
- Document why migration happened (benefits)
- Ensure skill can find production scripts
</constraints>

<benefits>
After this update, the epic-to-user-stories skill will have:

1. **Atomic Operations** - All-or-nothing issue creation prevents partial state
2. **Error Handling** - Comprehensive error messages and recovery suggestions
3. **Retry Logic** - Automatic retry with exponential backoff for transient failures
4. **Field Caching** - Performance improvement via cached field IDs
5. **Native Sub-Issue API** - Proper Epic→Story relationships in GitHub UI
6. **No Hardcoding** - Works with any project, not just #13
7. **Consistency** - Same scripts as github-project-setup and other skills
8. **Better Testing** - Dry-run mode for safe testing before execution
9. **Race Condition Prevention** - Atomic operations eliminate API propagation issues
10. **Single Source of Truth** - All GitHub Projects operations in one place
</benefits>

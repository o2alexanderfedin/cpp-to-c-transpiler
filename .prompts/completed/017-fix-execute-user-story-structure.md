<objective>
Fix structural issues in the execute-user-story skill identified by the skill-auditor.

The audit revealed that workflows/execute-user-story.md violates progressive disclosure principles by duplicating content already in SKILL.md. This is a single-workflow skill, not a multi-workflow router, so the separate workflow file should be deleted and the skill should be restructured to follow best practices.

This cleanup will improve maintainability, eliminate duplication, and ensure compliance with Agent Skills best practices.
</objective>

<context>
**Audit findings:**
- workflows/execute-user-story.md (1,079 lines) duplicates content already in SKILL.md
- This is a single-workflow skill, not a multi-workflow router
- The router pattern (SKILL.md → workflows/) is for skills with MULTIPLE workflows
- SKILL.md has unnecessary `<skill>` wrapper tags
- SKILL.md has non-standard `version: 3.0.0` in frontmatter
- References use markdown headings instead of pure XML (lower priority)

**Skill location:**
`/Users/alexanderfedin/.claude/skills/execute-user-story/`

**Current structure:**
```
execute-user-story/
├── SKILL.md (383 lines)
├── workflows/
│   └── execute-user-story.md (1,079 lines - TO DELETE)
├── references/ (6 files - keep these, they provide domain knowledge)
```

**Target structure:**
```
execute-user-story/
├── SKILL.md (streamlined, no routing to workflow)
├── references/ (unchanged)
```
</context>

<requirements>

## Critical Fixes (Priority 1)

1. **Delete workflows/execute-user-story.md**
   - This file violates progressive disclosure
   - Content is duplicated in SKILL.md and references
   - Single-workflow skills don't need separate workflow files

2. **Update SKILL.md routing section**
   - Current: Lines 289-306 route to workflows/execute-user-story.md
   - Change to: Remove routing section entirely
   - Why: No workflow file to route to; content is already in SKILL.md

3. **Remove `<skill>` wrapper tags**
   - Current: Lines 24 and 383 have `<skill>` and `</skill>`
   - Change to: Remove these wrapper tags
   - Why: Per best practices, skills use direct XML tags, no wrapper

4. **Fix frontmatter**
   - Current: Line 3 has `version: 3.0.0`
   - Change to: Remove version field
   - Why: Not a standard skill metadata field

## Verification Steps

5. **Ensure no content loss**
   - Read workflows/execute-user-story.md before deletion
   - Verify all unique content is already in SKILL.md or references
   - If any content is unique, integrate it into SKILL.md first

6. **Update any cross-references**
   - Search for references to workflows/execute-user-story.md
   - Update or remove these references

## Optional Improvements (Priority 2 - only if time permits)

7. **Simplify SKILL.md structure**
   - Since there's no routing, content can flow directly
   - Remove unnecessary indirection
   - Keep essential sections: objective, principles, intake, success criteria

</requirements>

<implementation>

## Step-by-Step Approach

1. **Read and analyze workflow file**:
   ```bash
   wc -l ~/.claude/skills/execute-user-story/workflows/execute-user-story.md
   head -50 ~/.claude/skills/execute-user-story/workflows/execute-user-story.md
   ```

2. **Verify content coverage**:
   - Compare workflow content with SKILL.md sections
   - Check references/ for domain knowledge coverage
   - Identify any unique content (should be minimal/none)

3. **Delete workflow file**:
   ```bash
   rm ~/.claude/skills/execute-user-story/workflows/execute-user-story.md
   rmdir ~/.claude/skills/execute-user-story/workflows  # if empty
   ```

4. **Update SKILL.md**:
   - Remove `version: 3.0.0` from frontmatter
   - Remove `<skill>` and `</skill>` wrapper tags
   - Remove or update routing section (lines 289-306)
   - Ensure content flows logically without workflow indirection

5. **Search for cross-references**:
   ```bash
   grep -r "workflows/execute-user-story" ~/.claude/skills/execute-user-story/
   grep -r "execute-user-story.md" ~/.claude/skills/execute-user-story/
   ```

6. **Verify structure**:
   - Read updated SKILL.md
   - Ensure no broken references
   - Verify skill still functions correctly

7. **Commit changes** (in skills repository):
   ```bash
   cd ~/.claude/skills
   git checkout -b feature/fix-execute-user-story-structure
   git add execute-user-story/
   git commit -m "refactor(execute-user-story): remove redundant workflow file and clean up structure"
   git flow feature finish fix-execute-user-story-structure
   git push origin develop
   ```

## What NOT to Change

- ❌ Don't modify reference files (they provide domain knowledge - this is correct)
- ❌ Don't change the skill's functionality or behavior
- ❌ Don't remove essential content from SKILL.md
- ❌ Don't modify other skills

## Why This Matters

- **Progressive disclosure**: SKILL.md should contain routing OR complete content, not both
- **Single responsibility**: One workflow = one file (SKILL.md), not two (SKILL.md + workflows/)
- **Maintainability**: Eliminating duplication makes updates easier
- **Best practices compliance**: Follows documented Agent Skills patterns

</implementation>

<output>
Modify/delete the following files in `~/.claude/skills/execute-user-story/`:

**Delete:**
- `workflows/execute-user-story.md` (entire file)
- `workflows/` (directory, if empty after deletion)

**Modify:**
- `SKILL.md`:
  - Remove `version: 3.0.0` from frontmatter
  - Remove `<skill>` wrapper tag (line 24)
  - Remove `</skill>` closing tag (line 383)
  - Remove or simplify routing section (lines 289-306)

**Keep unchanged:**
- All files in `references/` directory

**Commit in skills repository:**
- Use git flow feature branch
- Commit message: "refactor(execute-user-story): remove redundant workflow file and clean up structure"
- Push to develop branch
</output>

<verification>
Before declaring complete, verify:

1. **File deletion**:
   - `workflows/execute-user-story.md` no longer exists
   - `workflows/` directory removed if empty

2. **SKILL.md structure**:
   - No `version` field in frontmatter
   - No `<skill>` wrapper tags
   - Routing section removed or updated
   - Content flows logically without workflow indirection

3. **No broken references**:
   - Search for "workflows/execute-user-story" returns no results
   - All references in SKILL.md are valid

4. **Git commit**:
   - Changes committed in skills repository
   - Pushed to develop branch
   - Feature branch finished

5. **Functionality preserved**:
   - Skill still contains all essential content
   - References still accessible via progressive disclosure
   - Success criteria unchanged

</verification>

<success_criteria>

**Structure fixed:**
- ✅ workflows/execute-user-story.md deleted
- ✅ workflows/ directory removed (if empty)
- ✅ SKILL.md frontmatter cleaned (no version field)
- ✅ SKILL.md wrapper tags removed (<skill>)
- ✅ Routing section updated or removed

**Best practices compliance:**
- ✅ Progressive disclosure: SKILL.md contains complete process
- ✅ Single-workflow pattern: No separate workflow file
- ✅ Pure XML structure: No unnecessary wrapper tags
- ✅ Standard frontmatter: Only required fields

**Functionality preserved:**
- ✅ All essential content retained
- ✅ References still accessible
- ✅ Success criteria unchanged
- ✅ No broken references

**Git hygiene:**
- ✅ Changes committed in skills repository
- ✅ Conventional commit message
- ✅ Pushed to develop branch
- ✅ Feature branch finished

</success_criteria>

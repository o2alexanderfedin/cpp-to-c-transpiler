# GitHub Projects Scripts Redesign - Implementation Plan Summary

**5-phase roadmap for SOLID/KISS/DRY-compliant CRUD scripts with minimal options**

v1 • 2025-12-15
Based on: `.prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md`

---

## Executive Summary

Complete redesign of GitHub Projects scripts following software engineering principles. Replaces 16 complex multi-mode scripts with 32 simple single-purpose scripts.

**Key improvement:** Each script does ONE thing with MINIMAL options (hard to misuse).

---

## Key Decisions

### Script Organization
**Decision:** Flat structure with `gh-{resource}-{operation}.sh` pattern

- ✅ One script per operation per resource
- ✅ No subcommands (too complex)
- ✅ Self-documenting filenames
- ✅ Tab-completion friendly

**Example:** `gh-epic-create.sh`, `gh-story-list.sh`, `gh-task-update.sh`

### Naming Pattern
```
gh-{resource}-{operation}.sh

Resources: project, epic, story, task, spike, bug
Operations: create, list, view, update, delete, init
```

### Configuration
**Multi-tier with precedence:**
1. CLI flags (--project, --owner)
2. Environment variables (GH_PROJECT_NUMBER)
3. Config file (~/.config/gh-projects/config.json)
4. Auto-detection (git remote, gh auth)

**One-time init:** `gh-project-init.sh --project 1` (auto-detects owner/repo)

### Item Type Handling
**Decision:** Separate scripts per type (epic/story/task/spike/bug)

- Type implicit in script name (no --type flag)
- Parent relationships explicit (--epic, --story)
- Type-specific validations enforced

**Example:**
- Old: `gh-project-item-create.sh --title "Epic" --type Epic`
- New: `gh-epic-create.sh "Epic"` (type implicit)

### Migration Strategy
**Archive old scripts, update skills, provide mapping**

- Move old scripts → `~/.claude/skills/lib/gh-projects-legacy/`
- Update affected skills to use new scripts
- Provide migration guide with old→new mappings
- No backward compatibility layer (clean break)

---

## Script Inventory

### Phase 1 - Foundation (4-6 hours)
**Common library + configuration**

- `lib/gh-project-common.sh` - 450 lines (enhanced existing library)
- `gh-project-init.sh` - Configuration initialization

**New common library functions:**
- `create_repo_issue()` - Create issue, return URL
- `add_issue_to_project()` - Add to project, return item_id
- `set_item_field()` - Update field by name
- `get_item_by_issue()` - Find item from issue number
- `list_items_by_type()` - Filter by Type field
- `gh()` wrapper - Fixes PATH issues

### Phase 2 - Project CRUD (2-3 hours)
**5 project management scripts**

- `gh-project-create.sh` - Create project
- `gh-project-list.sh` - List projects
- `gh-project-view.sh` - View project details
- `gh-project-delete.sh` - Delete project

### Phase 3 - Epic & Story CRUD (6-8 hours)
**10 core item type scripts**

**Epic (5 scripts):**
- `gh-epic-create.sh` - Create epic (Type=Epic)
- `gh-epic-list.sh` - List epics
- `gh-epic-view.sh` - View epic with sub-issues
- `gh-epic-update.sh` - Update fields
- `gh-epic-delete.sh` - Delete epic

**Story (5 scripts):**
- `gh-story-create.sh` - Create story (requires --epic)
- `gh-story-list.sh` - List stories
- `gh-story-view.sh` - View story with parent
- `gh-story-update.sh` - Update fields
- `gh-story-delete.sh` - Delete story

### Phase 4 - Task/Spike/Bug CRUD (4-5 hours)
**15 additional item type scripts**

Following same pattern as Epic/Story:
- **Task:** 5 scripts (create requires --story)
- **Spike:** 5 scripts (optional --epic)
- **Bug:** 5 scripts (optional --epic or --story)

### Phase 5 - Migration & Testing (3-4 hours)
**Archive, update, verify**

- Archive old scripts to legacy directory
- Create `MIGRATION-GUIDE.md` with old→new mappings
- Update affected skills (execute-epic, execute-user-story, etc.)
- Run integration test suite
- Verify no regressions

---

## Total Deliverables

**32 scripts across 5 phases:**
- 1 common library (450 lines)
- 1 init script (80 lines)
- 4 project operations (60 lines each)
- 25 item operations (85 lines average each)

**Total LOC:** ~2,900 lines (similar to old, but much simpler per script)

**Estimated effort:** 19-26 hours total

---

## Implementation Phases

### Phase 1: Foundation ⚙️
**Goal:** Common library + configuration
**Effort:** 4-6 hours
**Complexity:** Medium

**Deliverables:**
- Enhanced `lib/gh-project-common.sh` with high-level functions
- `gh-project-init.sh` with auto-detection
- README.md with usage documentation

**Acceptance criteria:**
- Common library sources without errors
- Config loads with env var override
- Field name normalization works (lowercase)
- gh() wrapper finds CLI in restricted environments
- All high-level functions tested

---

### Phase 2: Project CRUD 📋
**Goal:** Basic project management
**Effort:** 2-3 hours
**Complexity:** Simple

**Deliverables:**
- 4 project scripts (create, list, view, delete)

**Acceptance criteria:**
- All project operations work
- Help text comprehensive
- Error messages actionable
- --format json outputs valid JSON

---

### Phase 3: Epic & Story CRUD 📦
**Goal:** Core item types
**Effort:** 6-8 hours
**Complexity:** Medium

**Deliverables:**
- 5 epic scripts
- 5 story scripts

**Acceptance criteria:**
- Epic ← Story relationship works
- Type fields set correctly
- Parent-child links created
- All CRUD operations tested

---

### Phase 4: Task/Spike/Bug CRUD 🔧
**Goal:** Remaining item types
**Effort:** 4-5 hours
**Complexity:** Simple (pattern reuse)

**Deliverables:**
- 5 task scripts (requires --story)
- 5 spike scripts (optional --epic)
- 5 bug scripts (optional parent)

**Acceptance criteria:**
- All item types follow same pattern
- Labels added automatically (bug, spike)
- All relationships work
- Consistent help/errors across types

---

### Phase 5: Migration & Testing 🔄
**Goal:** Replace old scripts
**Effort:** 3-4 hours
**Complexity:** Medium

**Deliverables:**
- Archived old scripts
- Migration guide
- Updated skills
- Integration test suite

**Acceptance criteria:**
- All old scripts in legacy directory
- All affected skills updated and tested
- No regressions from old implementation
- Common workflows verified

---

## Breaking Changes

### 1. Type-specific scripts required
- **Old:** `gh-project-update.sh --issue 42 --status Done`
- **New:** `gh-epic-update.sh 42 --status Done` (must know type)

### 2. Parent relationships explicit
- **Old:** `--parent 42` (ambiguous)
- **New:** `--epic 42` or `--story 42` (clear)

### 3. No generic item operations
- **Old:** `gh-project-item-create.sh --type Epic`
- **New:** `gh-epic-create.sh` (type implicit)

### 4. Setup scripts consolidated
- **Old:** 3 setup scripts (init/apply/clone)
- **New:** 1 init script (clone removed per YAGNI)

### 5. Positional arguments
- **Old:** `--title "Epic Title"` (named flag)
- **New:** `"Epic Title"` (positional arg)

---

## Skills to Update

**Affected skills:**
- `execute-epic.skill.md` - Uses gh-project-item-create
- `execute-user-story.skill.md` - Uses gh-project-item-create
- `epic-to-user-stories.skill.md` - Uses gh-project-item-create
- `prd-to-epics.skill.md` - Uses gh-project-item-create

**Update pattern:**
```diff
- gh-project-item-create.sh --title "$TITLE" --type Epic --status Todo
+ gh-epic-create.sh "$TITLE" --status Todo
```

```diff
- gh-project-item-create.sh --title "$TITLE" --type "User Story" --parent $EPIC
+ gh-story-create.sh "$TITLE" --epic $EPIC
```

---

## Principles Applied

### SOLID
- **Single Responsibility:** One script = one operation
- **Open/Closed:** Config file extensibility, no hardcoded values
- **Liskov Substitution:** Consistent interfaces across similar scripts
- **Interface Segregation:** Minimal required options
- **Dependency Inversion:** Common library abstractions

### KISS
- One script per operation (not multi-mode)
- Minimal options (hard to misuse)
- Sensible defaults
- Help text under 30 lines

### DRY
- Common library for shared code
- High-level operations abstracted
- Intentional duplication for clarity (help text, arg parsing)

### YAGNI
- No multi-project support (v1)
- No bulk operations
- No Projects V1 compatibility
- No pagination (assumes <30 items)

### TRIZ
- Auto-detection over configuration
- Graceful degradation
- Self-documenting
- Intuitive defaults
- Predictable behavior

---

## Quality Standards

### Help Text
- Usage line with positional args
- Options with defaults documented
- At least 2 examples (simple + advanced)
- Under 30 lines total
- Realistic example values

### Error Messages
**3-part format:**
1. What went wrong (specific)
2. Why it went wrong (context)
3. How to fix it (actionable)

### Exit Codes
- 0: Success
- 1: General error
- 2: Cancelled (dry-run, confirmation)
- 3: Configuration error
- 4: API error

### Validation
- Fail fast, fail clearly
- Validate before API calls
- Helpful error messages
- Suggest fixes

---

## Examples

### Create Epic with Stories

**Old way:**
```bash
gh-project-item-create.sh \
  --title "Auth System" \
  --type Epic \
  --status Todo \
  --priority High

gh-project-item-create.sh \
  --title "OAuth Login" \
  --type "User Story" \
  --parent 1
```

**New way:**
```bash
gh-epic-create.sh "Auth System" \
  --priority High

gh-story-create.sh "OAuth Login" \
  --epic 1
```

**Benefits:**
- Fewer options (simpler)
- Type implicit
- Parent relationship clear

---

## Next Steps

### Option A: Automated Sequential
- Implement all 5 phases automatically
- Total time: 19-26 hours
- Fully automated verification

### Option B: Manual Phase-by-Phase ⭐ (Recommended)
- Implement Phase 1, test
- Implement Phase 2, test
- Continue through Phase 5
- More control, can adjust

### Option C: Parallel Implementation
- Phase 1 first (foundation)
- Phase 4 scripts in parallel
- Phase 5 last (migration)
- Faster with multiple developers

---

## Decision Points

**Approve these decisions to proceed:**

1. ✅ Script organization: Flat `gh-{resource}-{operation}.sh`
2. ✅ Type-specific scripts (no generic --type flag)
3. ✅ Configuration: Config file + env var override
4. ✅ Migration: Archive old, no wrapper compatibility
5. ✅ YAGNI deferrals: No multi-project, bulk ops, V1 support

---

## Blockers

**None** - Ready to implement once plan approved.

All dependencies identified, all decisions made, all specifications complete.

---

## Success Criteria

- [ ] All 32 scripts implemented
- [ ] All help text comprehensive
- [ ] All error messages actionable
- [ ] All skills updated and tested
- [ ] Old scripts archived
- [ ] Migration guide complete
- [ ] Integration tests pass
- [ ] No regressions

---

**For execution:**

Review plan, approve decisions, then:
- **Manual:** Implement phase-by-phase following plan
- **Automated:** Use plan as specification for automated implementation

---

**Plan location:** `.prompts/019-gh-scripts-redesign-plan/gh-scripts-redesign-plan.md`
**Full specification:** 500+ lines of detailed implementation guidance

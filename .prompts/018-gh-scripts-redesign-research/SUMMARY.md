# GitHub Projects Scripts Redesign - Research Summary

**SOLID/KISS/DRY/YAGNI-compliant CLI scripts with crystal-clear interfaces**

v1 • 2025-12-15

---

## One-Line Summary

Resource-specific CRUD scripts (gh-epic-create, gh-story-update, etc.) with minimal options, comprehensive help, and shared library for DRY compliance.

---

## Key Findings

### CLI Design Principles (SOLID/KISS/DRY/YAGNI/TRIZ)

✅ **Single Responsibility** - One script = one action on one resource
- `gh-epic-create` creates epics (only)
- `gh-story-update` updates story fields (only)
- Eliminates Swiss Army Knife anti-pattern

✅ **KISS: Simplicity Rules**
- Target: <10 options per script
- Target: <30 lines of help text (one screen)
- No conditional logic based on option combinations
- Separate scripts for separate item types (no --type flag)

✅ **DRY: Common Library**
- Enhanced `gh-project-common.sh` with high-level abstractions
- Shared: config, field caching, error handling, logging, API execution
- Not shared: help text, argument parsing, script-specific logic

✅ **YAGNI: What to Defer**
- Multi-project support (use env vars if needed)
- Bulk operations (CSV imports)
- Undo/rollback (too complex for v1)
- Projects V1 compatibility (deprecated by GitHub)
- Custom field types beyond single-select

✅ **TRIZ: Approaching Ideal**
- Auto-detect config from git remote and gh auth
- Fail fast with actionable error messages
- Defaults match obvious starting states (Status=Todo)
- Graceful degradation (retry with exponential backoff)

### GitHub Projects API Capabilities

**Project Operations:**
- `gh project create/list/view/edit/close/delete` - Project lifecycle
- `gh project field-list/field-create/field-delete` - Custom fields
- `gh project link/unlink` - Repository associations

**Item Operations:**
- `gh project item-create` - Creates DRAFT ISSUE (project-only, no repo issue)
- `gh project item-add` - Adds EXISTING repo issue to project
- `gh project item-list/edit/delete/archive` - Item management

**Critical Finding: Field Names**
- UI displays: "Type", "Status", "Priority" (PascalCase)
- JSON requires: "type", "status", "priority" (lowercase)
- Case-sensitive lookups caused bugs in previous implementation

**Standard Field Structure:**
```json
{
  "fields": [{
    "id": "PVTF_lADOA...",
    "name": "Status",
    "type": "SINGLE_SELECT",
    "options": [
      {"id": "opt_123", "name": "Todo"},
      {"id": "opt_456", "name": "In Progress"}
    ]
  }]
}
```

### Project Items vs Repository Issues (CRITICAL DISTINCTION)

**Two separate entities:**

1. **Repository Issues** - Traditional GitHub issues
   - Have issue numbers (#1, #2, #3)
   - Visible at github.com/owner/repo/issues/123
   - Can have labels, assignees, comments
   - NO custom fields (Type, Status, Priority)
   - Managed via: `gh issue create/edit/list/close/delete`

2. **Project Items** - Items in Projects V2
   - Have project item IDs (not issue numbers)
   - Can be draft issues (project-only) OR linked to repo issues
   - ONLY project items have custom fields
   - Managed via: `gh project item-create/add/edit/list/delete`

**Recommended workflow (Method 2):**
```bash
# Step 1: Create repository issue
ISSUE_URL=$(gh issue create --repo owner/repo --title "Real issue")

# Step 2: Add to project
ITEM_ID=$(gh project item-add 1 --owner "@me" --url "$ISSUE_URL")

# Step 3: Set custom fields
gh project item-edit --id "$ITEM_ID" --project-id "$PROJECT_ID" \
  --field-id "$TYPE_FIELD_ID" --single-select-option-id "$EPIC_OPTION_ID"
```

**Why repository issues over draft issues:**
- Full GitHub functionality (comments, labels, assignees)
- Can be referenced in commits: "fixes #123"
- Team notifications work
- Proper audit trail
- Recommended for ALL real work (Epics, Stories, Tasks, Bugs, Spikes)

### Proposed Script Architecture

**Directory structure:**
```
~/.claude/skills/lib/gh-projects/
├── lib/
│   └── gh-project-common.sh        # Enhanced shared library
├── old-implementation/              # Archive current scripts
│
# Resource-specific CRUD (20-25 scripts total)
├── gh-project-{create,list,view,delete}.sh
├── gh-epic-{create,list,update,delete}.sh
├── gh-story-{create,list,update,delete,link}.sh
├── gh-task-{create,list,update,delete,link}.sh
├── gh-bug-{create,list,update,delete}.sh
├── gh-spike-{create,list,update,delete}.sh
└── gh-project-init.sh
```

**Naming convention:** `gh-{resource}-{action}.sh`
- Resources: project, epic, story, task, bug, spike
- Actions: create, list, view, update, delete, link

**Common library enhancements needed:**
- `create_project_item(type, title, body)` - Unified repo issue + project creation
- `list_items_by_type(type, limit)` - Type-filtered listing
- `update_item_field_by_issue(issue_num, field, value)` - Field updates by issue #
- `auto_detect_config()` - Detect from git remote and gh auth

### Help Text and Error Handling

**Help text format (from exemplars: git, docker, gh, jq):**
```
Usage: script-name [OPTIONS] ARGUMENTS

One-sentence description

Options:
  --required VALUE   Description (required)
  --optional VALUE   Description (default: value)
  -h, --help         Show help

Examples:
  # Use case 1
  script-name example-1

  # Use case 2
  script-name example-2

Requirements/Notes (if needed)
```

**Error message template:**
```
Error: [What went wrong]

Possible reasons:
- [Reason 1]
- [Reason 2]

Fix: [Specific command to run]
```

**Exit codes (GitHub CLI standard):**
- 0 = Success
- 1 = General error
- 2 = Cancelled
- 4 = Authentication required

### Exemplar Tool Analysis

**Git:** Consistent patterns, grouped commands, comprehensive help
- Adopt: `gh-{resource}-{action}` naming pattern
- Avoid: Too many commands (keep to 20-30)

**Docker:** Clear visual hierarchy, Common vs Management commands
- Adopt: Separate item types clearly in documentation
- Avoid: Duplicate commands (docker ps vs docker container ls)

**GitHub CLI (gh):** JSON output, examples, inherited flags
- Adopt: `--format json` for all scripts, example sections
- Avoid: Complex JSON queries (--jq, --template are YAGNI)

**jq:** Example in help text, clear input/output
- Adopt: Include quick example in help

**kubectl:** Resource-oriented CRUD
- Adopt: Similar pattern to our {resource}-{action}

### Lessons from Existing Implementation

**What worked well (keep):**
- Common library approach (388 lines, well-organized)
- Field caching (solves rate limit issues)
- Retry logic (3 attempts, exponential backoff)
- Colored logging (stderr, doesn't pollute stdout)
- Dry-run support (preview before executing)
- Atomic operations (all-or-nothing)
- Sub-issue integration (GitHub's native API)

**What failed (fix in redesign):**
- Too many options per script (10+ options)
- Generic naming (gh-project-update - update what?)
- Dual-mode scripts (different behavior based on flags)
- Setup script proliferation (init/apply/clone - confusing)
- Implicit script dependencies (scripts calling other scripts)

**Confusion points (address):**
- Project items vs repository issues terminology
- When to use item-create vs item-add
- Field name case sensitivity
- Issue number vs item ID
- Partial creation failures

---

## Quality Report

### Verified Claims

✅ **GitHub CLI capabilities** - Tested all `gh project` and `gh issue` subcommands
✅ **Field case sensitivity** - Confirmed from previous bug fix (prompt 015)
✅ **Exit code conventions** - Verified with `gh help exit-codes`
✅ **Existing scripts** - Analyzed 16 scripts in ~/.claude/skills/lib/gh-projects/
✅ **Exemplar tools** - Studied git, docker, gh, jq help formats
✅ **CLI best practices** - Researched Google Shell Style Guide, clig.dev, 12-factor CLI

### Sources Consulted

- [Google Shell Style Guide](https://google.github.io/styleguide/shellguide.html)
- [Command Line Interface Guidelines](https://clig.dev/)
- [12 Factor CLI Apps](https://medium.com/@jdxcode/12-factor-cli-apps-dd3c227a0e46)
- [CLI Guidelines GitHub](https://github.com/cli-guidelines/cli-guidelines)
- GitHub CLI: `gh project --help`, `gh issue --help`, `gh help exit-codes`
- Existing implementation: ~/.claude/skills/lib/gh-projects/

### Assumptions to Validate in Planning

⚠️ **Needs verification:**
- Story Points field exists in target projects (may not be universal)
- Users prefer repository issues over draft issues (99% use case assumed)
- Field options rarely change after setup (cache assumption)
- Single project per repository (multi-project is YAGNI)

---

## Decisions Needed for Planning Phase

1. **Draft issue support:** Include in v1 or defer?
   - Recommendation: Defer (YAGNI), focus on repository issues

2. **Script naming:** `gh-epic-create.sh` or just `gh-epic-create`?
   - Recommendation: No .sh extension for executables (Google style guide)

3. **Rollback on failure:** Delete issue if project add fails?
   - Recommendation: No rollback in v1 (too complex), clear error message

4. **Pagination:** Support >30 items?
   - Recommendation: Not in v1, document limitation

5. **Multi-project:** Environment variable override or config switching?
   - Recommendation: Env var override only (GH_PROJECT_NUMBER)

6. **Field validation:** Strict (fail if field missing) or lenient (warn and continue)?
   - Recommendation: Strict for v1 (prevents partial state)

7. **Backward compatibility:** Support old script names with deprecation warnings?
   - Recommendation: Yes, 30-day deprecation period

---

## Blockers

None identified.

All required information gathered for planning phase.

---

## Next Steps

### Immediate: Create Planning Prompt

File: `.prompts/019-gh-scripts-redesign-plan/`

**Planning prompt should:**
1. Reference this research: `@.prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md`
2. Create complete script inventory (exact list of scripts to create)
3. Define directory structure and file naming
4. Specify common library interface (function signatures)
5. Design migration strategy from old scripts
6. Create implementation phases (prioritize core CRUD operations)
7. Define acceptance criteria for each script
8. Document testing approach

### Implementation Phases (suggested)

**Phase 1: Foundation**
- Enhance common library with high-level abstractions
- Create gh-project-init with auto-detection
- Test configuration management

**Phase 2: Core CRUD**
- Epic: create, list, update, delete
- Story: create, list, update, delete, link
- Task: create, list, update, delete, link

**Phase 3: Additional Types**
- Bug: create, list, update, delete
- Spike: create, list, update, delete

**Phase 4: Migration**
- Move old scripts to old-implementation/
- Add deprecation warnings
- Update documentation

**Phase 5: Polish**
- Comprehensive testing
- Documentation improvements
- Performance optimization

---

## Success Metrics

- [ ] 20-25 scripts total (down from conceptually unlimited combinations)
- [ ] <10 options per script (down from 10+ in current)
- [ ] <30 lines help text per script (one screen)
- [ ] 100% scripts have comprehensive help and examples
- [ ] Zero ambiguity about project items vs repository issues
- [ ] Common library provides all DRY abstractions
- [ ] All scripts support `--format json` for composability
- [ ] Exit codes follow GitHub CLI standard (0/1/2/4)
- [ ] Configuration auto-detects when possible
- [ ] Error messages include fix suggestions

---

## Confidence Level

**Medium-High**

- Strong foundation from official documentation
- Clear understanding of GitHub API capabilities
- Well-analyzed exemplar tools
- Thorough review of existing implementation
- Some assumptions need validation in practice
- Planning phase will validate decisions

---

**Ready for planning phase.**

This research provides comprehensive foundation for designing simple, principled CLI scripts that follow SOLID/KISS/DRY/YAGNI/TRIZ principles.

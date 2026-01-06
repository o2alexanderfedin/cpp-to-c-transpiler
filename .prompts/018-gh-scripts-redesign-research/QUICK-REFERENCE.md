# GitHub Projects Scripts Redesign - Quick Reference

**One-page reference for planning phase**

---

## Design Principles (SOLID/KISS/DRY/YAGNI/TRIZ)

| Principle | Application to Scripts |
|-----------|------------------------|
| **Single Responsibility** | One script = one action on one resource |
| **Open/Closed** | Config files for extensibility, env vars for overrides |
| **Liskov Substitution** | Consistent flags across similar scripts (--title, --body, --assignee) |
| **Interface Segregation** | <10 options per script, no --type flag (use separate scripts) |
| **Dependency Inversion** | Scripts depend on common library abstractions, not gh CLI directly |
| **KISS** | <30 lines help text, no option combinations, no conditional logic |
| **DRY** | Common library for config, caching, errors, API; duplicate help/args |
| **YAGNI** | Defer: multi-project, bulk ops, undo, V1 compat, pagination |
| **TRIZ** | Auto-detect config, fail fast with fixes, obvious defaults |

---

## Architecture: 20-25 Scripts

### Naming Pattern: `gh-{resource}-{action}`

**Resources:** project, epic, story, task, bug, spike
**Actions:** create, list, view, update, delete, link

### Script Inventory

```
# Project (4 scripts)
gh-project-create, gh-project-list, gh-project-view, gh-project-delete

# Epic (4 scripts)
gh-epic-create, gh-epic-list, gh-epic-update, gh-epic-delete

# Story (5 scripts)
gh-story-create, gh-story-list, gh-story-update, gh-story-delete, gh-story-link

# Task (5 scripts)
gh-task-create, gh-task-list, gh-task-update, gh-task-delete, gh-task-link

# Bug (4 scripts)
gh-bug-create, gh-bug-list, gh-bug-update, gh-bug-delete

# Spike (4 scripts)
gh-spike-create, gh-spike-list, gh-spike-update, gh-spike-delete

# Config (1 script)
gh-project-init

Total: 27 scripts
```

---

## Common Library Enhancements

### Current (keep): `lib/gh-project-common.sh`
- ✅ Configuration (load_config, save_config)
- ✅ Field caching (cache_fields, get_field_id, get_option_id)
- ✅ Error handling (die, retry_command)
- ✅ Logging (log_success, log_error, log_warn, log_info)
- ✅ GraphQL (execute_graphql, execute_sub_issue_mutation)
- ✅ ID retrieval (get_project_id, get_issue_id)
- ✅ Sub-issues (add_sub_issue, remove_sub_issue, query_sub_issues)
- ✅ Validation (validate_prerequisites)
- ✅ Field updates (set_single_select_field)

### Add (high-level abstractions):
- `create_project_item(type, title, body, labels, assignee)` → issue_num, item_id
- `list_items_by_type(type, limit)` → filtered JSON
- `update_item_field_by_issue(issue_num, field, value)` → success/fail
- `auto_detect_config()` → prompt and save
- `find_item_by_issue(issue_num)` → item_id

---

## GitHub API Quick Reference

### Project Items vs Repository Issues

| Aspect | Repository Issue | Project Item |
|--------|------------------|--------------|
| **Command** | `gh issue` | `gh project item-` |
| **ID** | Issue number (#123) | Item ID (PVTI_...) |
| **Location** | github.com/owner/repo/issues/123 | Project only |
| **Custom fields** | NO | YES (Type, Status, Priority) |
| **Comments** | YES | NO (unless linked to repo issue) |
| **Labels** | YES | NO (repo issue has labels) |
| **References** | Can reference in commits | Cannot reference directly |

### Recommended Workflow (Always Use Repo Issues)

```bash
# 1. Create repo issue
ISSUE_URL=$(gh issue create --repo owner/repo --title "Title" --body "Body")

# 2. Add to project
ITEM_ID=$(gh project item-add 1 --owner "@me" --url "$ISSUE_URL" --format json | jq -r '.id')

# 3. Set custom fields
gh project item-edit --id "$ITEM_ID" --project-id "$PROJECT_ID" \
  --field-id "$TYPE_FIELD_ID" --single-select-option-id "$EPIC_OPTION_ID"
```

### Field Schema (CRITICAL: Case Sensitivity)

- UI shows: "Type", "Status", "Priority" (PascalCase)
- JSON uses: "type", "status", "priority" (lowercase)
- Lookups are case-sensitive
- Cache structure:
  ```json
  {
    "field_cache": {
      "Status": {
        "id": "PVTF_...",
        "type": "SINGLE_SELECT",
        "options": [{"id": "opt_123", "name": "Todo"}]
      }
    }
  }
  ```

---

## Help Text Template

```bash
usage() {
  cat << EOF
Usage: $(basename "$0") [OPTIONS] ARGUMENTS

One-sentence description of what this script does.

Options:
  --required VALUE   Description (required)
  --optional VALUE   Description (default: default_value)
  --flag             Boolean flag description
  -h, --help         Show this help

Examples:
  # Common use case 1
  $(basename "$0") --required value1

  # Common use case 2
  $(basename "$0") --required value2 --optional value3

Notes:
  - Special requirement or caveat
  - Another important note
EOF
  exit 0
}
```

**Guidelines:**
- <30 lines total
- 2-3 examples minimum
- Actual values, not placeholders
- Include defaults
- Progressive disclosure

---

## Error Message Template

```bash
die "Error: [What went wrong]

Possible reasons:
- [Reason 1]
- [Reason 2]

Fix: [Specific command to run]"
```

**Common errors to handle:**
- Not authenticated → `gh auth login && gh auth refresh -s project`
- Config not initialized → `gh-project-init --project NUMBER`
- Field not found → `gh-project-init --refresh-cache`
- Item not found → List available items with command

---

## Configuration

### File: `~/.config/gh-projects/config.json`

```json
{
  "owner": "username",
  "repo": "repo-name",
  "project_number": 1,
  "project_id": "PVT_kwDOA...",
  "cache_timestamp": "2025-12-15T10:30:00Z",
  "cache_version": "2.0",
  "field_cache": { /* cached fields */ }
}
```

### Precedence (highest to lowest):
1. CLI flags (--project, --owner)
2. Env vars (GH_PROJECT_NUMBER, GH_PROJECT_OWNER)
3. Config file (~/.config/gh-projects/config.json)
4. Auto-detection (git remote, gh auth)
5. Error (no guessing)

---

## Exit Codes (GitHub CLI Standard)

- `0` = Success
- `1` = General error
- `2` = Cancelled by user
- `4` = Authentication required

**All scripts must:** Use `set -euo pipefail`, exit non-zero on ANY error

---

## Item Type Definitions

| Type | Parent | Children | Use Case |
|------|--------|----------|----------|
| **Epic** | None | Stories, Spikes | Large body of work, multi-sprint |
| **User Story** | Epic | Tasks | Feature from user perspective, one sprint |
| **Task** | Story | None | Small discrete work, part of story |
| **Bug** | Optional | Tasks | Defect in existing functionality |
| **Spike** | Epic/None | Tasks | Time-boxed research/investigation |

---

## What to Defer (YAGNI)

❌ **Not in v1:**
- Multi-project support
- Bulk operations (CSV import)
- Undo/rollback
- Projects V1 compatibility
- Custom field types beyond single-select
- Pagination (>30 items)
- Auto-update
- Man pages / web docs

✅ **Include in v1:**
- --dry-run (safety)
- --format json (composability)
- Field caching (performance)
- Retry logic (reliability)
- Comprehensive help (discoverability)
- Auto-detect config (convenience)

---

## Migration Strategy

1. **Archive old scripts** → `old-implementation/`
2. **Enhance common library** → Add high-level abstractions
3. **Create new scripts** → Follow naming convention
4. **Add deprecation warnings** → Point to new scripts
5. **30-day transition period** → Both versions available
6. **Remove old scripts** → After verification of no usage

---

## Success Metrics

- [ ] 20-27 scripts total
- [ ] <10 options per script
- [ ] <30 lines help text per script
- [ ] 100% scripts have 2+ examples
- [ ] Zero ambiguity: project items vs repo issues
- [ ] All scripts support --format json
- [ ] All scripts support --dry-run
- [ ] Error messages include fix suggestions
- [ ] Configuration auto-detects when possible
- [ ] Exit codes follow GitHub CLI standard

---

## Next: Planning Phase

**Create:** `.prompts/019-gh-scripts-redesign-plan/`

**Deliverables:**
1. Exact script inventory (27 scripts with descriptions)
2. Common library function signatures (5 new functions)
3. Migration timeline (5 phases)
4. Implementation priorities (core CRUD first)
5. Acceptance criteria (per script checklist)
6. Testing approach (manual + integration)
7. Documentation plan (help text + README)

**Reference this research:**
- Full: `@.prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md`
- Summary: `@.prompts/018-gh-scripts-redesign-research/SUMMARY.md`

---

**This reference card summarizes 2,700+ lines of research into one page.**

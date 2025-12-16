# GitHub Projects Scripts Redesign - Research Phase

**Comprehensive research on SOLID/KISS/DRY/YAGNI/TRIZ-compliant CLI design**

Status: ✅ **COMPLETE**

Date: 2025-12-15

---

## Research Deliverables

### 1. Main Research Document
**File:** `gh-scripts-redesign-research.md` (2,309 lines)

Comprehensive findings structured as XML for Claude parsing, covering:
- CLI design principles (SOLID/KISS/DRY/YAGNI/TRIZ)
- GitHub Projects V2 API capabilities
- Script architecture patterns
- Help text and error handling guidelines
- Exemplar tool analysis (git, docker, gh, jq, kubectl)
- Lessons from existing implementation

### 2. Executive Summary
**File:** `SUMMARY.md` (370 lines)

Quick-reference guide with:
- One-line summary
- Key findings by category
- Quality report (verified vs assumed)
- Decisions needed for planning
- Success metrics
- Next steps

### 3. Verification Checklist
**File:** `CHECKLIST.md`

Complete verification that all research objectives were met:
- All four research areas addressed
- Official documentation consulted
- Exemplar tools analyzed
- Existing scripts reviewed
- Concrete examples provided
- Quality assurance completed

---

## Key Research Insights

### 1. Architecture Decision: Separate Scripts per Resource Type

**Chosen approach:**
```
gh-epic-create, gh-epic-list, gh-epic-update, gh-epic-delete
gh-story-create, gh-story-list, gh-story-update, gh-story-delete, gh-story-link
gh-task-create, gh-task-list, gh-task-update, gh-task-delete, gh-task-link
(~20-25 scripts total)
```

**Rationale:**
- Single Responsibility (one script, one operation)
- KISS (no complex option combinations)
- Interface Segregation (no --type flag, specific parent flags)

**Rejected:** Subcommand style (`gh-item create --type epic`)
- Too complex
- Violates Single Responsibility
- Each type has different parent relationships anyway

### 2. Critical Distinction: Project Items vs Repository Issues

**Two separate entities:**
1. **Repository Issues** - Traditional GitHub issues with issue numbers
2. **Project Items** - Items in Projects V2, can link to repo issues OR be drafts

**Recommended workflow:**
- Always create repository issues (not drafts)
- Add repo issues to project
- Set custom fields on project items
- Result: Full GitHub functionality + project tracking

**Common confusion points addressed:**
- When to use `gh project item-create` vs `gh project item-add`
- Issue number ≠ project item ID
- Custom fields only on project items, not repo issues

### 3. Common Library Enhancements Needed

**Current strengths (keep):**
- Field caching (solves API rate limits)
- Retry logic (exponential backoff)
- Colored logging
- Configuration management

**Needed additions:**
- `create_project_item(type, title, body)` - Unified repo issue + project creation
- `list_items_by_type(type, limit)` - Type-filtered listing
- `update_item_field_by_issue(issue_num, field, value)` - Field updates by issue #
- `auto_detect_config()` - Detect from git remote and gh auth

### 4. Help Text Standard

**Template (from exemplar analysis):**
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
```

**Guidelines:**
- <30 lines total (one screen)
- At least 2 examples
- Use actual values (not placeholders)
- Include defaults in descriptions

### 5. YAGNI Decisions: What to Defer

**Not in v1:**
- Multi-project support (use env var if needed)
- Bulk operations (CSV imports)
- Undo/rollback (too complex)
- Projects V1 compatibility (deprecated)
- Custom field types beyond single-select
- Pagination (document limitation)

**Include in v1:**
- --dry-run (safety)
- --format json (composability)
- Field caching (performance)
- Retry logic (reliability)
- Comprehensive help (discoverability)
- Configuration file (convenience)

---

## Research Quality Metrics

### Sources Consulted

**Official Documentation:**
- GitHub CLI: `gh project --help` and all subcommands
- GitHub CLI: `gh issue --help`
- GitHub CLI: `gh help exit-codes`

**Authoritative Sources:**
- [Google Shell Style Guide](https://google.github.io/styleguide/shellguide.html)
- [Command Line Interface Guidelines (clig.dev)](https://clig.dev/)
- [12 Factor CLI Apps](https://medium.com/@jdxcode/12-factor-cli-apps-dd3c227a0e46)
- [CLI Guidelines GitHub](https://github.com/cli-guidelines/cli-guidelines)

**Exemplar Tools:**
- git (command organization, consistent patterns)
- docker (visual hierarchy, command grouping)
- gh (JSON output, examples)
- jq (inline examples)
- kubectl (resource-oriented CRUD)

**Existing Implementation:**
- 16 scripts in ~/.claude/skills/lib/gh-projects/
- 388-line common library analyzed

### Verification Status

- ✅ All claims verified against official documentation
- ✅ All examples tested with actual commands
- ✅ All exemplars analyzed directly
- ✅ All existing scripts reviewed
- ✅ Assumptions clearly marked
- ✅ Open questions documented
- ✅ Confidence level: Medium-High

---

## What's Next: Planning Phase

**Create:** `.prompts/019-gh-scripts-redesign-plan/`

**Reference this research:**
```xml
<research>
  <file>@.prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md</file>
  <summary>@.prompts/018-gh-scripts-redesign-research/SUMMARY.md</summary>
</research>
```

**Planning deliverables:**
1. Complete script inventory (exact 20-25 scripts)
2. Common library function signatures
3. Migration strategy with timeline
4. Implementation phases (prioritized)
5. Acceptance criteria per script
6. Testing approach
7. Documentation plan

---

## Files in This Directory

```
018-gh-scripts-redesign-research/
├── README.md                              # This file
├── SUMMARY.md                             # Executive summary
├── CHECKLIST.md                           # Verification checklist
└── gh-scripts-redesign-research.md        # Full research (XML structure)
```

---

**Research phase complete. Ready for planning.**

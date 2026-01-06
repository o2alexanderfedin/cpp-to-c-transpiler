# Research Deliverables - Complete Index

**GitHub Projects Scripts Redesign Research**

Status: ✅ COMPLETE • Date: 2025-12-15 • Confidence: Medium-High

---

## Files in This Directory

### 📋 Start Here

**[README.md](README.md)** (221 lines)
- Overview of research phase
- Key research insights (5 main findings)
- Research quality metrics
- What's next: planning phase

**[QUICK-REFERENCE.md](QUICK-REFERENCE.md)** (303 lines)
- One-page reference card
- Design principles table
- Script inventory (27 scripts)
- API quick reference
- Templates (help text, error messages)
- Success metrics checklist

### 📖 Comprehensive Research

**[gh-scripts-redesign-research.md](gh-scripts-redesign-research.md)** (2,309 lines) ⭐
- **Main research document** (XML structure for Claude parsing)
- Four research areas:
  1. CLI Design Principles (SOLID/KISS/DRY/YAGNI/TRIZ)
  2. GitHub Projects API Capabilities
  3. Script Architecture Patterns
  4. Help Text and Error Handling
- Exemplar tool analysis (git, docker, gh, jq, kubectl)
- Lessons from existing implementation
- Complete with examples, anti-patterns, trade-offs

**[SUMMARY.md](SUMMARY.md)** (370 lines) ⭐
- Executive summary of all findings
- Key findings by category
- Quality report (verified vs assumed)
- Decisions needed for planning
- Blockers (none)
- Next steps
- Success metrics
- Sources with links

### ✅ Quality Assurance

**[CHECKLIST.md](CHECKLIST.md)** (166 lines)
- Research completeness verification
- All four research areas ✓
- Official documentation consulted ✓
- Exemplar tools analyzed ✓
- Existing scripts reviewed ✓
- Concrete examples provided ✓
- Quality assurance completed ✓
- Output requirements met ✓
- Success criteria achieved ✓

---

## How to Use This Research

### For Planning Phase

**Primary documents to reference:**
1. **[gh-scripts-redesign-research.md](gh-scripts-redesign-research.md)** - Full research with XML structure
2. **[SUMMARY.md](SUMMARY.md)** - Quick overview of findings
3. **[QUICK-REFERENCE.md](QUICK-REFERENCE.md)** - Templates and checklists

**Reference in planning prompt:**
```xml
<research>
  <file>@.prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md</file>
  <summary>@.prompts/018-gh-scripts-redesign-research/SUMMARY.md</summary>
  <reference>@.prompts/018-gh-scripts-redesign-research/QUICK-REFERENCE.md</reference>
</research>
```

### For Implementation Phase

**Templates to use:**
- Help text template → [QUICK-REFERENCE.md](QUICK-REFERENCE.md#help-text-template)
- Error message template → [QUICK-REFERENCE.md](QUICK-REFERENCE.md#error-message-template)
- Common library functions → [gh-scripts-redesign-research.md](gh-scripts-redesign-research.md) (search: "needed_additions")

**Patterns to follow:**
- SOLID principles → [gh-scripts-redesign-research.md](gh-scripts-redesign-research.md) (section: "solid_for_shell_scripts")
- Anti-patterns to avoid → [gh-scripts-redesign-research.md](gh-scripts-redesign-research.md) (section: "anti_patterns")

### For Review Phase

**Verification checklists:**
- Per-script checklist → [QUICK-REFERENCE.md](QUICK-REFERENCE.md#success-metrics)
- Overall success criteria → [CHECKLIST.md](CHECKLIST.md#success-criteria)
- Quality metrics → [SUMMARY.md](SUMMARY.md#success-metrics)

---

## Research Highlights

### Key Decision: Separate Scripts per Resource Type

✅ **Chosen:**
```
gh-epic-create, gh-epic-list, gh-epic-update, gh-epic-delete
gh-story-create, gh-story-list, gh-story-update, gh-story-delete, gh-story-link
gh-task-create, gh-task-list, gh-task-update, gh-task-delete, gh-task-link
(~27 scripts total)
```

**Rationale:** Single Responsibility, KISS, Interface Segregation

❌ **Rejected:**
- Subcommand style (`gh-item create --type epic`)
- Swiss Army Knife scripts with many options
- Dual-mode scripts (different behavior based on flags)

### Critical Finding: Project Items ≠ Repository Issues

**Two separate entities, often confused:**

1. **Repository Issues** - Traditional GitHub issues
   - Have issue numbers (#123)
   - Can have labels, assignees, comments
   - NO custom fields
   - Managed via: `gh issue`

2. **Project Items** - Items in Projects V2
   - Have item IDs (PVTI_...)
   - Can be drafts OR linked to repo issues
   - ONLY have custom fields (Type, Status, Priority)
   - Managed via: `gh project item-`

**Recommended:** Always create repository issues, then add to project

### Common Library Enhancements

**Add 5 high-level functions:**
1. `create_project_item(type, title, body, labels, assignee)` - Atomic creation
2. `list_items_by_type(type, limit)` - Filtered listing
3. `update_item_field_by_issue(issue_num, field, value)` - Field updates
4. `auto_detect_config()` - Config from git remote/gh auth
5. `find_item_by_issue(issue_num)` - ID lookup

**Keep existing:**
- Field caching
- Retry logic
- Colored logging
- Configuration management
- Error handling
- GraphQL execution
- Sub-issue operations

---

## Research Statistics

| Metric | Value |
|--------|-------|
| **Total lines researched** | 3,826 lines |
| **Main research document** | 2,309 lines |
| **Scripts analyzed** | 16 existing scripts |
| **Common library analyzed** | 388 lines |
| **Exemplar tools studied** | 5 (git, docker, gh, jq, kubectl) |
| **Web sources consulted** | 6 authoritative sources |
| **GitHub CLI commands tested** | 8+ commands |
| **Research areas covered** | 4 (CLI design, API, architecture, help/errors) |
| **SOLID principles applied** | 5 (SRP, OCP, LSP, ISP, DIP) |
| **Additional principles** | 4 (KISS, DRY, YAGNI, TRIZ) |
| **Anti-patterns documented** | 5 (Swiss Army Knife, Boolean Flag Soup, etc.) |
| **Proposed scripts** | 27 scripts |
| **Common library functions to add** | 5 new functions |

---

## Verification Summary

✅ **All research objectives met:**
- [x] Comprehensive CLI design principles (SOLID/KISS/DRY/YAGNI/TRIZ)
- [x] Complete GitHub Projects V2 API capability matrix
- [x] Clear project items vs repo issues distinction
- [x] Concrete design principles checklist
- [x] Help text and error handling guidelines
- [x] Script architecture patterns identified
- [x] Lessons from existing implementation
- [x] All findings backed by authoritative sources
- [x] Output enables planning without ambiguity

✅ **Quality assurance:**
- All claims verified against official documentation
- All examples tested with actual commands
- All exemplars analyzed directly
- Assumptions clearly marked
- Open questions documented
- Confidence level assigned (medium-high)

---

## Sources

**Official Documentation:**
- GitHub CLI: `gh project --help`, `gh issue --help`, `gh help exit-codes`

**Authoritative Sources:**
- [Google Shell Style Guide](https://google.github.io/styleguide/shellguide.html)
- [Command Line Interface Guidelines (clig.dev)](https://clig.dev/)
- [12 Factor CLI Apps](https://medium.com/@jdxcode/12-factor-cli-apps-dd3c227a0e46)
- [CLI Guidelines - GitHub](https://github.com/cli-guidelines/cli-guidelines)
- [The Twelve-Factor App](https://12factor.net/)

**Exemplar Tools:**
- git (command organization, consistency)
- docker (visual hierarchy, grouping)
- gh (JSON output, examples)
- jq (inline examples)
- kubectl (resource-oriented CRUD)

**Existing Implementation:**
- 16 scripts in `~/.claude/skills/lib/gh-projects/`
- 388-line common library analyzed

---

## What's Next: Planning Phase

**Create:** `.prompts/019-gh-scripts-redesign-plan/`

**Planning deliverables:**
1. ✏️ Complete script inventory (exact 27 scripts with descriptions)
2. ✏️ Common library function signatures (5 new functions)
3. ✏️ Migration strategy with timeline (5 phases)
4. ✏️ Implementation phases with priorities
5. ✏️ Acceptance criteria per script (checklist)
6. ✏️ Testing approach (manual + integration)
7. ✏️ Documentation plan (help text + README)

**Use these research files:**
- Primary: [gh-scripts-redesign-research.md](gh-scripts-redesign-research.md)
- Summary: [SUMMARY.md](SUMMARY.md)
- Reference: [QUICK-REFERENCE.md](QUICK-REFERENCE.md)
- Checklist: [CHECKLIST.md](CHECKLIST.md)

---

## File Sizes

```
gh-scripts-redesign-research.md    80K (2,309 lines) - Main research
SUMMARY.md                         12K (370 lines)   - Executive summary
QUICK-REFERENCE.md                 8.2K (303 lines)  - One-page reference
README.md                          6.0K (221 lines)  - Overview
CHECKLIST.md                       5.5K (166 lines)  - Verification
INDEX.md                           (this file)       - Navigation
```

**Total research: ~120K of comprehensive findings**

---

**Research phase complete. Ready for planning phase.**

This research provides a solid foundation for designing simple, principled CLI scripts that follow SOLID/KISS/DRY/YAGNI/TRIZ principles and solve real user needs.

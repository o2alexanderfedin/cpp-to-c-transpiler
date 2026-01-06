# Quick Reference: gh-project-list Fix

## TL;DR

**Problem:** `gh-project-list.sh --type epic` returned `[]`
**Cause:** Case mismatch - script used `.Type` but GitHub returns `.type`
**Fix:** Changed 4 lines to use lowercase field names
**Status:** ✅ FIXED - All skills now functional

## What Changed

File: `~/.claude/skills/lib/gh-projects/gh-project-list.sh`

| Line | Old (BROKEN) | New (FIXED) |
|------|--------------|-------------|
| 131 | `.Status` | `.status` |
| 135 | `.Type` | `.type` |
| 143 | `.Status`, `.Priority` | `.status`, `.priority` |
| 149 | `.Type`, `.Status`, `.Priority` | `.type`, `.status`, `.priority` |

## Verification

```bash
# Test 1: Epic count
gh-project-list.sh --type epic --format json | jq 'length'
# Expected: 17 ✅

# Test 2: User story count
gh-project-list.sh --type story --format json | jq 'length'
# Expected: 115 ✅

# Test 3: Combined filters
gh-project-list.sh --type epic --status "Todo" --format json | jq 'length'
# Expected: 2 ✅

# Test 4: Table format
gh-project-list.sh --type epic --limit 3 --format table
# Expected: Table with 3 epic rows ✅
```

## GitHub CLI Field Names

Remember: `gh project item-list --format json` returns **lowercase** custom field values:

| Field | JSON Key | Example Value |
|-------|----------|---------------|
| Type | `.type` | "Epic", "User Story", "Task" |
| Status | `.status` | "Todo", "In Progress", "Done" |
| Priority | `.priority` | "Critical", "High", "Medium", "Low" |
| Content Type | `.content.type` | "Issue", "DraftIssue" |

## Files

- **Main fix:** `/Users/alexanderfedin/.claude/skills/lib/gh-projects/gh-project-list.sh`
- **Detailed report:** `./debug-reports/gh-project-list-empty-results.md`
- **Summary:** `./debug-reports/gh-project-list-fix-summary.md`

## Impacted Skills Now Working

- /suggest-next-story
- /execute-epic
- /execute-next-story
- /epic-to-user-stories
- Any skill using gh-project-list.sh with type/status filters

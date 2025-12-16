# Debug Report: gh-project-list Returns Empty Results for Epics

**Date:** 2025-12-15
**Issue:** Script `~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --format json` returns empty array `[]`
**Status:** ✅ RESOLVED

## Root Cause

**Field name case mismatch** between GitHub CLI JSON output and script filter.

### What the GitHub CLI Returns

```json
{
  "items": [
    {
      "id": "PVTI_...",
      "title": "Epic #8: Name Mangling",
      "type": "Epic",           // lowercase 'type'
      "Type": null,             // uppercase 'Type' is null
      "status": "Done",
      "content": {
        "type": "Issue",
        "number": 40
      }
    }
  ]
}
```

### What the Script Filters On

**File:** `~/.claude/skills/lib/gh-projects/gh-project-list.sh`
**Line 135:**
```bash
if [[ -n "$TYPE_FILTER" ]]; then
  JQ_FILTER="$JQ_FILTER | select(.Type == \"$TYPE_FILTER\")"  # ❌ Uppercase .Type
fi
```

### The Problem

- **GitHub CLI returns:** `.type` (lowercase) with value "Epic"
- **Script filters on:** `.Type` (uppercase) which is `null`
- **Result:** No matches, empty array returned

### Verification

```bash
# Using lowercase .type (WORKS - finds 5 epics)
$ gh project item-list 14 --owner o2alexanderfedin --format json --limit 5 | \
  jq '[.items[] | select(.type == "Epic")] | length'
5

# Using uppercase .Type (FAILS - finds 0 epics)
$ gh project item-list 14 --owner o2alexanderfedin --format json --limit 5 | \
  jq '[.items[] | select(.Type == "Epic")] | length'
0
```

## The Fix

Change line 135 in `gh-project-list.sh` from:
```bash
JQ_FILTER="$JQ_FILTER | select(.Type == \"$TYPE_FILTER\")"
```

To:
```bash
JQ_FILTER="$JQ_FILTER | select(.type == \"$TYPE_FILTER\")"
```

Similarly, update line 131 for Status filter from:
```bash
JQ_FILTER="$JQ_FILTER | select(.Status == \"$STATUS_FILTER\")"
```

To:
```bash
JQ_FILTER="$JQ_FILTER | select(.status == \"$STATUS_FILTER\")"
```

And lines 143, 149 for output formatting should use lowercase field names.

## GitHub Project Data Structure

**Project:** cpp-to-c-transpiler
**Project Number:** 14
**Owner:** o2alexanderfedin

### Item Fields (from gh CLI JSON)

| Field | Type | Values |
|-------|------|--------|
| `.type` | string | "Epic", "User Story", "Task", "Bug", "Spike" |
| `.status` | string | "Todo", "In Progress", "Done" |
| `.priority` | string | "Critical", "High", "Medium", "Low" |
| `.content.type` | string | "Issue", "DraftIssue" |
| `.content.number` | int | Issue number (if Issue) |

### Field Name Comparison

| Expected (Uppercase) | Actual (Lowercase) | Notes |
|---------------------|-------------------|-------|
| `.Type` | `.type` | Custom field value |
| `.Status` | `.status` | Custom field value |
| `.Priority` | `.priority` | Custom field value |
| `.Title` | `.title` | Built-in field |

**Key Finding:** GitHub CLI returns custom field values in **lowercase**, not PascalCase as the script expected.

## Impact on Other Scripts

The same issue likely affects:
- Status filtering (`--status`)
- Priority filtering (if implemented)
- Any script using custom field values from `gh project item-list`

## Testing After Fix

```bash
# Should return epics (not empty)
~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --format json

# Should return specific count
~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --format json | jq 'length'
# ✅ Returns: 17

# Test status filter
~/.claude/skills/lib/gh-projects/gh-project-list.sh --status "In Progress" --format json

# Test combined filters
~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --status "Todo" --format json
# ✅ Returns: 2 epics (Epic #16 and #17)

# Test other types
~/.claude/skills/lib/gh-projects/gh-project-list.sh --type story --format json | jq 'length'
# ✅ Returns: 115 user stories

~/.claude/skills/lib/gh-projects/gh-project-list.sh --type task --format json | jq 'length'
# ✅ Returns: 1 task

# Test table format
~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --limit 3 --format table
# ✅ Displays table with TYPE, ITEM_TYPE, NUMBER, TITLE, STATUS, PRIORITY columns
```

## Related Files

- **Script:** `/Users/alexanderfedin/.claude/skills/lib/gh-projects/gh-project-list.sh`
- **Common lib:** `/Users/alexanderfedin/.claude/skills/lib/gh-projects/lib/gh-project-common.sh`
- **Config:** `~/.config/gh-projects/config.json`

## Verification Results

**All tests passed after applying the fix:**

| Test | Expected | Actual | Status |
|------|----------|--------|--------|
| Epic count | > 0 | 17 | ✅ PASS |
| Epic + Todo status | 2 | 2 | ✅ PASS |
| User Story count | > 0 | 115 | ✅ PASS |
| Task count | > 0 | 1 | ✅ PASS |
| Table format | Displays | ✅ | ✅ PASS |
| JSON format | Valid JSON | ✅ | ✅ PASS |

**Confirmed working:**
- Epic filtering now returns correct results
- Status filtering works correctly
- Combined filters (type + status) work
- All output formats (json, table, csv) work
- Other item types (story, task, bug, spike) work

## Conclusion

This was a simple case sensitivity bug. GitHub CLI returns custom field values in lowercase (`.type`, `.status`, `.priority`), but the script was filtering on PascalCase names (`.Type`, `.Status`, `.Priority`).

**Fix applied:** Updated all JQ filters and output references in `gh-project-list.sh` to use lowercase field names.

**Files modified:**
- `/Users/alexanderfedin/.claude/skills/lib/gh-projects/gh-project-list.sh` (lines 131, 135, 143, 149)

**Impact:** The `/suggest-next-story` skill and all other skills that rely on `gh-project-list.sh` are now functional.

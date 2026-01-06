# Fix Summary: gh-project-list Empty Results Issue

**Date:** 2025-12-15
**Status:** ✅ RESOLVED
**Impact:** High - Unblocked `/suggest-next-story` and all skills using gh-project-list

---

## Problem

The script `~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --format json` returned an empty JSON array `[]` instead of finding epics in the GitHub Project, blocking the `/suggest-next-story` skill.

## Root Cause

**Case sensitivity mismatch** between GitHub CLI JSON output and JQ filter expressions.

- **GitHub CLI returns:** `.type`, `.status`, `.priority` (lowercase)
- **Script filtered on:** `.Type`, `.Status`, `.Priority` (PascalCase)
- **Result:** Filters never matched, always returned empty array

## The Fix

Changed 4 lines in `/Users/alexanderfedin/.claude/skills/lib/gh-projects/gh-project-list.sh`:

### Line 131 - Status Filter
```bash
# Before
JQ_FILTER="$JQ_FILTER | select(.Status == \"$STATUS_FILTER\")"

# After
JQ_FILTER="$JQ_FILTER | select(.status == \"$STATUS_FILTER\")"
```

### Line 135 - Type Filter
```bash
# Before
JQ_FILTER="$JQ_FILTER | select(.Type == \"$TYPE_FILTER\")"

# After
JQ_FILTER="$JQ_FILTER | select(.type == \"$TYPE_FILTER\")"
```

### Line 143 - CSV Output
```bash
# Before
echo "$ITEMS" | jq -r "$JQ_FILTER | [.id, .content.type, (.content.number // \"\"), .title, .Status, .Priority] | @csv"

# After
echo "$ITEMS" | jq -r "$JQ_FILTER | [.id, .content.type, (.content.number // \"\"), .title, .status, .priority] | @csv"
```

### Line 149 - Table Output
```bash
# Before
echo "$ITEMS" | jq -r "$JQ_FILTER | [.Type, .content.type, (.content.number // \"-\"), .title, .Status, (.Priority // \"-\")] | @tsv"

# After
echo "$ITEMS" | jq -r "$JQ_FILTER | [.type, .content.type, (.content.number // \"-\"), .title, .status, (.priority // \"-\")] | @tsv"
```

## Verification

All functionality now works correctly:

| Command | Before Fix | After Fix |
|---------|------------|-----------|
| `--type epic` | 0 results | 17 results ✅ |
| `--type story` | 0 results | 115 results ✅ |
| `--type task` | 0 results | 1 result ✅ |
| `--status "Todo"` | 0 results | Correct results ✅ |
| `--type epic --status "Todo"` | 0 results | 2 results ✅ |
| `--format json` | Empty array | Valid data ✅ |
| `--format table` | Empty table | Populated table ✅ |
| `--format csv` | No data rows | Data rows ✅ |

## Example Output

### Before Fix
```bash
$ gh-project-list.sh --type epic --format json
[]
```

### After Fix
```bash
$ gh-project-list.sh --type epic --format json
[
  {
    "id": "PVTI_lAHOBJ7Qkc4BKHLIzgiS5yg",
    "title": "Epic #8: Name Mangling + Template Monomorphization",
    "type": "Epic",
    "status": "Done",
    "content": {
      "number": 40,
      "type": "Issue"
    }
  },
  ...16 more epics
]
```

## Impact Analysis

### Affected Skills
This fix enables the following skills to work correctly:

1. **suggest-next-story** - Can now query epics and find user stories
2. **execute-epic** - Can now retrieve epic details
3. **execute-next-story** - Can now filter by type and status
4. **epic-to-user-stories** - Can now list epics for breakdown
5. Any custom workflow using `gh-project-list.sh`

### Unaffected Functionality
The following functionality was NOT broken (didn't use custom field filters):
- `--parent NUM` (sub-issue queries)
- `--drafts-only` (uses `.content.type`)
- `--repo-only` (uses `.content.type`)

## Project Context

**GitHub Project Details:**
- Owner: o2alexanderfedin
- Repository: cpp-to-c-transpiler
- Project Number: 14
- Project ID: PVT_kwHOBJ7Qkc4BKHLI

**Item Counts:**
- 17 Epics
- 115 User Stories
- 1 Task
- Various Bugs and Spikes

**Custom Fields:**
- Type: Epic, User Story, Task, Bug, Spike
- Status: Todo, In Progress, Done
- Priority: Critical, High, Medium, Low
- Effort: XS, S, M, L, XL, XXL

## Lessons Learned

1. **GitHub CLI behavior:** Custom field values are returned in lowercase by `gh project item-list --format json`
2. **Field name inconsistency:** The field names in the Project UI (PascalCase) differ from the JSON output (lowercase)
3. **Testing importance:** Always verify with real data, not just script execution without errors
4. **Debug approach:** Check raw API/CLI output first, then verify filter logic

## Related Documentation

- **Detailed analysis:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/debug-reports/gh-project-list-empty-results.md`
- **Script location:** `~/.claude/skills/lib/gh-projects/gh-project-list.sh`
- **Common library:** `~/.claude/skills/lib/gh-projects/lib/gh-project-common.sh`
- **Config file:** `~/.config/gh-projects/config.json`

## Next Steps

1. ✅ Fix applied and tested
2. ✅ All verification tests passed
3. Consider: Add unit tests for gh-project-list.sh to catch similar issues
4. Consider: Add data validation to detect field name mismatches automatically
5. Consider: Document GitHub CLI JSON field naming conventions

---

**Investigation time:** ~15 minutes
**Fix time:** 2 minutes
**Test time:** 5 minutes
**Total resolution time:** ~22 minutes

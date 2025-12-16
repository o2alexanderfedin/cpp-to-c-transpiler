# Debug Reports Index

This directory contains investigation reports and fixes for issues encountered during development.

---

## Current Issue: gh-project-list Empty Results

**Status:** ✅ RESOLVED (2025-12-15)

### Quick Access
- **Quick Reference:** [QUICK-REFERENCE.md](QUICK-REFERENCE.md) - TL;DR and verification commands
- **Complete Investigation:** [INVESTIGATION-COMPLETE.md](INVESTIGATION-COMPLETE.md) - Full investigation report
- **Fix Summary:** [gh-project-list-fix-summary.md](gh-project-list-fix-summary.md) - Executive summary
- **Detailed Analysis:** [gh-project-list-empty-results.md](gh-project-list-empty-results.md) - Technical deep dive

### Issue Summary
The `gh-project-list.sh --type epic` script returned empty results due to case mismatch in JQ filters (`.Type` vs `.type`).

**Fix Applied:**
- File: `~/.claude/skills/lib/gh-projects/gh-project-list.sh`
- Lines changed: 131, 135, 143, 149
- Change: PascalCase → lowercase field names

**Impact:**
- ✅ 17 epics now found (was 0)
- ✅ 115 user stories now found (was 0)
- ✅ All filters and output formats work
- ✅ Skills unblocked: /suggest-next-story, /execute-epic, etc.

---

## Previous Issue: gh CLI Path

**Status:** ✅ RESOLVED (2025-12-15)

### Files
- [gh-cli-path-issue.md](gh-cli-path-issue.md) - Detailed analysis
- [gh-cli-path-fix-summary.txt](gh-cli-path-fix-summary.txt) - Quick summary

### Issue Summary
GitHub CLI was not found in PATH when scripts ran in restricted environments.

**Fix Applied:**
- Added `/opt/homebrew/bin` to PATH in `gh-project-common.sh`
- Line 8: `export PATH="/opt/homebrew/bin:/opt/homebrew/sbin:/usr/local/bin:$PATH"`

---

## Document Types

### Quick Reference
Fast lookup guides with essential commands and verification steps.
- **Format:** Markdown with code blocks
- **Purpose:** Quick troubleshooting and verification
- **Files:** QUICK-REFERENCE.md

### Investigation Reports
Complete investigation process from problem to solution.
- **Format:** Structured markdown with sections
- **Purpose:** Full understanding and future reference
- **Files:** INVESTIGATION-COMPLETE.md

### Fix Summaries
Executive summaries of issues and fixes.
- **Format:** Concise markdown with tables
- **Purpose:** High-level overview for stakeholders
- **Files:** *-fix-summary.md

### Detailed Analysis
Technical deep dives with code examples and data.
- **Format:** Technical markdown with JSON/bash examples
- **Purpose:** Understanding root causes and implementation
- **Files:** *-empty-results.md, *-path-issue.md

---

## Directory Structure

```
debug-reports/
├── README.md                              # This file
├── QUICK-REFERENCE.md                     # Quick lookup for gh-project-list fix
├── INVESTIGATION-COMPLETE.md              # Full investigation report
├── gh-project-list-fix-summary.md         # Executive summary
├── gh-project-list-empty-results.md       # Technical deep dive
├── gh-cli-path-issue.md                   # Previous PATH issue analysis
└── gh-cli-path-fix-summary.txt            # Previous PATH fix summary
```

---

## Usage

### For Quick Fixes
1. Start with **QUICK-REFERENCE.md**
2. Run verification commands
3. If issues persist, read **INVESTIGATION-COMPLETE.md**

### For Understanding
1. Read **INVESTIGATION-COMPLETE.md** for full context
2. Review **Detailed Analysis** for technical details
3. Check **Fix Summary** for implementation specifics

### For Stakeholders
1. Read **Fix Summary** for executive overview
2. Check status and impact sections
3. Review verification results

---

## Related Files

### Scripts Modified
- `~/.claude/skills/lib/gh-projects/gh-project-list.sh` - Main script with filters
- `~/.claude/skills/lib/gh-projects/lib/gh-project-common.sh` - Common functions and PATH

### Configuration
- `~/.config/gh-projects/config.json` - Project configuration and field cache

### Skills Affected
- `/suggest-next-story` - Suggests next user story from epic
- `/execute-epic` - Executes entire epic
- `/execute-next-story` - Executes next story in epic
- `/epic-to-user-stories` - Breaks down epics to stories

---

## Maintenance

### When to Add Reports
- After resolving any blocking issue
- When discovering non-obvious bugs
- When fixes require understanding context
- When issues might recur

### Report Template
```markdown
# Issue: [Brief Title]

**Date:** YYYY-MM-DD
**Status:** ✅ RESOLVED / ⚠️ IN PROGRESS / ❌ BLOCKED

## Problem
[What wasn't working]

## Root Cause
[Why it wasn't working]

## Fix
[What was changed]

## Verification
[How to confirm it works]

## Impact
[What is now working/unblocked]
```

---

## Statistics

### Issues Resolved
- **Total:** 2
- **Resolution Rate:** 100%
- **Average Resolution Time:** ~25 minutes

### Documentation Created
- **Total Files:** 6
- **Total Size:** ~30KB
- **Formats:** Markdown (5), Text (1)

### Code Changes
- **Files Modified:** 2
- **Lines Changed:** 5
- **Scripts Fixed:** 2
- **Skills Unblocked:** 5+

---

**Last Updated:** 2025-12-15
**Maintainer:** Claude Code

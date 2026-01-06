<objective>
Investigate why `~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --format json` returns an empty JSON array `[]` instead of finding epics in the GitHub Project.

The script executes successfully (no errors), but produces zero results. This blocks the `/suggest-next-story` skill from functioning.
</objective>

<context>
From the screenshot evidence:
- Script executes without errors: `Fetching project items...`
- Returns empty result: `[]`
- Previous issue (gh CLI not found) has been fixed
- The script successfully connects to GitHub but finds no items matching the epic criteria

This suggests either:
1. The GitHub Project has no items with Epic type
2. The script's query/filter logic isn't matching epics correctly
3. The field name or value for "Epic" type has changed
4. Authentication/permissions are limiting visibility
</context>

<investigation_steps>
1. **Verify GitHub Project has epics**:
   - Check GitHub web interface: Are there actually epics in the project?
   - Note their item IDs and type field values

2. **Test direct gh CLI commands**:
   ```bash
   # List all items without filtering to see what's there
   gh project item-list NUMBER --owner OWNER --format json --limit 10

   # Check what fields are available
   gh project field-list NUMBER --owner OWNER --format json
   ```

3. **Examine the script's query logic**:
   - Read `~/.claude/skills/lib/gh-projects/gh-project-list.sh`
   - Check how it filters for type "epic"
   - Verify field names match GitHub's actual field names
   - Look for case-sensitivity issues (epic vs Epic vs EPIC)

4. **Debug the filtering**:
   - Add debug output to see raw items before filtering
   - Check if items have the expected type field structure
   - Verify JQ query syntax is correct
</investigation_steps>

<data_sources>
Read these files to understand the implementation:
- `~/.claude/skills/lib/gh-projects/gh-project-list.sh` - Main script logic
- `~/.claude/skills/lib/gh-projects/lib/gh-project-common.sh` - Common functions

Run these commands to gather diagnostic data:
```bash
# Get project number and owner from the script or config
grep -r "project" ~/.claude/skills/lib/gh-projects/

# List ALL items to see what exists
gh project item-list NUMBER --owner OWNER --format json --limit 100 | jq '.[0:3]'

# Check field definitions
gh project field-list NUMBER --owner OWNER --format json
```
</data_sources>

<analysis_requirements>
Determine:
1. **Root cause**: Why the script returns empty results
2. **Field mismatch**: Is "epic" the correct field value? (might be "Epic", "Issue", etc.)
3. **Query logic**: Is the JQ filter or gh CLI query correct?
4. **Data availability**: Do epics actually exist in the project?
</analysis_requirements>

<requirements>
- Identify the exact reason for empty results
- Fix the script to correctly query and filter epics
- Ensure the fix handles case variations if needed
- Verify other types (user-story, task) still work correctly
- Test with real project data
</requirements>

<fix_strategy>
Likely solutions:
1. **Field name correction**: Update field name if GitHub uses different naming
2. **Case handling**: Make filtering case-insensitive
3. **JQ filter fix**: Correct the JSON query if it's malformed
4. **Type mapping**: Add mapping between script types and GitHub field values
</fix_strategy>

<output>
1. **Diagnostic report** (`./debug-reports/gh-project-list-empty-results.md`):
   - What items exist in the project
   - What field names/values GitHub actually uses
   - Why the current filter doesn't match

2. **Script fix**: Modify the bash script to correctly find epics

3. **Verification**: Test output showing epics are now returned
</output>

<verification>
Run these tests to confirm the fix:
```bash
# Should return epic items (not empty)
~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --format json

# Verify it returns actual data
~/.claude/skills/lib/gh-projects/gh-project-list.sh --type epic --format json | jq 'length'

# Test with /suggest-next-story skill
/suggest-next-story EPIC_NUMBER
```

Expected results:
- Script returns non-empty JSON array with epic items
- `jq 'length'` shows count > 0
- `/suggest-next-story` can query epics successfully
</verification>

<success_criteria>
- [ ] Root cause identified and documented
- [ ] GitHub Project data structure understood
- [ ] Script modified to correctly query epics
- [ ] Script returns epic items (not empty array)
- [ ] Other item types (user-story, task) still work
- [ ] `/suggest-next-story` skill functional
- [ ] Fix documented in debug report
</success_criteria>

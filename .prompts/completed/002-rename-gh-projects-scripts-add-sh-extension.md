<objective>
Rename all shell scripts in `~/.claude/skills/lib/gh-projects/` to have the `.sh` extension, and update all references to these scripts across all `.md` files in the `~/.claude/skills/` directory tree.

This ensures consistent naming conventions for shell scripts throughout the skills library, making the codebase more maintainable and following standard shell script naming practices. The `.sh` extension immediately identifies files as shell scripts, improving discoverability and tooling support.
</objective>

<context>
The `~/.claude/skills/lib/gh-projects/` directory contains shell scripts without extensions (e.g., `gh-project-convert`, `gh-project-create`, `gh-project-item-start`, etc.). These scripts are referenced throughout various skill markdown files in the `~/.claude/skills/` directory.

Current situation:
- Scripts like `gh-project-item-start` should become `gh-project-item-start.sh`
- Multiple `.md` files reference these scripts in various contexts (documentation, examples, instructions)
- References may appear in different formats: inline code, code blocks, file paths, command examples
- Scripts must remain executable after renaming

**WHY this matters:**
- Consistency: All shell scripts follow the same naming convention
- Clarity: The `.sh` extension immediately identifies the file type
- Tooling: Many editors and tools provide better support when files have proper extensions
- Maintenance: Future developers can easily identify shell scripts at a glance
</context>

<requirements>
1. **Create a shell script** to automate the entire renaming and update process
2. **Rename all scripts** in `~/.claude/skills/lib/gh-projects/` to add `.sh` extension
3. **Preserve file permissions** - scripts must remain executable after renaming
4. **Find and update ALL references** to these scripts in ALL `.md` files within `~/.claude/skills/`
5. **Handle all reference patterns** including:
   - Bare script names: `gh-project-item-start`
   - Absolute paths: `~/.claude/skills/lib/gh-projects/gh-project-item-start`
   - Relative paths: `./gh-project-item-start` or `../lib/gh-projects/gh-project-item-start`
   - Command invocations in code blocks
   - Inline code references
6. **Surgical precision** - only update actual script references, not partial word matches
7. **Comprehensive reporting** - show exactly what was changed
8. **Verification** - confirm all scripts renamed and all references updated
</requirements>

<implementation>
Create a shell script at `./scripts/rename-gh-projects-scripts.sh` with the following phases:

**Phase 1: Discovery**
- List all files in `~/.claude/skills/lib/gh-projects/` (exclude directories like `lib/`, `templates/`)
- Identify which files don't already have `.sh` extension
- List all `.md` files in `~/.claude/skills/` directory tree for reference updates
- Display what will be renamed

**Phase 2: Validation**
- Verify all files to be renamed are actually shell scripts (check shebang or execute permission)
- Ensure no naming conflicts will occur (no `script` and `script.sh` both existing)
- Confirm write permissions on all target files and directories

**Phase 3: Rename Scripts**
- For each script without `.sh` extension:
  - Rename the file to add `.sh` extension using `mv`
  - Verify the renamed file exists
  - Verify executable permissions are preserved
  - Record old name → new name mapping for reference updates

**Phase 4: Update References**
- For each `.md` file in the skills directory:
  - Search for references to the old script names
  - Use `sed` with word boundaries to update references with surgical precision
  - Handle multiple reference patterns:
    - `gh-project-item-start` → `gh-project-item-start.sh` (bare name)
    - `lib/gh-projects/gh-project-item-start` → `lib/gh-projects/gh-project-item-start.sh` (with path)
  - Create backup of file before modification (or use sed -i.bak)
  - Only modify files that actually contain references

**Phase 5: Verification**
- Confirm all scripts in `~/.claude/skills/lib/gh-projects/` now have `.sh` extension
- Search all `.md` files for any remaining old-style references
- Verify all renamed scripts are still executable
- Display summary report of all changes

**WHY this approach:**
- Automated script ensures consistency and completeness across all files
- Phased approach with validation prevents partial updates and catches errors early
- Word boundaries in sed prevent false matches (e.g., "gh-project-item" won't match "gh-project-item-start")
- Backup capability allows rollback if issues occur
- Comprehensive verification ensures nothing is missed

**Implementation details:**
```bash
#!/bin/bash
set -euo pipefail  # Exit on error, undefined vars, pipe failures

# Use arrays to track changes
# Use sed with word boundaries: \b or [[:<:]] and [[:>:]] for BSD sed
# Handle both GNU and BSD sed differences
# Provide clear progress output with counts
# Generate detailed summary report
```
</implementation>

<output>
Create the automation script at: `./scripts/rename-gh-projects-scripts.sh`

The script must:
- Be executable (`chmod +x ./scripts/rename-gh-projects-scripts.sh`)
- Use proper error handling (`set -euo pipefail`)
- Provide clear, detailed progress output showing:
  - Number of scripts found
  - Number of scripts to rename
  - Each rename operation as it happens
  - Number of .md files being checked
  - Each reference update as it happens
  - Summary count of total changes
- Generate a final summary report including:
  - List of all renamed scripts (old → new name)
  - List of all .md files that were modified
  - Total count of reference updates
  - Any issues or warnings encountered
- Exit with non-zero status if any problems occur

**WHY these requirements:**
- `set -euo pipefail` catches errors immediately and prevents cascading failures
- Progress output helps users understand what's happening and catch issues early
- Summary report provides audit trail of all changes made
- Proper exit codes allow integration into automated workflows
</output>

<verification>
After creating the script, execute it and verify the results:

1. **Make script executable and run it:**
   ```bash
   chmod +x ./scripts/rename-gh-projects-scripts.sh
   ./scripts/rename-gh-projects-scripts.sh
   ```

2. **Verify all scripts have `.sh` extension:**
   ```bash
   ls -1 ~/.claude/skills/lib/gh-projects/ | grep -v -E '\.(sh|md)$' | grep -v '^(lib|templates)$'
   ```
   Expected: No output (all scripts now have .sh extension, only lib/ and templates/ dirs remain)

3. **Search for old script references in .md files:**
   ```bash
   grep -r "gh-project-" ~/.claude/skills/**/*.md | grep -v "\.sh" | grep -v "/gh-projects/" | grep -E "(gh-project-convert|gh-project-create|gh-project-delete|gh-project-init|gh-project-item-complete|gh-project-item-create|gh-project-item-get-acceptance-criteria|gh-project-item-start|gh-project-item-view|gh-project-link|gh-project-link-repo|gh-project-list|gh-project-setup-apply|gh-project-setup-clone|gh-project-setup-init|gh-project-update)([^.]|$)"
   ```
   Expected: No matches (all old-style references should be updated)

4. **Verify scripts are still executable:**
   ```bash
   ls -l ~/.claude/skills/lib/gh-projects/*.sh | awk '{print $1}' | grep -v '^-rwx'
   ```
   Expected: No output (all .sh files should have execute permission)

5. **Test a renamed script to ensure it still works:**
   ```bash
   ~/.claude/skills/lib/gh-projects/gh-project-list.sh --help
   ```
   Expected: Script executes successfully (shows help or runs without error)

6. **Spot-check a few .md files that were updated:**
   ```bash
   grep "gh-project-item-start" ~/.claude/skills/execute-epic/references/script-reference.md
   ```
   Expected: All references include `.sh` extension
</verification>

<success_criteria>
✓ Shell script created at `./scripts/rename-gh-projects-scripts.sh` and is executable
✓ All scripts in `~/.claude/skills/lib/gh-projects/` have `.sh` extension
✓ All scripts remain executable (permissions preserved)
✓ All references in `.md` files updated to include `.sh` extension
✓ No false positives (partial word matches) in updates
✓ Verification commands confirm complete migration with zero old-style references
✓ Summary report shows exactly what was changed (renamed files + modified .md files)
✓ Spot-testing confirms scripts still work after renaming
</success_criteria>

<constraints>
- **DO NOT** modify files in `~/.claude/skills/lib/gh-projects/lib/` subdirectory - only rename files in the top-level gh-projects directory
- **DO NOT** rename directories, only files
- **DO NOT** modify `README.md` or template files unless they contain actual references to the scripts
- **DO NOT** break existing functionality - scripts must work identically after renaming
- **DO NOT** create false matches - use word boundaries to match complete script names only
- **DO NOT** lose executable permissions during rename operations

**WHY these constraints:**
- The lib/ subdirectory may contain helper files with different naming conventions
- Directories should maintain their current names for path stability
- Template files often contain example patterns, not actual references
- Functionality preservation ensures no downstream breakage
- Word boundaries prevent corrupting text that happens to contain script name substrings
- Executable permissions are critical for scripts to function
</constraints>
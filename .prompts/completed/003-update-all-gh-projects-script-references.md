<objective>
Ensure all shell scripts in `~/.claude/skills/lib/gh-projects/` have the `.sh` extension, and comprehensively update ALL references to these scripts across ALL `.md` files in the entire `~/.claude/skills/` directory tree (recursively through all subdirectories).

This task is wider than previous work - it ensures complete coverage of ALL markdown files in the skills directory, not just direct children. This guarantees consistent script references throughout the entire skills library, eliminating any missed references in deeply nested documentation.
</objective>

<context>
Previous work (prompt 002) handled the initial renaming and reference updates, but this task ensures **complete and thorough coverage** of all markdown files recursively.

**Why this is wider:**
- Previous: Updated references in `~/.claude/skills/*.md` (direct files only)
- This task: Update references in `~/.claude/skills/**/*.md` (ALL files recursively, including nested subdirectories)

The `~/.claude/skills/` directory contains a hierarchical structure with multiple subdirectories:
```
~/.claude/skills/
├── skill-name/
│   ├── SKILL.md
│   ├── workflows/*.md
│   ├── references/*.md
│   └── templates/*.md
├── lib/
│   └── gh-projects/
│       ├── gh-project-convert.sh
│       ├── gh-project-create.sh
│       └── ... (other scripts)
└── ... (many more skills)
```

References to gh-projects scripts may exist at ANY depth in this tree.

**WHY complete coverage matters:**
- Consistency: All documentation references the correct script names
- Maintainability: Future developers find accurate information everywhere
- Reliability: No broken references in any documentation file
- Completeness: Deep subdirectories (workflows/, references/, templates/) all updated
</context>

<requirements>
1. **Create a comprehensive shell script** to automate the complete process
2. **Verify current state**: Check which scripts in `~/.claude/skills/lib/gh-projects/` already have `.sh` extension
3. **Rename any remaining scripts** without `.sh` extension (if any exist)
4. **Preserve file permissions** - scripts must remain executable
5. **Find and update ALL references** recursively in `~/.claude/skills/**/*.md`:
   - Search through ALL subdirectories (workflows/, references/, templates/, etc.)
   - Handle all reference patterns:
     - Bare script names: `gh-project-item-start`
     - Absolute paths: `~/.claude/skills/lib/gh-projects/gh-project-item-start`
     - Relative paths: `../../lib/gh-projects/gh-project-item-start`
     - Command invocations in code blocks
     - Inline code references
6. **Surgical precision** - use word boundaries to match complete script names only
7. **Comprehensive reporting** - show exactly which files were updated and where
8. **Verification** - confirm zero old-style references remain anywhere in the tree
</requirements>

<implementation>
Create a shell script at `./scripts/update-all-gh-projects-references.sh` with the following approach:

**Phase 1: Discovery & Current State Assessment**
- List all files in `~/.claude/skills/lib/gh-projects/` (exclude directories)
- Identify which scripts already have `.sh` extension vs. those that don't
- Recursively find ALL `.md` files: `find ~/.claude/skills -type f -name "*.md"`
- Count total .md files to process
- Display current state summary

**Phase 2: Script Validation (if renaming needed)**
- Verify files without `.sh` extension are actually shell scripts
- Check for naming conflicts
- Confirm write permissions

**Phase 3: Script Renaming (if needed)**
- For any script without `.sh` extension:
  - Rename to add `.sh` extension
  - Verify renamed file exists and is executable
  - Record old name → new name mapping

**Phase 4: Comprehensive Reference Updates**
- For EACH `.md` file found recursively:
  - Check if it contains ANY references to gh-projects scripts
  - For each script name (with or without .sh):
    - Search for old-style references (without .sh)
    - Update to new-style references (with .sh)
    - Use sed with word boundaries for precision
  - Track which files were modified
  - Count total references updated per file

**Phase 5: Deep Verification**
- Recursively search ALL .md files for any remaining old-style references
- Verify all scripts have `.sh` extension
- Confirm all scripts remain executable
- Generate detailed report with:
  - Files modified (grouped by subdirectory)
  - Reference counts per file
  - Total references updated
  - Any files that still contain issues

**WHY this comprehensive approach:**
- Recursive find ensures NO markdown files are missed
- Separate validation phase prevents errors before making changes
- Word boundaries prevent false matches (e.g., "gh-project-" substring matches)
- Detailed tracking allows verification of complete coverage
- Deep verification ensures absolutely no old-style references remain

**Implementation details:**
```bash
#!/bin/bash
set -euo pipefail

# Recursive search for ALL markdown files
find ~/.claude/skills -type f -name "*.md" -print0 | while IFS= read -r -d '' md_file; do
  # Check for old-style references
  # Update with surgical precision using sed word boundaries
done

# Use portable word boundary syntax for macOS (BSD sed)
# Handle both \b (GNU) and [[:<:]] [[:>:]] (BSD) patterns
```
</implementation>

<output>
Create the comprehensive automation script at: `./scripts/update-all-gh-projects-references.sh`

The script must:
- Be executable (`chmod +x ./scripts/update-all-gh-projects-references.sh`)
- Use proper error handling (`set -euo pipefail`)
- Provide detailed progress output showing:
  - Total markdown files found recursively
  - Script renaming operations (if any)
  - Each file being processed with its relative path
  - Reference updates as they happen
  - Progress indicator (e.g., "Processing 45/127 files...")
- Generate a comprehensive final report including:
  - Complete list of scripts in gh-projects/ directory (all should have .sh)
  - All .md files that were modified (organized by subdirectory)
  - Reference count per file
  - Total references updated
  - Verification results (should be zero old-style references)
  - Summary statistics
- Exit with non-zero status if any problems occur

**WHY these requirements:**
- Recursive find ensures complete coverage of all subdirectories
- Progress indicators help track long-running operations
- Organized reporting makes it easy to verify completeness
- Exit codes enable integration into workflows
- Detailed statistics prove thorough execution
</output>

<verification>
After creating and executing the script, verify comprehensive coverage:

1. **Make executable and run:**
   ```bash
   chmod +x ./scripts/update-all-gh-projects-references.sh
   ./scripts/update-all-gh-projects-references.sh
   ```

2. **Verify all scripts have `.sh` extension:**
   ```bash
   ls -1 ~/.claude/skills/lib/gh-projects/ | grep -v -E '\.(sh|md)$' | grep -v '^(lib|templates)$'
   ```
   Expected: No output (all scripts have .sh extension)

3. **Recursively search for ANY old-style references:**
   ```bash
   find ~/.claude/skills -type f -name "*.md" -exec grep -l "gh-project-" {} + | xargs grep -n "gh-project-" | grep -v "\.sh" | grep -E "(gh-project-convert|gh-project-create|gh-project-delete|gh-project-init|gh-project-item-complete|gh-project-item-create|gh-project-item-get-acceptance-criteria|gh-project-item-start|gh-project-item-view|gh-project-link|gh-project-link-repo|gh-project-list|gh-project-setup-apply|gh-project-setup-clone|gh-project-setup-init|gh-project-update)([^a-z.-]|$)" || echo "✓ No old-style references found"
   ```
   Expected: "✓ No old-style references found"

4. **Count total markdown files processed:**
   ```bash
   find ~/.claude/skills -type f -name "*.md" | wc -l
   ```
   Expected: Should match the count in the script's report

5. **Verify scripts remain executable:**
   ```bash
   ls -l ~/.claude/skills/lib/gh-projects/*.sh | awk '{print $1}' | grep -v '^-rwx'
   ```
   Expected: No output (all have execute permission)

6. **Spot-check deeply nested files:**
   ```bash
   grep -r "gh-project" ~/.claude/skills/*/workflows/*.md | head -5
   grep -r "gh-project" ~/.claude/skills/*/references/*.md | head -5
   ```
   Expected: All references should include `.sh` extension

7. **Test renamed scripts still work:**
   ```bash
   ~/.claude/skills/lib/gh-projects/gh-project-list.sh --help 2>&1 | head -3
   ```
   Expected: Script executes without error
</verification>

<success_criteria>
✓ Shell script created at `./scripts/update-all-gh-projects-references.sh` and is executable
✓ ALL scripts in `~/.claude/skills/lib/gh-projects/` have `.sh` extension (verified)
✓ ALL markdown files in `~/.claude/skills/` tree processed recursively (no files missed)
✓ ALL references updated (including in deeply nested subdirectories like workflows/, references/, templates/)
✓ Scripts remain executable (permissions preserved)
✓ Surgical precision achieved (word boundaries prevent false matches)
✓ Deep recursive verification confirms ZERO old-style references remain anywhere
✓ Comprehensive report shows complete coverage with file-by-file statistics
✓ Spot-testing of nested directories confirms updates
</success_criteria>

<constraints>
- **DO NOT** modify files in `~/.claude/skills/lib/gh-projects/lib/` subdirectory - only rename files in the top-level gh-projects directory
- **DO NOT** rename directories, only files
- **DO NOT** skip any markdown files - must process ALL files recursively
- **DO NOT** modify binary files or non-.md files
- **DO NOT** break existing functionality - scripts must work identically after renaming
- **DO NOT** create false matches - use word boundaries to match complete script names only
- **DO NOT** lose executable permissions during rename operations
- **DO NOT** modify files outside `~/.claude/skills/` directory

**WHY these constraints:**
- The lib/ subdirectory may contain helper files with different naming conventions
- Directories maintain current names for path stability
- Recursive processing must be limited to .md files to avoid corrupting other file types
- Functionality preservation ensures no downstream breakage
- Word boundaries prevent corrupting text containing script name substrings
- Executable permissions are critical for scripts to function
- Scope limitation prevents unintended changes outside the skills directory
</constraints>

<examples>
**Example references that should be updated:**

In `~/.claude/skills/execute-epic/workflows/execute-epic.md`:
```markdown
Before: Run `gh-project-item-start` to begin
After:  Run `gh-project-item-start.sh` to begin
```

In `~/.claude/skills/execute-user-story/references/script-usage.md`:
```markdown
Before: Execute `~/.claude/skills/lib/gh-projects/gh-project-item-complete` when done
After:  Execute `~/.claude/skills/lib/gh-projects/gh-project-item-complete.sh` when done
```

In `~/.claude/skills/lib/gh-projects/README.md`:
```markdown
Before: The `gh-project-list` script shows all projects
After:  The `gh-project-list.sh` script shows all projects
```

**Non-matches (should NOT be updated):**
- `gh-project-management` (different word, not a script name)
- `gh-projects/` (directory reference)
- `gh-project-item-start.sh` (already correct)
</examples>
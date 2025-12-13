<objective>
Migrate GitHub Projects scripts to ~/.claude/ for global availability and update the github-project-setup skill to use these production-ready scripts instead of raw gh CLI commands.

This establishes a consistent, maintainable workflow where the skill leverages our battle-tested scripts with error handling, retry logic, and atomic operations.
</objective>

<context>
Current state:
- GitHub Projects scripts are in ./scripts/gh-projects/ (11 scripts + templates)
- github-project-setup skill is in ~/.claude/skills/github-project-setup/
- Skill uses raw gh CLI commands and GraphQL mutations
- Scripts are only available when working in this specific repository

Desired state:
- Scripts moved to ~/.claude/bin/gh-projects/ for global availability
- Skill updated to use scripts instead of raw commands
- All workflows updated to leverage script features (templates, atomic operations, error handling)
- Documentation updated in both locations

Why this matters:
- Scripts become available for all projects, not just this repository
- Skill becomes more robust by using production-tested scripts
- Maintenance is centralized in one place (the scripts)
- Users get consistent behavior across CLI usage and skill invocation
</context>

<requirements>
1. **Move scripts to ~/.claude/bin/gh-projects/**
   - Create ~/.claude/bin/gh-projects/ directory structure
   - Copy all scripts from ./scripts/gh-projects/ to ~/.claude/bin/gh-projects/
   - Preserve permissions (executable flags)
   - Include lib/ directory and templates/ directory
   - Verify all scripts work from new location

2. **Update github-project-setup skill**
   - Review ~/.claude/skills/github-project-setup/workflows/setup-github-project.md
   - Replace raw gh CLI commands with script calls
   - Update to use gh-project-setup-clone for project creation
   - Update to use gh-project-link-repo for repository linking
   - Update to use gh-project-create for issue creation
   - Leverage cpp-transpiler template from scripts

3. **Update documentation**
   - Update ./scripts/gh-projects/README.md to mention ~/.claude/bin/gh-projects/
   - Add migration notice and PATH setup instructions
   - Update skill's SKILL.md if needed
   - Create ~/.claude/bin/gh-projects/README.md explaining global availability

4. **Verify integration**
   - Test that scripts work from ~/.claude/bin/gh-projects/
   - Verify skill can invoke scripts correctly
   - Ensure templates are accessible
   - Check that error handling works as expected
</requirements>

<implementation>
## Step 1: Create directory structure in ~/.claude/

```bash
mkdir -p ~/.claude/bin/gh-projects/lib
mkdir -p ~/.claude/bin/gh-projects/templates
```

## Step 2: Copy scripts maintaining structure

```bash
# Copy all executable scripts
cp scripts/gh-projects/gh-project-* ~/.claude/bin/gh-projects/

# Copy lib directory
cp scripts/gh-projects/lib/gh-project-common.sh ~/.claude/bin/gh-projects/lib/

# Copy templates directory
cp scripts/gh-projects/templates/* ~/.claude/bin/gh-projects/templates/

# Verify permissions
chmod +x ~/.claude/bin/gh-projects/gh-project-*
```

## Step 3: Update skill workflows

Read and modify:
- ~/.claude/skills/github-project-setup/workflows/setup-github-project.md

Replace patterns like:
```bash
# OLD: Raw gh CLI
gh project create --owner {owner} --title "{title}"

# NEW: Use our script with template
gh-project-setup-clone --template cpp-transpiler --title "{title}"
```

Replace:
```bash
# OLD: Raw GraphQL mutation
gh api graphql -f query='mutation { linkProjectV2ToRepository ... }'

# NEW: Use our script
gh-project-link-repo --project {number}
```

Replace:
```bash
# OLD: Manual field creation
gh api graphql -f query='mutation { createProjectV2Field ... }'

# NEW: Template already has fields via gh-project-setup-clone
# No additional field creation needed
```

## Step 4: Update PATH instructions

Add to ./scripts/gh-projects/README.md:

```markdown
## Global Installation

Scripts are now installed globally at `~/.claude/bin/gh-projects/`

Add to your PATH:
```bash
export PATH="$PATH:$HOME/.claude/bin/gh-projects"
```

Add this line to your shell profile (~/.zshrc, ~/.bashrc, etc.)
```

## Step 5: Create global README

Create ~/.claude/bin/gh-projects/README.md explaining:
- What these scripts do
- How they're used by the github-project-setup skill
- PATH setup instructions
- Link back to main project documentation
</implementation>

<script_usage_patterns>
When updating the skill, use these patterns:

**Project Creation:**
```bash
# Use template-based cloning
gh-project-setup-clone \
  --template cpp-transpiler \
  --title "{project-name}"
```

**Repository Linking:**
```bash
# Simple auto-detection
gh-project-link-repo --project {number}
```

**Issue Creation:**
```bash
# Atomic draft→convert
gh-project-create \
  --title "{title}" \
  --type {epic|story|task} \
  --priority {priority}
```

**Epic-Story Linking:**
```bash
gh-project-link --parent {epic-num} --children {story1},{story2}
```

**Field Application:**
```bash
# If not using template
gh-project-setup-apply --template cpp-transpiler --project {number}
```
</script_usage_patterns>

<output>
Modified files:
1. ~/.claude/bin/gh-projects/* (newly created)
2. ~/.claude/skills/github-project-setup/workflows/setup-github-project.md (updated)
3. ./scripts/gh-projects/README.md (updated with migration notice)
4. ~/.claude/bin/gh-projects/README.md (newly created)

Verification commands to include in output:
```bash
# Verify scripts work globally
which gh-project-create
gh-project-setup-clone --help

# Verify templates accessible
ls ~/.claude/bin/gh-projects/templates/

# Test script execution
gh-project-create --title "Test" --type task --dry-run
```
</output>

<verification>
Before declaring complete, verify:

1. **Directory structure exists:**
   - [ ] ~/.claude/bin/gh-projects/ created
   - [ ] All 11 scripts copied
   - [ ] lib/ directory copied
   - [ ] templates/ directory copied with cpp-transpiler.json

2. **Scripts are executable:**
   - [ ] Run: `ls -l ~/.claude/bin/gh-projects/gh-project-*`
   - [ ] All should show -rwxr-xr-x permissions

3. **Scripts work from new location:**
   - [ ] Test: `~/.claude/bin/gh-projects/gh-project-create --help`
   - [ ] Should show usage without errors

4. **Skill updated correctly:**
   - [ ] Read updated workflow file
   - [ ] Verify no raw gh CLI commands remain (except basic checks)
   - [ ] Verify script calls are correct

5. **Documentation updated:**
   - [ ] README.md in both locations mention ~/.claude/bin/gh-projects/
   - [ ] PATH setup instructions included
</verification>

<success_criteria>
- All scripts successfully copied to ~/.claude/bin/gh-projects/ with correct permissions
- Skill workflow updated to use scripts instead of raw commands
- Templates directory accessible from new location
- Documentation updated in both ./scripts/ and ~/.claude/bin/ locations
- Verification tests pass showing scripts work globally
- No breaking changes to existing script functionality
</success_criteria>

<constraints>
- Do NOT modify script functionality, only their location
- Preserve all file permissions and structure
- Keep original scripts in ./scripts/gh-projects/ (don't delete) for version control
- Ensure skill can find scripts via PATH or absolute path
- Maintain backward compatibility - existing script users should not break
</constraints>

# GitHub Projects Management Scripts

Production-ready bash scripts for managing GitHub Projects v2 with **native sub-issue API support**.

## Global Installation Available

**These scripts are now available globally at `~/.claude/bin/gh-projects/`**

This makes them accessible from any project without needing to specify the full path.

### Using Global Scripts

Add to your PATH:
```bash
export PATH="$PATH:$HOME/.claude/bin/gh-projects"
```

Add this line to your shell profile (`~/.zshrc`, `~/.bashrc`, etc.) and reload:
```bash
source ~/.zshrc  # or source ~/.bashrc
```

### Integration with Claude Code Skills

These scripts are used by the `github-project-setup` skill:
- Skill location: `~/.claude/skills/github-project-setup/`
- The skill automatically uses these production-tested scripts for robust project setup

### Documentation

- **Global scripts README**: `~/.claude/bin/gh-projects/README.md`
- **Repository README**: This file (source of truth for script development)

---

## Features

✅ **Native Sub-Issue Support** - Uses GitHub's `addSubIssue`/`removeSubIssue` mutations for Epic-Story hierarchies
✅ **Atomic Draft→Convert** - Creates drafts, sets fields, converts to repo issues in single operation
✅ **Repository Issues by Default** - Matches GitHub UI behavior (Enter = issue, Cmd+Enter = draft)
✅ **Drafts Available** - Use `--draft` flag to skip conversion for brainstorming
✅ **Custom Fields** - Status, Type, Priority with automatic caching
✅ **Project Setup & Templating** - Export, clone, and replicate project structures
✅ **Production Quality** - Retry logic, error handling, dry-run mode
✅ **Developer Experience** - Color-coded output, progress indicators, comprehensive help

## Quick Start

### Installation

```bash
# Add scripts to PATH
export PATH="$PATH:/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/scripts/gh-projects"

# Or copy to ~/bin
cp scripts/gh-projects/gh-project-* ~/bin/
```

### Prerequisites

- [GitHub CLI](https://cli.github.com/) (`gh`) - authenticated
- [jq](https://stedolan.github.io/jq/) - JSON processor

### Initialize Configuration

```bash
# Auto-detect repository, specify project number
gh-project-init --project 14

# Or specify explicitly
gh-project-init --project 14 --owner o2alexanderfedin --repo cpp-to-c-transpiler

# Link project to repository (makes it appear in repo's Projects tab)
gh-project-link-repo --project 14

# Refresh field cache
gh-project-init --project 14 --refresh-cache
```

Configuration is saved to: `~/.config/gh-projects/config.json`

## Workflow Examples

### Creating an Epic with Stories

```bash
# Repository issues created atomically (draft→convert in single operation)

# 1. Create epic (GitHub assigns issue number, e.g., #41)
gh-project-create \
  --title "Epic: Virtual Functions + Vtables" \
  --type epic \
  --priority High
# Output: Issue: #41

# 2. Create stories (GitHub assigns numbers, e.g., #167, #168)
gh-project-create \
  --title "Story: Virtual Method Detection" \
  --type story \
  --status Todo
# Output: Issue: #167

gh-project-create \
  --title "Story: Vtable Struct Generation" \
  --type story \
  --status Todo
# Output: Issue: #168

# 3. Link stories to epic using native GitHub sub-issue API
#    (use the issue numbers that were output above)
gh-project-link --parent 41 --children 167,168

# Behind the scenes, each gh-project-create:
#   1. Creates draft (fast)
#   2. Sets custom fields
#   3. Converts to repository issue (atomic)
#   4. GitHub assigns the issue number
```

### Working with Drafts

Drafts are lightweight, project-only items for brainstorming. Use the `--draft` flag:

```bash
# Create draft for quick ideation (use --draft flag)
gh-project-create \
  --title "Draft: Research RTTI implementation" \
  --type spike \
  --draft

# List all drafts
gh-project-list --drafts-only

# Convert draft to repo issue when ready for collaboration
gh-project-convert --title "Research RTTI implementation"
```

### Querying and Filtering

```bash
# List all epics
gh-project-list --type epic

# List in-progress stories
gh-project-list --type story --status "In Progress"

# Show sub-issues of Epic #42
gh-project-list --parent 42

# Export to CSV
gh-project-list --format csv > items.csv
```

### Updating Items

```bash
# Mark story as done
gh-project-update --issue 167 --status Done

# Update priority
gh-project-update --issue 42 --priority Critical

# Multiple fields
gh-project-update --issue 167 --status "In Progress" --priority High
```

### Removing Items

```bash
# Remove repository issue from project
gh-project-delete --issue 167

# Delete draft permanently
gh-project-delete --item PVTI_...

# Archive (close + remove from project)
gh-project-delete --issue 167 --archive --yes
```

### Project Setup and Templating

Create standardized project structures, clone complete projects, or apply field configurations to existing projects.

#### Available Templates

**Repository Templates** (version-controlled, available to all users):
- `cpp-transpiler` - C++ to C Transpiler project structure (9 fields, 3 views)

**User Templates** (local customizations):
- Stored in `~/.config/gh-projects/templates/`
- Created via `gh-project-setup-init`

Templates are searched in order: repository templates first, then user templates.

#### Quick Start

```bash
# Clone complete project from built-in template
gh-project-setup-clone \
  --template cpp-transpiler \
  --title "My New Transpiler Project"

# Apply fields only to existing project
gh-project-setup-apply \
  --template cpp-transpiler \
  --project 15

# Export your own template
gh-project-setup-init --project 14 --owner o2alexanderfedin
```

**When to use each approach:**

- **gh-project-setup-clone** (Recommended)
  - Creates complete project clone including views, workflows, and fields
  - Uses GitHub's native `copyProjectV2` mutation
  - Best for: Creating new projects with identical structure
  - ✅ Includes views (Kanban, Table, Roadmap)
  - ✅ Includes automation workflows
  - ⚠️ Requires source project access

- **gh-project-setup-apply**
  - Applies field structure only to existing project
  - Views must be created manually in GitHub UI
  - Best for: Adding standardized fields to existing projects
  - ✅ Works on existing projects
  - ✅ Non-destructive (skips existing fields)
  - ⚠️ Views not included (API limitation)

**Important Limitation:**
GitHub's GraphQL API does not support programmatic view creation. Use `copyProjectV2` (via `gh-project-setup-clone`) for complete project replication including views, or create views manually in the UI.

## Scripts Reference

### gh-project-init

Initialize configuration and cache field metadata.

**Usage:**
```bash
gh-project-init --project NUM [--owner OWNER] [--repo REPO] [--refresh-cache]
```

**Options:**
- `--project NUM` - Project number (required)
- `--owner OWNER` - Repository owner (default: auto-detect)
- `--repo REPO` - Repository name (default: auto-detect)
- `--refresh-cache` - Force refresh field cache
- `-h, --help` - Show help

### gh-project-create

Create repository issue in project with custom fields using **atomic draft→convert workflow**.

**Atomic Operation:**
1. Creates draft issue (fast, simple)
2. Sets custom fields
3. Converts to repository issue (unless `--draft` flag)

This ensures consistency and matches GitHub UI behavior.

**Usage:**
```bash
gh-project-create --title TEXT [OPTIONS]
```

**Options:**
- `--title TEXT` - Issue title (required)
- `--body TEXT` - Issue body (optional)
- `--type TYPE` - Issue type: epic, story, task, bug, spike (default: story)
- `--status STATUS` - Status: Todo, "In Progress", Done (default: Todo)
- `--priority PRIORITY` - Priority: Critical, High, Medium, Low (optional)
- `--draft` - Keep as draft (skip conversion to repository issue)
- `--dry-run` - Show what would be created
- `-h, --help` - Show help

### gh-project-convert

Convert draft issue to repository issue (IRREVERSIBLE).

**Usage:**
```bash
gh-project-convert --item ID [--yes] [--dry-run]
```

**Options:**
- `--item ID` - Project item ID (PVTI_...)
- `--title TEXT` - Filter by title match
- `--yes, -y` - Skip confirmation
- `--dry-run` - Show what would be converted
- `-h, --help` - Show help

**Warning:** This operation is IRREVERSIBLE!

### gh-project-link

Link story to epic using GitHub's native sub-issue API.

**Usage:**
```bash
gh-project-link --parent NUM --child NUM [OPTIONS]
```

**Options:**
- `--parent NUM` - Parent issue number (epic)
- `--child NUM` - Child issue number (story)
- `--children NUM,NUM` - Multiple children (comma-separated)
- `--dry-run` - Show what would be linked
- `-h, --help` - Show help

**Requirements:**
- Both parent and child must be repository issues (not drafts)
- Both must be in the same repository

### gh-project-link-repo

Link a GitHub Project to a repository so it appears in the repository's Projects tab.

**Usage:**
```bash
gh-project-link-repo --project NUM [OPTIONS]
```

**Options:**
- `--project NUM` - Project number (required)
- `--owner OWNER` - Project owner (default: from config or auto-detect)
- `--repo REPO` - Repository name (default: from config or auto-detect)
- `--repo-owner OWNER` - Repository owner if different from project owner
- `--unlink` - Unlink project from repository instead of linking
- `--dry-run` - Show what would be done
- `-h, --help` - Show help

**What this does:**
- Makes the project appear in the repository's "Projects" tab
- Allows easy addition of repository issues to the project
- Links the project and repository in GitHub's UI

**Examples:**
```bash
# Link project to current repository
gh-project-link-repo --project 14

# Link to specific repository
gh-project-link-repo --project 14 --repo my-repo

# Unlink project from repository
gh-project-link-repo --project 14 --unlink
```

### gh-project-list

Query and filter project items with advanced filtering.

**Usage:**
```bash
gh-project-list [OPTIONS]
```

**Options:**
- `--status STATUS` - Filter by status
- `--type TYPE` - Filter by type (epic, story, task, bug, spike)
- `--drafts-only` - Show only draft issues
- `--repo-only` - Show only repository issues
- `--parent NUM` - Show sub-issues of parent epic
- `--format FORMAT` - Output format: table, json, csv (default: table)
- `--limit NUM` - Limit results (default: 200)
- `-h, --help` - Show help

### gh-project-update

Update draft/repo issue custom fields.

**Usage:**
```bash
gh-project-update [--item ID | --issue NUM] [OPTIONS]
```

**Options:**
- `--item ID` - Project item ID
- `--issue NUM` - Repository issue number (auto-find in project)
- `--status STATUS` - Update status
- `--priority PRIORITY` - Update priority
- `--type TYPE` - Update type
- `--dry-run` - Preview changes
- `-h, --help` - Show help

### gh-project-delete

Delete draft or remove repository issue from project.

**Usage:**
```bash
gh-project-delete [--item ID | --issue NUM] [OPTIONS]
```

**Options:**
- `--item ID` - Project item ID
- `--issue NUM` - Repository issue number
- `--archive` - Archive instead of delete (repo issues only)
- `--yes, -y` - Skip confirmation
- `-h, --help` - Show help

**Warning:**
- Deleting drafts is PERMANENT
- Removing repo issues only removes from project (issue preserved in repo)
- Archive closes the issue AND removes from project

### gh-project-setup-init

Export GitHub Project structure as a reusable template.

**Usage:**
```bash
gh-project-setup-init [--project NUM] [--owner OWNER] [OPTIONS]
```

**Options:**
- `--project NUM` - Project number (default: from config)
- `--owner OWNER` - Project owner (default: from config)
- `--name NAME` - Template name (default: project-{number})
- `--output PATH` - Output file path (default: ~/.config/gh-projects/templates/{name}.json)
- `--dry-run` - Show what would be exported
- `-h, --help` - Show help

**Template Contents:**
- Project metadata (title, description, readme)
- Custom fields with definitions and options
- View configurations (metadata only - views cannot be created via API)
- Field mappings for data types

**Template Locations:**
- Repository templates: `scripts/gh-projects/templates/` (version-controlled)
- User templates: `~/.config/gh-projects/templates/` (local customizations)

Templates are searched in order: repository templates first, then user templates.

### gh-project-setup-clone

Clone complete GitHub Project using GitHub's native `copyProjectV2` mutation.

**Usage:**
```bash
gh-project-setup-clone --template NAME --title TEXT [OPTIONS]
```

**Options:**
- `--source-project NUM` - Source project number (required if no template)
- `--source-owner OWNER` - Source project owner (required if no template)
- `--template NAME` - Use cached template (alternative to source-project)
- `--title TEXT` - New project title (required)
- `--target-owner OWNER` - Target owner (user/org, default: authenticated user)
- `--include-drafts` - Include draft issues (default: false)
- `--dry-run` - Show what would be cloned
- `-h, --help` - Show help

**What Gets Cloned:**
- ✅ All custom fields (definitions + options)
- ✅ All views (Table, Kanban, Roadmap) with filters and sorting
- ✅ All automation workflows
- ✅ Draft issues (if `--include-drafts` flag used)
- ❌ Repository issues (not cloned)

**Note:** This is the only way to programmatically create views. The `copyProjectV2` mutation is GitHub's native cloning mechanism.

### gh-project-setup-apply

Apply custom field structure from template to existing project.

**Usage:**
```bash
gh-project-setup-apply --template NAME --project NUM [OPTIONS]
```

**Options:**
- `--template NAME` - Template name (required)
- `--project NUM` - Target project number (required)
- `--owner OWNER` - Target project owner (default: from config)
- `--update-existing` - Update existing fields (default: skip)
- `--dry-run` - Show what would be applied
- `-h, --help` - Show help

**Supported Field Types:**
- TEXT - Single-line text fields
- NUMBER - Numeric fields
- DATE - Date fields
- SINGLE_SELECT - Dropdown fields with options
- ITERATION - Iteration fields

**Note:** This script only creates/updates fields. Views must be created manually in GitHub UI or via `gh-project-setup-clone`.

## Architecture

### Directory Structure

```
scripts/gh-projects/
├── lib/
│   └── gh-project-common.sh        # Shared functions
├── gh-project-init                  # Initialize config + cache
├── gh-project-create                # Create draft/repo issues
├── gh-project-convert               # Convert draft → repo
├── gh-project-link                  # Link story to epic (native sub-issue)
├── gh-project-link-repo             # Link project to repository
├── gh-project-list                  # Query/filter items
├── gh-project-update                # Update custom fields
├── gh-project-delete                # Delete/remove items
├── gh-project-setup-init            # Export project as template
├── gh-project-setup-clone           # Clone complete project (copyProjectV2)
└── gh-project-setup-apply           # Apply fields from template

~/.config/gh-projects/
├── config.json                      # Configuration + cache
└── templates/                       # User templates (local customizations)
    └── project-14.json              # Example: exported project structure
```

**Built-in Templates:**
- `cpp-transpiler` - Version-controlled template in `scripts/gh-projects/templates/`
- Ready to use without exporting from project #14
- Available to all users of the repository

### Configuration File

`~/.config/gh-projects/config.json`:
```json
{
  "owner": "o2alexanderfedin",
  "repo": "cpp-to-c-transpiler",
  "project_number": 14,
  "project_id": "PVT_kwDOQku...",
  "cache_timestamp": "2025-12-09T21:00:00Z",
  "cache_version": "2.0",
  "field_cache": {
    "Status": {
      "id": "PVTSSF_...",
      "type": "ProjectV2SingleSelectField",
      "options": [
        {"id": "f75ad846", "name": "Todo"},
        {"id": "47fc9ee4", "name": "In Progress"},
        {"id": "98ec2077", "name": "Done"}
      ]
    },
    "Type": {
      "id": "PVTSSF_...",
      "type": "ProjectV2SingleSelectField",
      "options": [
        {"id": "fca9429d", "name": "Epic"},
        {"id": "839ffda1", "name": "User Story"},
        {"id": "7a520867", "name": "Task"}
      ]
    }
  }
}
```

### Shared Library

`lib/gh-project-common.sh` provides:

- **Logging**: Color-coded output (success/error/warn/info)
- **Error Handling**: Retry with exponential backoff
- **GraphQL Operations**: Execute queries/mutations with retry
- **Sub-Issue API**: Native `addSubIssue`/`removeSubIssue` operations with `GraphQL-Features:sub_issues` header
- **Field Caching**: Cache field IDs/option IDs for performance
- **ID Resolution**: Convert issue numbers to GraphQL IDs
- **Validation**: Check prerequisites (gh, jq, auth)
- **Dry-Run**: Preview mode for all mutations

## Native Sub-Issue API

### How It Works

GitHub's native sub-issue API uses GraphQL mutations with a special header:

```bash
gh api graphql \
  -H "GraphQL-Features:sub_issues" \
  -f query='
    mutation($parentId: ID!, $childId: ID!) {
      addSubIssue(input: {
        issueId: $parentId
        subIssueId: $childId
      }) {
        issue {
          trackedIssues { totalCount }
        }
      }
    }
  ' \
  -f parentId="$EPIC_ID" \
  -f childId="$STORY_ID"
```

### Benefits Over Custom Fields

✅ **UI Integration** - Sub-issues appear in GitHub's issue detail page
✅ **Progress Tracking** - Automatic "X of Y tasks complete" display
✅ **Bi-directional Queries** - Query parent from child, children from parent
✅ **Ecosystem Support** - Works with Actions, webhooks, API integrations
✅ **Type Safety** - Uses IDs, prevents invalid links

### Requirements

- Both parent and child must be **repository issues** (not drafts)
- Both must be in the **same repository**
- Requires `GraphQL-Features:sub_issues` header (handled automatically by scripts)

**Note:** Since scripts create repository issues by default, you can use sub-issue linking immediately without conversion!

## Troubleshooting

### Configuration not initialized

**Error:** `Configuration not initialized. Run: gh-project-init --project NUM`

**Solution:**
```bash
gh-project-init --project 14
```

### Field not found

**Error:** `Field 'Status' not found. Run: gh-project-init --refresh-cache`

**Solution:**
```bash
gh-project-init --project 14 --refresh-cache
```

### Cannot link draft to epic

**Error:** `Epic #42 not found or not a repository issue`

**Solution:** Convert draft to repository issue first:
```bash
gh-project-convert --item PVTI_...
```

### Sub-issue not showing in UI

**Possible causes:**
- One or both issues are drafts (must be repository issues)
- Issues are in different repositories
- Insufficient permissions
- GraphQL-Features header not sent (should be automatic)

**Verify:**
```bash
# Check if both are repository issues
gh-project-list --parent 42
```

### gh CLI not authenticated

**Error:** `Not authenticated. Run: gh auth login`

**Solution:**
```bash
gh auth login
```

### Rate limiting

Scripts automatically retry with exponential backoff (2s, 4s, 8s).

If rate limited repeatedly:
- Wait 60 seconds
- Use `--dry-run` to preview operations first
- Reduce bulk operation size

## Advanced Usage

### Bulk Operations

```bash
# Link multiple stories to epic
gh-project-link --parent 42 --children 167,168,169,170,171

# Update status for multiple items (manual loop)
for issue in 167 168 169; do
  gh-project-update --issue $issue --status Done
done
```

### Custom Queries

```bash
# Count items by status
gh-project-list --format json | \
  jq 'group_by(.Status) | map({status: .[0].Status, count: length})'

# Find items without priority
gh-project-list --format json | \
  jq '.[] | select(.Priority == null or .Priority == "")'

# Export epics with sub-issue count
for epic in $(gh-project-list --type epic --format json | jq -r '.[].content.number'); do
  echo "Epic #$epic:"
  gh-project-list --parent $epic --format table
done
```

### Integration with Git Flow

```bash
# Create story for current feature (repository issue by default)
BRANCH=$(git branch --show-current)
STORY_TITLE="Story: ${BRANCH#feature/}"

gh-project-create \
  --title "$STORY_TITLE" \
  --type story \
  --status "In Progress"
```

## Implementation Details

### Field Caching

Field metadata is cached on first `gh-project-init` to avoid repeated GraphQL queries:

- **Cache location**: `~/.config/gh-projects/config.json`
- **Cache lifetime**: 7 days (or manual refresh)
- **What's cached**: Field IDs, option IDs for all single-select fields

### Error Handling

All scripts include:

- **Retry logic**: 3 attempts with exponential backoff (2s, 4s, 8s)
- **Rate limiting**: Automatic wait and retry
- **Validation**: Check prerequisites before operations
- **Graceful degradation**: Clear error messages with suggested fixes

### Dry-Run Mode

All mutation operations support `--dry-run`:

```bash
# Preview without executing
gh-project-create --title "Test" --dry-run
gh-project-link --parent 42 --child 167 --dry-run
gh-project-convert --item PVTI_... --dry-run
```

## Migration Guide

### From Custom Fields to Native Sub-Issues

If you previously used custom "Parent Epic" field:

1. **Identify Epic-Story pairs:**
```bash
gh-project-list --format json > items.json
# Parse items.json to find custom field relationships
```

2. **Ensure all are repository issues:**
```bash
# Convert any drafts
gh-project-convert --title "Epic #42"
```

3. **Create native links:**
```bash
gh-project-link --parent 42 --children 167,168,169
```

4. **Verify in GitHub UI:**
   - Open Epic #42
   - Scroll to "Sub-issues" section
   - Confirm stories appear with progress tracking

### Adopting the Scripts

**Current State**: May have mixed repo issues, drafts, and duplicates

**Migration Steps**:
1. **Initialize Configuration**:
   ```bash
   gh-project-init --project 14
   ```

2. **Audit Existing Items**:
   ```bash
   gh-project-list --format json > items.json
   # Review: Which are drafts? Which are repo issues?
   ```

3. **Standardize Workflow**:
   - **Going forward**: Scripts create repository issues by default (matching GitHub UI)
   - **Use `--draft` flag**: For lightweight brainstorming only
   - **Link epics/stories**: Use `gh-project-link` for native sub-issue hierarchy

4. **Formalize Existing Hierarchies**:
   ```bash
   # Link existing epics and stories using native API
   gh-project-link --parent 41 --children 167,168,169
   ```

5. **Document**: Update team workflow to use scripts consistently

## Contributing

### Testing New Scripts

```bash
# Use dry-run for all new operations
./gh-project-create --title "Test" --dry-run

# Test against dedicated test project first
gh-project-init --project <test-project-number>
```

### Adding New Features

1. Add shared functions to `lib/gh-project-common.sh`
2. Follow naming convention: `gh-project-{action}`
3. Include `--dry-run` and `--help` support
4. Use color-coded logging
5. Handle errors gracefully

## References

- [GitHub GraphQL API - addSubIssue](https://docs.github.com/en/graphql/reference/mutations#addsubissue)
- [GitHub Projects v2 Documentation](https://docs.github.com/en/issues/planning-and-tracking-with-projects)
- [GitHub CLI Manual](https://cli.github.com/manual/)
- [jq Manual](https://stedolan.github.io/jq/manual/)

## License

Part of the hupyy-cpp-to-c transpiler project.

## Version

v2.0 - Native sub-issue API support (2025-12-09)

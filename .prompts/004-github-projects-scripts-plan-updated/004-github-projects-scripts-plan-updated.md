# GitHub Projects Management Scripts - Updated Implementation Plan

## Objective

Create a detailed implementation plan for robust bash scripts that manage GitHub Projects v2 issues using **CORRECTED research** that includes native sub-issue API support.

**Goal**: Production-ready shell scripts leveraging:
1. ✅ Native `addSubIssue`/`removeSubIssue`/`reprioritizeSubIssue` mutations (NOT custom fields)
2. ✅ Draft-first workflow for planning (convert to repo issues for sub-issue linking)
3. ✅ GraphQL-Features header support for sub-issue operations
4. ✅ Custom fields for project metadata (Status, Priority, Type)
5. ✅ Excellent UX (dry-run, colors, progress, confirmations)

**Why This Matters**: The original plan would have used custom field workarounds. The corrected research reveals native GitHub sub-issue API exists, completely changing implementation approach for Epic-Story hierarchies.

## Context

**Corrected Research Foundation**:
```
@.prompts/001-github-projects-management-research/github-projects-management-research.md (v1.1)
@.prompts/003-github-projects-research-refine/github-projects-research-refined.md
```

**CRITICAL CHANGE from Original Plan**:
- ❌ OLD: Use custom "Parent Epic" text field for hierarchy
- ✅ NEW: Use native `addSubIssue` mutation for Epic-Story linking

**Key Research Findings (v1.1)**:
1. **Native Sub-Issue API**: `addSubIssue`, `removeSubIssue`, `reprioritizeSubIssue` mutations exist
2. **GraphQL-Features Header Required**: `-H "GraphQL-Features:sub_issues"` for all operations
3. **Draft Issues Cannot Be Sub-Issues**: Must convert draft → repo issue for sub-issue linking
4. **Bi-Directional Queries**: Query parent from child (`parent` field), children from parent (`trackedIssues`)
5. **UI Integration**: Sub-issues display in GitHub UI with progress tracking
6. **Dual-ID System**: Draft editing requires DI_* content ID, custom fields use PVTI_* project item ID
7. **Custom Fields**: Project-level metadata (Status, Priority, Type) preserved during conversion

**Target Workflow** (Updated):
1. Create draft epic in project
2. Create draft stories in project
3. Set custom fields (Status=Todo, Type=Epic/Story, Priority, etc.)
4. Convert epic to repository issue (for sub-issue capability)
5. Convert stories to repository issues
6. Link stories to epic using `addSubIssue` mutation
7. Result: Native GitHub hierarchy with UI integration + project custom fields

**Constraints**:
- Bash scripts (not Python) for simplicity
- Use `gh` CLI + GraphQL where CLI insufficient
- Support macOS/Linux (portable bash)
- No external dependencies beyond gh, jq, curl
- Must handle GraphQL-Features header requirement
- Graceful error handling with clear messages

## Requirements

### Planning Scope

**Phase 1: Script Architecture**

1. **File Organization**:
   - **Recommendation**: Modular approach with 7 core scripts + 1 shared library
   - **Location**: `scripts/gh-projects/` directory
   - **Naming**: `gh-project-{action}` pattern (e.g., `gh-project-create`, `gh-project-link`)
   - **Installation**: Copy to `~/bin/` or add to PATH
   - **Config**: `~/.config/gh-projects/config.json` with project metadata

2. **Core Functions Library** (`lib/gh-project-common.sh`):
   - Error handling (retry with backoff, clear error messages)
   - Logging (color-coded: green=success, red=error, yellow=warning, blue=info)
   - GraphQL helpers (execute_graphql with header support)
   - Field ID resolution and caching
   - JSON parsing helpers (jq wrappers)
   - Draft-to-repo conversion workflow
   - Sub-issue operations (add/remove/query with GraphQL-Features header)

3. **Configuration Management**:
   - **Format**: JSON for structured data
   - **Location**: `~/.config/gh-projects/config.json`
   - **Contents**:
     ```json
     {
       "owner": "o2alexanderfedin",
       "repo": "cpp-to-c-transpiler",
       "project_number": 14,
       "field_cache": {
         "Status": {"id": "PVTSSF_...", "options": {...}},
         "Type": {"id": "PVTSSF_...", "options": {...}},
         "Priority": {"id": "PVTSSF_...", "options": {...}}
       },
       "cache_timestamp": "2025-12-09T21:00:00Z"
     }
     ```
   - **Auto-detection**: `gh repo view --json owner,name` for current repo
   - **Validation**: Check project exists, has required fields

**Phase 2: Script Specifications**

### Script 1: `gh-project-init`

**Purpose**: Initialize configuration, cache field metadata, validate setup

**Interface**:
```bash
gh-project-init [OPTIONS]

Options:
  --project NUM        Project number (required)
  --owner OWNER        Repository owner (default: auto-detect)
  --repo REPO          Repository name (default: auto-detect)
  --refresh-cache      Force refresh field cache
  -h, --help           Show help
```

**Behavior**:
1. Detect or accept owner/repo/project number
2. Validate project exists and is accessible
3. Query all custom fields with `gh project field-list`
4. Cache field IDs and option IDs to config file
5. Display configuration summary

**Examples**:
```bash
# Initialize for project #14 (auto-detect repo)
gh-project-init --project 14

# Initialize with explicit repo
gh-project-init --project 14 --owner myorg --repo myrepo

# Refresh cached field metadata
gh-project-init --project 14 --refresh-cache
```

**Error Handling**:
- Project doesn't exist → "Project #14 not found. Check project number and permissions."
- No write access → "Insufficient permissions. Requires project write access."
- gh CLI not authenticated → "Run: gh auth login"

---

### Script 2: `gh-project-create`

**Purpose**: Create draft or repository issue in project with custom fields

**Interface**:
```bash
gh-project-create [OPTIONS]

Options:
  --title TEXT         Issue title (required)
  --body TEXT          Issue body (optional)
  --type TYPE          Issue type: epic, story, task (default: story)
  --status STATUS      Status: Todo, In Progress, Done (default: Todo)
  --priority NUM       Priority: 1-5 (optional)
  --draft              Create as draft (default: true)
  --repo-issue         Create as repository issue directly
  --dry-run            Show what would be created without creating
  -h, --help           Show help
```

**Behavior**:
1. Load config, validate required fields exist
2. Create draft issue via `gh project item-create --format json`
3. Set custom fields (Type, Status, Priority) using field/option IDs
4. If `--repo-issue`: Convert draft → repo issue immediately
5. Output: Item ID, title, URL

**Examples**:
```bash
# Create draft epic
gh-project-create --title "Epic #42: Advanced Features" --type epic

# Create story in repo (for immediate sub-issue linking)
gh-project-create \
  --title "Story: Implement RTTI" \
  --type story \
  --status "In Progress" \
  --repo-issue

# Dry-run to preview
gh-project-create --title "Test" --dry-run
```

**Error Handling**:
- Missing title → "Error: --title required"
- Invalid type → "Error: --type must be epic, story, or task"
- Field doesn't exist → "Error: 'Type' field not found. Run: gh-project-init --refresh-cache"
- Rate limit → Retry with exponential backoff (1s, 2s, 4s)

---

### Script 3: `gh-project-link`

**Purpose**: Link story to epic using native `addSubIssue` mutation

**Interface**:
```bash
gh-project-link [OPTIONS]

Options:
  --parent NUM         Parent issue number (epic)
  --child NUM          Child issue number (story)
  --children NUM,NUM   Multiple children (comma-separated)
  --dry-run            Show what would be linked
  -h, --help           Show help
```

**Behavior**:
1. Validate both parent and child exist as **repository issues** (not drafts)
2. Get issue IDs: `gh issue view NUM --json id`
3. Execute `addSubIssue` mutation with `GraphQL-Features:sub_issues` header
4. Verify link created by querying `trackedIssues`
5. Output: Confirmation with progress (e.g., "Epic #42 now tracks 3 of 9 stories")

**Examples**:
```bash
# Link single story to epic
gh-project-link --parent 42 --child 167

# Link multiple stories
gh-project-link --parent 42 --children 167,168,169

# Preview without linking
gh-project-link --parent 42 --child 167 --dry-run
```

**Error Handling**:
- Parent is draft → "Error: Epic #42 is a draft. Convert to repo issue first: gh-project-convert 42"
- Child is draft → "Error: Story #167 is a draft. Convert to repo issue first."
- Already linked → Warning: "Story #167 already linked to Epic #42. Skipping."
- Permission denied → "Error: Insufficient permissions for issue linking"

---

### Script 4: `gh-project-convert`

**Purpose**: Convert draft issue to repository issue (irreversible, with confirmation)

**Interface**:
```bash
gh-project-convert [OPTIONS]

Options:
  --item ID            Project item ID (PVTI_...)
  --title TEXT         Filter by title match
  --yes, -y            Skip confirmation
  --dry-run            Show what would be converted
  -h, --help           Show help
```

**Behavior**:
1. Get draft content ID (DI_*) via GraphQL query
2. Show preview: title, current custom fields, "This is IRREVERSIBLE"
3. Confirm with user (unless `--yes`)
4. Execute `convertProjectV2DraftIssueItemToIssue` mutation
5. Verify conversion, get new repository issue number
6. Output: "Converted draft → Issue #177. URL: https://..."

**Examples**:
```bash
# Convert specific draft
gh-project-convert --item PVTI_lADOQku...

# Convert by title (interactive selection)
gh-project-convert --title "Epic #42"

# Batch convert (skip confirmation)
gh-project-convert --item PVTI_... --yes
```

**Error Handling**:
- Item not found → "Error: Item PVTI_... not found in project"
- Already repo issue → "Error: Item is already a repository issue (#177)"
- User cancels → "Conversion cancelled"
- Conversion fails → "Error: Conversion failed. Draft preserved."

---

### Script 5: `gh-project-list`

**Purpose**: Query and filter project items with advanced jq patterns

**Interface**:
```bash
gh-project-list [OPTIONS]

Options:
  --status STATUS      Filter by status
  --type TYPE          Filter by type (epic, story, task)
  --drafts-only        Show only draft issues
  --repo-only          Show only repository issues
  --parent NUM         Show sub-issues of parent epic
  --format FORMAT      Output format: table, json, csv (default: table)
  --limit NUM          Limit results (default: 100)
  -h, --help           Show help
```

**Behavior**:
1. Fetch items: `gh project item-list --format json --limit NUM`
2. Apply jq filters based on options
3. Format output (table with columns, JSON, or CSV)
4. For `--parent`: Query epic's `trackedIssues` separately

**Examples**:
```bash
# List all epics
gh-project-list --type epic

# List in-progress stories
gh-project-list --type story --status "In Progress"

# List drafts only
gh-project-list --drafts-only

# Show stories under epic #42
gh-project-list --parent 42

# Export to CSV
gh-project-list --format csv > items.csv
```

**Error Handling**:
- Invalid filter → "Error: Unknown status 'Doing'. Valid: Todo, In Progress, Done"
- Parent not found → "Error: Epic #42 not found"
- No results → "No items match filters"

---

### Script 6: `gh-project-update`

**Purpose**: Update draft/repo issue custom fields

**Interface**:
```bash
gh-project-update [OPTIONS]

Options:
  --item ID            Project item ID
  --issue NUM          Repository issue number (auto-find in project)
  --status STATUS      Update status
  --priority NUM       Update priority
  --type TYPE          Update type
  --dry-run            Preview changes
  -h, --help           Show help
```

**Behavior**:
1. If `--issue`: Find project item ID from issue number
2. Get current field values
3. Update specified fields using `gh project item-edit`
4. Verify updates, show diff

**Examples**:
```bash
# Update story status
gh-project-update --issue 167 --status "Done"

# Update epic priority
gh-project-update --issue 42 --priority 1

# Multiple fields
gh-project-update --issue 167 --status "In Progress" --priority 2
```

**Error Handling**:
- Issue not in project → "Error: Issue #167 not found in project"
- Invalid field value → "Error: Invalid status 'Complete'. Valid: Todo, In Progress, Done"

---

### Script 7: `gh-project-delete`

**Purpose**: Delete draft or remove repository issue from project

**Interface**:
```bash
gh-project-delete [OPTIONS]

Options:
  --item ID            Project item ID
  --issue NUM          Repository issue number
  --archive            Archive instead of delete (repo issues only)
  --yes, -y            Skip confirmation
  -h, --help           Show help
```

**Behavior**:
1. Get item details
2. Confirm deletion (show title, type, "This is permanent for drafts")
3. For drafts: Delete via `gh project item-delete`
4. For repo issues: Remove from project (issue preserved in repo)
5. If `--archive`: Close issue + remove from project

**Examples**:
```bash
# Delete draft
gh-project-delete --item PVTI_...

# Remove repo issue from project
gh-project-delete --issue 167

# Archive (close + remove)
gh-project-delete --issue 167 --archive --yes
```

**Error Handling**:
- Item not found → "Error: Item not found"
- User cancels → "Deletion cancelled"

---

**Phase 3: Implementation Details**

### Caching Strategy

**What to Cache**:
- Project ID (number → GraphQL ID)
- Field IDs: Status, Priority, Type, Effort, etc.
- Option IDs for single-select fields
- Owner/repo metadata

**Cache File Format** (`~/.config/gh-projects/config.json`):
```json
{
  "owner": "o2alexanderfedin",
  "repo": "cpp-to-c-transpiler",
  "project_number": 14,
  "project_id": "PVT_kwDOQku...",
  "field_cache": {
    "Status": {
      "id": "PVTSSF_lADOQku...",
      "type": "single_select",
      "options": {
        "Todo": "f75ad846",
        "In Progress": "47fc9ee4",
        "Done": "98ec2077"
      }
    },
    "Type": {
      "id": "PVTSSF_lADOQku...",
      "type": "single_select",
      "options": {
        "Epic": "epic_id",
        "Story": "story_id",
        "Task": "task_id"
      }
    }
  },
  "cache_timestamp": "2025-12-09T21:00:00Z",
  "cache_version": "1.0"
}
```

**Cache Invalidation**:
- Manual: `gh-project-init --refresh-cache`
- Auto: If cache > 7 days old
- On error: "Field not found" triggers refresh suggestion

**Cache Corruption Handling**:
- Invalid JSON → Delete and regenerate
- Missing required fields → Regenerate
- Backup old cache to `config.json.bak`

### Error Handling Patterns

**Network Failures**:
```bash
execute_graphql_with_retry() {
  local max_attempts=3
  local attempt=1
  local delay=1

  while [ $attempt -le $max_attempts ]; do
    if gh api graphql "$@"; then
      return 0
    fi

    log_warn "Attempt $attempt failed. Retrying in ${delay}s..."
    sleep $delay
    delay=$((delay * 2))
    attempt=$((attempt + 1))
  done

  log_error "GraphQL request failed after $max_attempts attempts"
  return 1
}
```

**GraphQL-Features Header Support**:
```bash
execute_sub_issue_mutation() {
  gh api graphql \
    -H "GraphQL-Features:sub_issues" \
    -f query="$1" \
    "${@:2}"
}
```

**Graceful Degradation**:
- If sub-issue mutation fails → Suggest custom field alternative
- If field cache stale → Warn but continue with best effort
- If rate limited → Display wait time, offer to retry

### User Experience

**Dry-Run Mode**:
```bash
if [ "$DRY_RUN" = true ]; then
  log_info "[DRY-RUN] Would create draft issue:"
  log_info "  Title: $TITLE"
  log_info "  Type: $TYPE"
  log_info "  Status: $STATUS"
  exit 0
fi
```

**Color Output**:
```bash
# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

log_success() { echo -e "${GREEN}✓${NC} $1"; }
log_error() { echo -e "${RED}✗${NC} $1" >&2; }
log_warn() { echo -e "${YELLOW}⚠${NC} $1"; }
log_info() { echo -e "${BLUE}ℹ${NC} $1"; }
```

**Progress Indicators**:
```bash
# For bulk operations
total=9
for i in {1..9}; do
  log_info "Processing story $i of $total..."
  # ... work ...
  echo -ne "Progress: [$i/$total]\r"
done
echo ""
```

**Confirmation Prompts**:
```bash
confirm_conversion() {
  echo ""
  log_warn "⚠  WARNING: This operation is IRREVERSIBLE"
  log_info "Draft: $TITLE"
  log_info "Will become: Repository Issue"
  echo ""
  read -p "Continue? (yes/no): " response
  [ "$response" = "yes" ]
}
```

### Testing Strategy

**Test Environment Setup**:
1. Create test project: "GitHub Projects Scripts Test"
2. Add required custom fields: Status, Type, Priority
3. Create sample drafts and repo issues
4. Establish test epic-story hierarchy

**Validation Checklist**:
- [ ] Initialize config for test project
- [ ] Create draft epic
- [ ] Create draft story
- [ ] Set custom fields on both
- [ ] Convert epic to repo issue
- [ ] Convert story to repo issue
- [ ] Link story to epic (verify `trackedIssues`)
- [ ] Query epic's sub-issues
- [ ] Update story status
- [ ] Remove story from epic
- [ ] Delete draft
- [ ] Remove repo issue from project

**Rollback Procedures**:
- Draft creation: Just delete (`gh project item-delete`)
- Repo issue conversion: Cannot rollback (document in warnings)
- Sub-issue linking: Use `removeSubIssue` mutation
- Custom field changes: Manually revert

**Phase 4: Advanced Features**

### Bulk Operations

**Create Epic + Stories from Template**:
```bash
gh-project-bulk-create --template epic-stories.json

# epic-stories.json:
{
  "epic": {
    "title": "Epic #42: Advanced Features",
    "body": "...",
    "status": "Todo",
    "priority": 1
  },
  "stories": [
    {"title": "Story: RTTI", "priority": 2},
    {"title": "Story: Virtual Inheritance", "priority": 2}
  ]
}
```

**Bulk Status Update**:
```bash
# Mark all stories under epic #42 as "Done"
gh-project-bulk-update --parent 42 --status Done
```

### Query Patterns

**Pre-Built Filters** (in `lib/gh-project-queries.sh`):
```bash
# Count by status
count_by_status() {
  gh project item-list --format json | \
    jq -r '.items | group_by(.Status) | map({status: .[0].Status, count: length})'
}

# Export epics with story count
export_epic_summary() {
  # Query each epic's trackedIssues and format as CSV
}

# Find orphaned stories (no parent epic)
find_orphaned_stories() {
  # Query stories where parent field is null
}
```

### Workflow Helpers

**Create Epic Workflow**:
```bash
gh-project-epic-create() {
  # 1. Create draft epic
  # 2. Prompt for story titles
  # 3. Create draft stories
  # 4. Link stories to epic metadata
  # 5. Offer to convert all to repo issues
  # 6. If converted, link using addSubIssue
}
```

**Close Epic Workflow**:
```bash
gh-project-epic-close() {
  # 1. Query epic's sub-issues
  # 2. Confirm all stories are done
  # 3. Close all stories
  # 4. Close epic
  # 5. Update project status
}
```

**Phase 5: Migration Path**

### From Repository-First to Draft-First

**Current State**: Mixed repo issues and project items, duplicate confusion

**Migration Steps**:
1. **Audit**: `gh project item-list --format json` → identify drafts vs repo issues
2. **Cleanup Duplicates**: Identify issues in both repo and project, remove redundant entries
3. **Standardize Workflow**:
   - Going forward: Create all new items as drafts
   - Convert to repo issues only for PR linking or sub-issue hierarchy
4. **Document**: Update team workflow docs

**Handling Existing Hierarchies**:
- Existing epics/stories in repo: Leave as-is, use `addSubIssue` to formalize links
- Custom field workarounds: Keep temporarily, migrate gradually to native sub-issues

### Documentation

**README.md Structure**:
```markdown
# GitHub Projects Management Scripts

## Installation
## Quick Start
## Configuration
## Scripts Reference
  - gh-project-init
  - gh-project-create
  - ...
## Workflows
  - Creating Epic + Stories
  - Linking Stories to Epics
  - Querying and Filtering
## Troubleshooting
## API Reference
```

**Troubleshooting Section**:
- "Error: GraphQL mutation failed" → Check GraphQL-Features header
- "Error: Field not found" → Run `gh-project-init --refresh-cache`
- "Error: Cannot link draft to epic" → Convert draft to repo issue first
- "Sub-issue not showing in UI" → Verify both are repo issues, check permissions

### Implementation Order

**Phase 1: Foundation** (3-4 hours)
- Create `lib/gh-project-common.sh` with logging, error handling, GraphQL helpers
- Implement `gh-project-init` (config management, field caching)
- Implement `gh-project-create` (draft/repo creation, custom fields)
- Test: Create drafts, set fields, verify config

**Phase 2: Core Operations** (3-4 hours)
- Implement `gh-project-convert` (draft → repo with confirmation)
- Implement `gh-project-link` (addSubIssue with GraphQL-Features header)
- Implement `gh-project-list` (query, filter, format)
- Test: Full epic-story workflow (create → convert → link → query)

**Phase 3: Management** (2-3 hours)
- Implement `gh-project-update` (custom field updates)
- Implement `gh-project-delete` (delete drafts, remove repo issues)
- Add error handling, retries, confirmations
- Test: Update workflows, deletion, edge cases

**Phase 4: Polish** (2-3 hours)
- Add dry-run mode to all scripts
- Implement color output, progress indicators
- Add --help documentation
- Create README with examples
- Test: Full workflow end-to-end

**Phase 5: Advanced Features** (Optional, 4-6 hours)
- Bulk operations (template-based creation)
- Query patterns library
- Workflow helpers (epic-create, epic-close)
- Migration utilities

**Total Effort**: 10-14 hours core + 4-6 hours advanced = **14-20 hours**

## Output Specification

Save to: `.prompts/004-github-projects-scripts-plan-updated/github-projects-scripts-plan.md`

[Use same XML structure as previous plan prompt]

## Success Criteria

1. ✅ Native sub-issue API integrated (addSubIssue, removeSubIssue, reprioritizeSubIssue)
2. ✅ GraphQL-Features header support documented
3. ✅ Draft → repo conversion workflow for sub-issue linking
4. ✅ All 7 core scripts specified with interfaces, examples, error handling
5. ✅ Shared library functions outlined (including sub-issue operations)
6. ✅ Config management with field caching
7. ✅ Implementation order with realistic time estimates
8. ✅ Testing strategy with validation checklist
9. ✅ Migration path from old workflow
10. ✅ SUMMARY.md with substantive one-liner

**Target**: Production-ready plan leveraging corrected research

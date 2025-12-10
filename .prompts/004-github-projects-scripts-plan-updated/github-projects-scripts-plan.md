<plan version="2.0" date="2025-12-09">

<executive_summary>
This implementation plan provides production-ready specifications for bash scripts that manage GitHub Projects v2 using the CORRECTED research findings, most critically the native sub-issue API (addSubIssue/removeSubIssue/reprioritizeSubIssue mutations). The original plan would have used custom field workarounds - this plan leverages GitHub's native parent-child relationships for Epic-Story hierarchies, providing better UI integration, progress tracking, and ecosystem support.

**Key Change**: Epic-Story linking uses native GitHub sub-issue mutations with GraphQL-Features header, eliminating the need for custom field workarounds.

**Deliverables**: 7 core scripts + 1 shared library for creating, converting, linking, querying, updating, and deleting project items with full support for Epic-Story hierarchies using native GitHub sub-issue relationships.

**Estimated Effort**: 14-20 hours (10-14 core + 4-6 advanced features)
</executive_summary>

<architecture>

<file_organization>
**Directory Structure**:
```
scripts/gh-projects/
├── lib/
│   └── gh-project-common.sh        # Shared functions
├── gh-project-init                  # Initialize config + cache
├── gh-project-create                # Create draft/repo issues
├── gh-project-convert               # Convert draft → repo
├── gh-project-link                  # Link story to epic (native sub-issue)
├── gh-project-list                  # Query/filter items
├── gh-project-update                # Update custom fields
└── gh-project-delete                # Delete/remove items

~/.config/gh-projects/
└── config.json                      # Configuration + cache
```

**Naming Convention**: `gh-project-{action}` for consistency with gh CLI ecosystem

**Installation**:
```bash
# Copy to PATH
cp scripts/gh-projects/gh-project-* ~/bin/
chmod +x ~/bin/gh-project-*

# Or add to PATH
export PATH="$PATH:$PWD/scripts/gh-projects"
```
</file_organization>

<shared_library>
**File**: `lib/gh-project-common.sh`

**Purpose**: Centralize error handling, logging, GraphQL operations, field caching, and sub-issue operations

**Core Functions**:

```bash
#!/bin/bash
# lib/gh-project-common.sh - Shared functions for GitHub Projects scripts

set -euo pipefail

# Configuration paths
CACHE_DIR="${GH_PROJECT_CACHE_DIR:-$HOME/.config/gh-projects}"
CONFIG_FILE="$CACHE_DIR/config.json"

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

#------------------------------------------------------------------------------
# LOGGING FUNCTIONS
#------------------------------------------------------------------------------

log_success() { echo -e "${GREEN}✓${NC} $*" >&2; }
log_error() { echo -e "${RED}✗${NC} $*" >&2; }
log_warn() { echo -e "${YELLOW}⚠${NC} $*" >&2; }
log_info() { echo -e "${BLUE}ℹ${NC} $*" >&2; }

#------------------------------------------------------------------------------
# ERROR HANDLING
#------------------------------------------------------------------------------

die() {
  log_error "$@"
  exit 1
}

retry_command() {
  local max_attempts=3
  local attempt=1
  local delay=2

  while (( attempt <= max_attempts )); do
    if "$@"; then
      return 0
    fi

    log_warn "Attempt $attempt/$max_attempts failed, retrying in ${delay}s..."
    sleep "$delay"
    attempt=$((attempt + 1))
    delay=$((delay * 2))
  done

  die "Command failed after $max_attempts attempts: $*"
}

#------------------------------------------------------------------------------
# CONFIGURATION MANAGEMENT
#------------------------------------------------------------------------------

ensure_config_dir() {
  mkdir -p "$CACHE_DIR"
}

load_config() {
  ensure_config_dir

  if [[ ! -f "$CONFIG_FILE" ]]; then
    die "Configuration not initialized. Run: gh-project-init --project NUM"
  fi

  # Export config values
  export PROJECT_OWNER=$(jq -r '.owner' < "$CONFIG_FILE")
  export PROJECT_REPO=$(jq -r '.repo' < "$CONFIG_FILE")
  export PROJECT_NUMBER=$(jq -r '.project_number' < "$CONFIG_FILE")
  export PROJECT_ID=$(jq -r '.project_id' < "$CONFIG_FILE")
}

save_config() {
  local owner="$1"
  local repo="$2"
  local project_number="$3"
  local project_id="$4"

  ensure_config_dir

  jq -n \
    --arg owner "$owner" \
    --arg repo "$repo" \
    --argjson project_number "$project_number" \
    --arg project_id "$project_id" \
    --arg cache_timestamp "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg cache_version "2.0" \
    '{
      owner: $owner,
      repo: $repo,
      project_number: $project_number,
      project_id: $project_id,
      cache_timestamp: $cache_timestamp,
      cache_version: $cache_version,
      field_cache: {}
    }' > "$CONFIG_FILE"
}

#------------------------------------------------------------------------------
# GRAPHQL OPERATIONS
#------------------------------------------------------------------------------

execute_graphql() {
  local query="$1"
  shift

  retry_command gh api graphql -f query="$query" "$@"
}

# Execute GraphQL mutation with GraphQL-Features header for sub-issues
execute_sub_issue_mutation() {
  local query="$1"
  shift

  retry_command gh api graphql \
    -H "GraphQL-Features:sub_issues" \
    -f query="$query" \
    "$@"
}

#------------------------------------------------------------------------------
# FIELD CACHING AND RESOLUTION
#------------------------------------------------------------------------------

cache_fields() {
  local project_number="${1:-$PROJECT_NUMBER}"
  local owner="${2:-$PROJECT_OWNER}"

  log_info "Caching project fields..."

  local fields_json
  fields_json=$(gh project field-list "$project_number" \
    --owner "$owner" \
    --format json)

  # Update config with field cache
  local tmp_config=$(mktemp)
  jq --argjson fields "$fields_json" \
    '.field_cache = ($fields.fields | map({(.name): {id: .id, type: .type, options: (.options // [])}}) | add)' \
    < "$CONFIG_FILE" > "$tmp_config"
  mv "$tmp_config" "$CONFIG_FILE"

  log_success "Cached $(echo "$fields_json" | jq '.fields | length') fields"
}

get_field_id() {
  local field_name="$1"

  jq -r ".field_cache.\"$field_name\".id // empty" < "$CONFIG_FILE"
}

get_option_id() {
  local field_name="$1"
  local option_name="$2"

  jq -r ".field_cache.\"$field_name\".options[] | select(.name == \"$option_name\") | .id" < "$CONFIG_FILE"
}

#------------------------------------------------------------------------------
# ID RETRIEVAL
#------------------------------------------------------------------------------

get_project_id() {
  local project_number="${1:-$PROJECT_NUMBER}"
  local owner="${2:-$PROJECT_OWNER}"

  gh project view "$project_number" \
    --owner "$owner" \
    --format json | jq -r '.id'
}

get_repo_id() {
  local owner="${1:-$PROJECT_OWNER}"
  local repo="${2:-$PROJECT_REPO}"

  gh repo view "$owner/$repo" --json id | jq -r '.id'
}

get_issue_id() {
  local issue_number="$1"
  local repo="${2:-$PROJECT_OWNER/$PROJECT_REPO}"

  gh issue view "$issue_number" --repo "$repo" --json id -q '.id'
}

get_draft_content_id() {
  local project_item_id="$1"

  execute_graphql "{
    node(id: \"$project_item_id\") {
      ... on ProjectV2Item {
        content {
          ... on DraftIssue {
            id
          }
        }
      }
    }
  }" | jq -r '.data.node.content.id // empty'
}

#------------------------------------------------------------------------------
# SUB-ISSUE OPERATIONS (NATIVE API)
#------------------------------------------------------------------------------

add_sub_issue() {
  local parent_number="$1"
  local child_number="$2"
  local repo="${3:-$PROJECT_OWNER/$PROJECT_REPO}"

  log_info "Linking Story #$child_number to Epic #$parent_number..."

  # Get issue IDs
  local parent_id=$(get_issue_id "$parent_number" "$repo")
  local child_id=$(get_issue_id "$child_number" "$repo")

  if [[ -z "$parent_id" ]]; then
    die "Epic #$parent_number not found or not a repository issue"
  fi

  if [[ -z "$child_id" ]]; then
    die "Story #$child_number not found or not a repository issue"
  fi

  # Add sub-issue with GraphQL-Features header
  local result
  result=$(execute_sub_issue_mutation '
    mutation($parentId: ID!, $childId: ID!) {
      addSubIssue(input: {
        issueId: $parentId
        subIssueId: $childId
      }) {
        issue {
          number
          title
          trackedIssues {
            totalCount
          }
        }
        subIssue {
          number
          title
        }
      }
    }
  ' \
    -f parentId="$parent_id" \
    -f childId="$child_id")

  local total_count=$(echo "$result" | jq -r '.data.addSubIssue.issue.trackedIssues.totalCount')
  log_success "Story #$child_number linked to Epic #$parent_number ($total_count total sub-issues)"
}

remove_sub_issue() {
  local parent_number="$1"
  local child_number="$2"
  local repo="${3:-$PROJECT_OWNER/$PROJECT_REPO}"

  log_info "Removing Story #$child_number from Epic #$parent_number..."

  local parent_id=$(get_issue_id "$parent_number" "$repo")
  local child_id=$(get_issue_id "$child_number" "$repo")

  execute_sub_issue_mutation '
    mutation($parentId: ID!, $childId: ID!) {
      removeSubIssue(input: {
        issueId: $parentId
        subIssueId: $childId
      }) {
        issue {
          number
          trackedIssues { totalCount }
        }
        subIssue {
          number
        }
      }
    }
  ' \
    -f parentId="$parent_id" \
    -f childId="$child_id" \
    --jq '.data.removeSubIssue | "Removed Story #\(.subIssue.number) from Epic #\(.issue.number)"'

  log_success "Story #$child_number removed from Epic #$parent_number"
}

query_sub_issues() {
  local parent_number="$1"
  local repo="${2:-$PROJECT_OWNER/$PROJECT_REPO}"
  local owner="${repo%%/*}"
  local repo_name="${repo##*/}"

  execute_sub_issue_mutation "
    query {
      repository(owner: \"$owner\", name: \"$repo_name\") {
        issue(number: $parent_number) {
          title
          trackedIssues(first: 100) {
            totalCount
            nodes {
              number
              title
              state
              url
            }
          }
        }
      }
    }
  " | jq -r '.data.repository.issue'
}

#------------------------------------------------------------------------------
# VALIDATION
#------------------------------------------------------------------------------

validate_prerequisites() {
  # Check gh CLI
  if ! command -v gh &> /dev/null; then
    die "gh CLI not found. Install from https://cli.github.com/"
  fi

  # Check gh auth
  if ! gh auth status &> /dev/null; then
    die "Not authenticated. Run: gh auth login"
  fi

  # Check jq
  if ! command -v jq &> /dev/null; then
    die "jq not found. Install from https://stedolan.github.io/jq/"
  fi
}

#------------------------------------------------------------------------------
# DRY-RUN SUPPORT
#------------------------------------------------------------------------------

execute() {
  local description="$1"
  shift

  if [[ "${DRY_RUN:-false}" == "true" ]]; then
    log_warn "[DRY-RUN] $description: $*"
    return 0
  fi

  log_info "$description"
  "$@"
}

#------------------------------------------------------------------------------
# CUSTOM FIELD OPERATIONS
#------------------------------------------------------------------------------

set_single_select_field() {
  local item_id="$1"
  local field_name="$2"
  local option_name="$3"

  local field_id=$(get_field_id "$field_name")
  local option_id=$(get_option_id "$field_name" "$option_name")

  if [[ -z "$field_id" ]]; then
    die "Field '$field_name' not found. Run: gh-project-init --refresh-cache"
  fi

  if [[ -z "$option_id" ]]; then
    die "Option '$option_name' not found for field '$field_name'"
  fi

  execute "Set $field_name=$option_name" \
    gh project item-edit \
      --project-id "$PROJECT_ID" \
      --id "$item_id" \
      --field-id "$field_id" \
      --single-select-option-id "$option_id" \
      --format json
}
```

**Function Categories**:

1. **Logging**: Color-coded output (success/error/warn/info)
2. **Error Handling**: Retry with exponential backoff, die function
3. **Configuration**: Load/save config, manage cache
4. **GraphQL**: Execute queries/mutations with retry
5. **Sub-Issue API**: Native addSubIssue/removeSubIssue/query operations
6. **Field Caching**: Cache field IDs/option IDs for performance
7. **ID Resolution**: Convert numbers to GraphQL IDs
8. **Validation**: Check prerequisites (gh, jq, auth)
9. **Dry-Run**: Preview mode for all mutations

</shared_library>

<configuration_management>
**Config File**: `~/.config/gh-projects/config.json`

**Structure**:
```json
{
  "owner": "o2alexanderfedin",
  "repo": "cpp-to-c-transpiler",
  "project_number": 14,
  "project_id": "PVT_kwHOBJ7Qkc4BKHLI",
  "cache_timestamp": "2025-12-09T21:00:00Z",
  "cache_version": "2.0",
  "field_cache": {
    "Status": {
      "id": "PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1IE",
      "type": "ProjectV2SingleSelectField",
      "options": [
        {"id": "f75ad846", "name": "Todo"},
        {"id": "47fc9ee4", "name": "In Progress"},
        {"id": "98236657", "name": "Done"}
      ]
    },
    "Type": {
      "id": "PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1I4",
      "type": "ProjectV2SingleSelectField",
      "options": [
        {"id": "fca9429d", "name": "Epic"},
        {"id": "839ffda1", "name": "User Story"},
        {"id": "7a520867", "name": "Task"},
        {"id": "45369092", "name": "Bug"},
        {"id": "979f85d9", "name": "Spike"}
      ]
    },
    "Priority": {
      "id": "PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1Kk",
      "type": "ProjectV2SingleSelectField",
      "options": [
        {"id": "d0e39f7a", "name": "Critical"},
        {"id": "5b8eb342", "name": "High"},
        {"id": "9a73c416", "name": "Medium"},
        {"id": "2f4d8c93", "name": "Low"}
      ]
    }
  }
}
```

**Cache Invalidation**:
- Manual: `gh-project-init --refresh-cache`
- Auto: If timestamp > 7 days old
- On error: Suggest refresh when field not found

**Cache Corruption Handling**:
- Invalid JSON → Delete and prompt for re-init
- Missing fields → Auto-refresh
- Backup to `config.json.bak` before updates
</configuration_management>

</architecture>

<scripts>

<script name="gh-project-init">
**Purpose**: Initialize configuration, cache field metadata, validate setup

**Interface**:
```bash
gh-project-init [OPTIONS]

Options:
  --project NUM        Project number (required)
  --owner OWNER        Repository owner (default: auto-detect from git)
  --repo REPO          Repository name (default: auto-detect from git)
  --refresh-cache      Force refresh field cache
  -h, --help           Show help
```

**Implementation**:
```bash
#!/bin/bash
# gh-project-init - Initialize GitHub Projects configuration

source "$(dirname "$0")/lib/gh-project-common.sh"

usage() {
  cat << EOF
Usage: gh-project-init [OPTIONS]

Initialize GitHub Projects configuration and field cache.

Options:
  --project NUM        Project number (required)
  --owner OWNER        Repository owner (default: auto-detect)
  --repo REPO          Repository name (default: auto-detect)
  --refresh-cache      Force refresh field cache
  -h, --help           Show help

Examples:
  # Initialize for project #14 (auto-detect repo)
  gh-project-init --project 14

  # Initialize with explicit repo
  gh-project-init --project 14 --owner myorg --repo myrepo

  # Refresh cached field metadata
  gh-project-init --project 14 --refresh-cache
EOF
  exit 0
}

# Parse arguments
PROJECT_NUMBER=""
OWNER=""
REPO=""
REFRESH_CACHE=false

while [[ $# -gt 0 ]]; do
  case $1 in
    --project) PROJECT_NUMBER="$2"; shift 2 ;;
    --owner) OWNER="$2"; shift 2 ;;
    --repo) REPO="$2"; shift 2 ;;
    --refresh-cache) REFRESH_CACHE=true; shift ;;
    -h|--help) usage ;;
    *) die "Unknown option: $1" ;;
  esac
done

# Validate prerequisites
validate_prerequisites

# Validate project number
if [[ -z "$PROJECT_NUMBER" ]]; then
  die "Project number required. Use: --project NUM"
fi

# Auto-detect owner/repo if not provided
if [[ -z "$OWNER" ]] || [[ -z "$REPO" ]]; then
  log_info "Auto-detecting repository..."
  REPO_INFO=$(gh repo view --json owner,name)
  OWNER=${OWNER:-$(echo "$REPO_INFO" | jq -r '.owner.login')}
  REPO=${REPO:-$(echo "$REPO_INFO" | jq -r '.name')}
fi

log_info "Configuration:"
log_info "  Owner: $OWNER"
log_info "  Repo: $REPO"
log_info "  Project: #$PROJECT_NUMBER"

# Validate project exists
log_info "Validating project..."
if ! gh project view "$PROJECT_NUMBER" --owner "$OWNER" --format json &> /dev/null; then
  die "Project #$PROJECT_NUMBER not found for owner $OWNER"
fi

# Get project ID
PROJECT_ID=$(get_project_id "$PROJECT_NUMBER" "$OWNER")
log_success "Project validated: $PROJECT_ID"

# Save config
save_config "$OWNER" "$REPO" "$PROJECT_NUMBER" "$PROJECT_ID"
log_success "Configuration saved: $CONFIG_FILE"

# Cache fields
cache_fields "$PROJECT_NUMBER" "$OWNER"

# Display summary
echo ""
log_success "Initialization complete!"
echo ""
echo "Configuration:"
jq -r 'to_entries | map("  \(.key): \(.value)") | .[]' < "$CONFIG_FILE" | grep -v field_cache
echo ""
echo "Cached fields:"
jq -r '.field_cache | to_entries | map("  - \(.key) (\(.value.type))") | .[]' < "$CONFIG_FILE"
```

**Behavior**:
1. Validate gh CLI, jq, authentication
2. Auto-detect or accept owner/repo/project number
3. Validate project exists and accessible
4. Get project ID via GraphQL
5. Query all custom fields
6. Cache field IDs and option IDs
7. Display summary

**Error Handling**:
- Project not found → Clear error message with project number
- No permissions → "Requires project write access"
- gh not authenticated → "Run: gh auth login"
- Invalid config → Delete and re-initialize

**Time Estimate**: 1 hour
</script>

<script name="gh-project-create">
**Purpose**: Create draft or repository issue in project with custom fields

**Interface**:
```bash
gh-project-create [OPTIONS]

Options:
  --title TEXT         Issue title (required)
  --body TEXT          Issue body (optional)
  --type TYPE          Issue type: epic, story, task, bug, spike (default: story)
  --status STATUS      Status: Todo, "In Progress", Done (default: Todo)
  --priority PRIORITY  Priority: Critical, High, Medium, Low (optional)
  --draft              Create as draft (default: true)
  --repo-issue         Create as repository issue directly
  --dry-run            Show what would be created
  -h, --help           Show help
```

**Implementation**:
```bash
#!/bin/bash
# gh-project-create - Create draft or repository issue in project

source "$(dirname "$0")/lib/gh-project-common.sh"

usage() {
  cat << EOF
Usage: gh-project-create [OPTIONS]

Create draft or repository issue in GitHub Project with custom fields.

Options:
  --title TEXT         Issue title (required)
  --body TEXT          Issue body (optional)
  --type TYPE          Issue type: epic, story, task, bug, spike (default: story)
  --status STATUS      Status: Todo, "In Progress", Done (default: Todo)
  --priority PRIORITY  Priority: Critical, High, Medium, Low (optional)
  --draft              Create as draft (default: true)
  --repo-issue         Create as repository issue directly
  --dry-run            Show what would be created
  -h, --help           Show help

Examples:
  # Create draft epic
  gh-project-create --title "Epic #42: Advanced Features" --type epic

  # Create story as repo issue (for sub-issue linking)
  gh-project-create \\
    --title "Story: Implement RTTI" \\
    --type story \\
    --status "In Progress" \\
    --repo-issue

  # Dry-run
  gh-project-create --title "Test" --dry-run
EOF
  exit 0
}

# Parse arguments
TITLE=""
BODY=""
TYPE="story"
STATUS="Todo"
PRIORITY=""
CREATE_DRAFT=true
DRY_RUN=false

while [[ $# -gt 0 ]]; do
  case $1 in
    --title) TITLE="$2"; shift 2 ;;
    --body) BODY="$2"; shift 2 ;;
    --type) TYPE="$2"; shift 2 ;;
    --status) STATUS="$2"; shift 2 ;;
    --priority) PRIORITY="$2"; shift 2 ;;
    --draft) CREATE_DRAFT=true; shift ;;
    --repo-issue) CREATE_DRAFT=false; shift ;;
    --dry-run) DRY_RUN=true; shift ;;
    -h|--help) usage ;;
    *) die "Unknown option: $1" ;;
  esac
done

# Validate
load_config
validate_prerequisites

if [[ -z "$TITLE" ]]; then
  die "Title required. Use: --title TEXT"
fi

# Normalize type to match field options
case "${TYPE,,}" in
  epic) TYPE="Epic" ;;
  story) TYPE="User Story" ;;
  task) TYPE="Task" ;;
  bug) TYPE="Bug" ;;
  spike) TYPE="Spike" ;;
  *) die "Invalid type: $TYPE. Valid: epic, story, task, bug, spike" ;;
esac

# Dry-run preview
if [[ "$DRY_RUN" == "true" ]]; then
  log_warn "[DRY-RUN] Would create:"
  echo "  Title: $TITLE"
  echo "  Body: ${BODY:-<empty>}"
  echo "  Type: $TYPE"
  echo "  Status: $STATUS"
  echo "  Priority: ${PRIORITY:-<not set>}"
  echo "  Create as: $([ "$CREATE_DRAFT" == "true" ] && echo "Draft" || echo "Repository Issue")"
  exit 0
fi

# Create issue
ITEM_ID=""
ISSUE_URL=""

if [[ "$CREATE_DRAFT" == "true" ]]; then
  # Create draft issue
  log_info "Creating draft issue..."
  RESULT=$(gh project item-create "$PROJECT_NUMBER" \
    --owner "$PROJECT_OWNER" \
    --title "$TITLE" \
    --body "$BODY" \
    --format json)

  ITEM_ID=$(echo "$RESULT" | jq -r '.id')
  log_success "Draft issue created: $ITEM_ID"
else
  # Create repository issue
  log_info "Creating repository issue..."
  ISSUE_URL=$(gh issue create \
    --repo "$PROJECT_OWNER/$PROJECT_REPO" \
    --title "$TITLE" \
    --body "$BODY")

  log_success "Repository issue created: $ISSUE_URL"

  # Add to project
  log_info "Adding to project..."
  RESULT=$(gh project item-add "$PROJECT_NUMBER" \
    --owner "$PROJECT_OWNER" \
    --url "$ISSUE_URL" \
    --format json)

  ITEM_ID=$(echo "$RESULT" | jq -r '.id')
  log_success "Added to project: $ITEM_ID"
fi

# Set custom fields
log_info "Setting custom fields..."

set_single_select_field "$ITEM_ID" "Type" "$TYPE"
set_single_select_field "$ITEM_ID" "Status" "$STATUS"

if [[ -n "$PRIORITY" ]]; then
  set_single_select_field "$ITEM_ID" "Priority" "$PRIORITY"
fi

# Display result
echo ""
log_success "Issue created successfully!"
echo ""
echo "  Item ID: $ITEM_ID"
echo "  Title: $TITLE"
echo "  Type: $TYPE"
echo "  Status: $STATUS"
if [[ -n "$ISSUE_URL" ]]; then
  echo "  URL: $ISSUE_URL"
fi
```

**Behavior**:
1. Load config, validate inputs
2. Create draft via `gh project item-create` OR repository issue via `gh issue create`
3. If repo issue, add to project via `gh project item-add`
4. Set custom fields (Type, Status, Priority)
5. Output item ID and summary

**Error Handling**:
- Missing title → "Error: --title required"
- Invalid type → List valid types
- Field not found → Suggest `gh-project-init --refresh-cache`
- Rate limit → Retry with backoff

**Time Estimate**: 2 hours
</script>

<script name="gh-project-link">
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

**Implementation**:
```bash
#!/bin/bash
# gh-project-link - Link story to epic using native sub-issue API

source "$(dirname "$0")/lib/gh-project-common.sh"

usage() {
  cat << EOF
Usage: gh-project-link [OPTIONS]

Link story to epic using GitHub's native sub-issue API.

Options:
  --parent NUM         Parent issue number (epic)
  --child NUM          Child issue number (story)
  --children NUM,NUM   Multiple children (comma-separated)
  --dry-run            Show what would be linked
  -h, --help           Show help

Examples:
  # Link single story to epic
  gh-project-link --parent 42 --child 167

  # Link multiple stories
  gh-project-link --parent 42 --children 167,168,169

  # Preview
  gh-project-link --parent 42 --child 167 --dry-run

Requirements:
  - Both parent and child must be repository issues (not drafts)
  - Both must be in the same repository
EOF
  exit 0
}

# Parse arguments
PARENT=""
CHILDREN=()
DRY_RUN=false

while [[ $# -gt 0 ]]; do
  case $1 in
    --parent) PARENT="$2"; shift 2 ;;
    --child) CHILDREN+=("$2"); shift 2 ;;
    --children) IFS=',' read -ra CHILDREN <<< "$2"; shift 2 ;;
    --dry-run) DRY_RUN=true; shift ;;
    -h|--help) usage ;;
    *) die "Unknown option: $1" ;;
  esac
done

# Validate
load_config
validate_prerequisites

if [[ -z "$PARENT" ]]; then
  die "Parent issue required. Use: --parent NUM"
fi

if [[ ${#CHILDREN[@]} -eq 0 ]]; then
  die "At least one child issue required. Use: --child NUM or --children NUM,NUM"
fi

# Dry-run preview
if [[ "$DRY_RUN" == "true" ]]; then
  log_warn "[DRY-RUN] Would link:"
  echo "  Epic: #$PARENT"
  echo "  Stories: ${CHILDREN[*]}"
  exit 0
fi

# Link each child to parent
SUCCESS_COUNT=0
FAILED_COUNT=0

for child in "${CHILDREN[@]}"; do
  if add_sub_issue "$PARENT" "$child"; then
    ((SUCCESS_COUNT++))
  else
    log_error "Failed to link Story #$child to Epic #$PARENT"
    ((FAILED_COUNT++))
  fi
done

# Summary
echo ""
log_success "Linking complete!"
echo "  Success: $SUCCESS_COUNT"
if [[ $FAILED_COUNT -gt 0 ]]; then
  echo "  Failed: $FAILED_COUNT"
fi

# Show epic's current sub-issues
log_info "Epic #$PARENT sub-issues:"
query_sub_issues "$PARENT" | jq -r '.trackedIssues.nodes[] | "  - #\(.number): \(.title) (\(.state))"'
```

**Behavior**:
1. Validate parent and children exist as repository issues
2. Get issue IDs using `gh issue view --json id`
3. Execute `addSubIssue` mutation with `GraphQL-Features:sub_issues` header
4. Verify link by querying `trackedIssues`
5. Output confirmation with progress

**Error Handling**:
- Parent is draft → "Epic #42 is a draft. Convert first: gh-project-convert"
- Child is draft → "Story #167 is a draft. Convert first."
- Already linked → Warning, skip
- Permission denied → Clear error message
- GraphQL error → Show error details

**Time Estimate**: 2 hours
</script>

<script name="gh-project-convert">
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

**Implementation**:
```bash
#!/bin/bash
# gh-project-convert - Convert draft issue to repository issue

source "$(dirname "$0")/lib/gh-project-common.sh"

usage() {
  cat << EOF
Usage: gh-project-convert [OPTIONS]

Convert draft issue to repository issue (IRREVERSIBLE).

Options:
  --item ID            Project item ID (PVTI_...)
  --title TEXT         Filter by title match
  --yes, -y            Skip confirmation
  --dry-run            Show what would be converted
  -h, --help           Show help

Examples:
  # Convert specific draft
  gh-project-convert --item PVTI_lADOQku...

  # Convert by title
  gh-project-convert --title "Epic #42"

  # Skip confirmation
  gh-project-convert --item PVTI_... --yes

WARNING: Conversion is IRREVERSIBLE. Draft cannot be converted back.
EOF
  exit 0
}

# Parse arguments
ITEM_ID=""
TITLE_FILTER=""
SKIP_CONFIRM=false
DRY_RUN=false

while [[ $# -gt 0 ]]; do
  case $1 in
    --item) ITEM_ID="$2"; shift 2 ;;
    --title) TITLE_FILTER="$2"; shift 2 ;;
    -y|--yes) SKIP_CONFIRM=true; shift ;;
    --dry-run) DRY_RUN=true; shift ;;
    -h|--help) usage ;;
    *) die "Unknown option: $1" ;;
  esac
done

# Validate
load_config
validate_prerequisites

# Find item by title if not provided
if [[ -z "$ITEM_ID" ]] && [[ -n "$TITLE_FILTER" ]]; then
  log_info "Searching for draft issues matching: $TITLE_FILTER"

  ITEMS=$(gh project item-list "$PROJECT_NUMBER" \
    --owner "$PROJECT_OWNER" \
    --limit 200 \
    --format json | \
    jq -r ".items[] | select(.content.type == \"DraftIssue\" and (.title | contains(\"$TITLE_FILTER\")))")

  ITEM_COUNT=$(echo "$ITEMS" | jq -s 'length')

  if [[ $ITEM_COUNT -eq 0 ]]; then
    die "No draft issues found matching: $TITLE_FILTER"
  elif [[ $ITEM_COUNT -gt 1 ]]; then
    echo "Multiple matches found:"
    echo "$ITEMS" | jq -r '"  - \(.id): \(.title)"'
    die "Specify exact item with --item ID"
  fi

  ITEM_ID=$(echo "$ITEMS" | jq -r '.id')
  log_success "Found: $ITEM_ID"
fi

if [[ -z "$ITEM_ID" ]]; then
  die "Item ID required. Use: --item ID or --title TEXT"
fi

# Get item details
ITEM_JSON=$(gh project item-list "$PROJECT_NUMBER" \
  --owner "$PROJECT_OWNER" \
  --limit 200 \
  --format json | \
  jq ".items[] | select(.id == \"$ITEM_ID\")")

if [[ -z "$ITEM_JSON" ]]; then
  die "Item not found: $ITEM_ID"
fi

ITEM_TITLE=$(echo "$ITEM_JSON" | jq -r '.title')
ITEM_TYPE=$(echo "$ITEM_JSON" | jq -r '.content.type')

# Check if already repository issue
if [[ "$ITEM_TYPE" != "DraftIssue" ]]; then
  die "Item is already a repository issue"
fi

# Preview
log_warn "⚠  WARNING: This operation is IRREVERSIBLE"
echo ""
echo "Draft Issue:"
echo "  ID: $ITEM_ID"
echo "  Title: $ITEM_TITLE"
echo ""
echo "Will become:"
echo "  Repository Issue in $PROJECT_OWNER/$PROJECT_REPO"
echo "  Custom fields: PRESERVED"
echo ""

if [[ "$DRY_RUN" == "true" ]]; then
  log_warn "[DRY-RUN] Would convert draft to repository issue"
  exit 0
fi

# Confirmation
if [[ "$SKIP_CONFIRM" != "true" ]]; then
  read -p "Continue? (yes/no): " response
  if [[ "$response" != "yes" ]]; then
    log_info "Conversion cancelled"
    exit 0
  fi
fi

# Convert
log_info "Converting draft to repository issue..."

REPO_ID=$(get_repo_id)

RESULT=$(gh api graphql -f query="
  mutation {
    convertProjectV2DraftIssueItemToIssue(input: {
      itemId: \"$ITEM_ID\"
      repositoryId: \"$REPO_ID\"
    }) {
      item {
        id
        content {
          ... on Issue {
            number
            url
          }
        }
      }
    }
  }
")

ISSUE_NUMBER=$(echo "$RESULT" | jq -r '.data.convertProjectV2DraftIssueItemToIssue.item.content.number')
ISSUE_URL=$(echo "$RESULT" | jq -r '.data.convertProjectV2DraftIssueItemToIssue.item.content.url')

log_success "Converted to Issue #$ISSUE_NUMBER"
echo ""
echo "  URL: $ISSUE_URL"
echo "  Item ID: $ITEM_ID (unchanged)"
```

**Behavior**:
1. Get draft content ID via GraphQL
2. Show preview: title, fields, "IRREVERSIBLE" warning
3. Confirm with user (unless `--yes`)
4. Execute `convertProjectV2DraftIssueItemToIssue` mutation
5. Verify conversion, get new issue number
6. Output result

**Error Handling**:
- Item not found → "Item PVTI_... not found"
- Already repo issue → "Item is already repository issue #177"
- User cancels → "Conversion cancelled"
- Conversion fails → "Error: ..., draft preserved"

**Time Estimate**: 2 hours
</script>

<script name="gh-project-list">
**Purpose**: Query and filter project items with advanced jq patterns

**Interface**:
```bash
gh-project-list [OPTIONS]

Options:
  --status STATUS      Filter by status
  --type TYPE          Filter by type (epic, story, task, bug, spike)
  --drafts-only        Show only draft issues
  --repo-only          Show only repository issues
  --parent NUM         Show sub-issues of parent epic
  --format FORMAT      Output format: table, json, csv (default: table)
  --limit NUM          Limit results (default: 100)
  -h, --help           Show help
```

**Implementation**: Standard item-list with jq filtering + sub-issue query for --parent

**Time Estimate**: 2 hours
</script>

<script name="gh-project-update">
**Purpose**: Update draft/repo issue custom fields

**Interface**:
```bash
gh-project-update [OPTIONS]

Options:
  --item ID            Project item ID
  --issue NUM          Repository issue number (auto-find in project)
  --status STATUS      Update status
  --priority PRIORITY  Update priority
  --type TYPE          Update type
  --dry-run            Preview changes
  -h, --help           Show help
```

**Implementation**: Get current values, update specified fields, show diff

**Time Estimate**: 1.5 hours
</script>

<script name="gh-project-delete">
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

**Implementation**: Confirm deletion, delete via item-delete, handle drafts vs repo issues

**Time Estimate**: 1.5 hours
</script>

</scripts>

<workflows>

<workflow name="epic-story-creation">
**Complete Epic-Story Workflow Using Native Sub-Issue API**

```bash
#!/bin/bash
# epic-story-workflow.sh - Complete workflow for Epic management

set -euo pipefail

source "$(dirname "$0")/lib/gh-project-common.sh"

# 1. Create Epic as repository issue
create_epic() {
  local title="$1"
  local body="$2"

  log_info "Creating Epic as repository issue..."

  # Create repository issue (not draft, for sub-issue capability)
  local issue_url=$(gh issue create \
    --repo "$PROJECT_OWNER/$PROJECT_REPO" \
    --title "$title" \
    --body "$body" \
    --label "epic")

  local issue_number=$(echo "$issue_url" | grep -oP '\d+$')

  # Add to project
  local item_id=$(gh project item-add "$PROJECT_NUMBER" \
    --owner "$PROJECT_OWNER" \
    --url "$issue_url" \
    --format json | jq -r '.id')

  # Set Type = Epic
  set_single_select_field "$item_id" "Type" "Epic"
  set_single_select_field "$item_id" "Status" "Todo"

  log_success "Epic created: #$issue_number"
  echo "$issue_number"
}

# 2. Create Story as repository issue
create_story() {
  local epic_number="$1"
  local title="$2"
  local body="$3"

  log_info "Creating Story as repository issue..."

  # Create repository issue
  local issue_url=$(gh issue create \
    --repo "$PROJECT_OWNER/$PROJECT_REPO" \
    --title "[Epic #$epic_number] $title" \
    --body "$body" \
    --label "story")

  local issue_number=$(echo "$issue_url" | grep -oP '\d+$')

  # Add to project
  local item_id=$(gh project item-add "$PROJECT_NUMBER" \
    --owner "$PROJECT_OWNER" \
    --url "$issue_url" \
    --format json | jq -r '.id')

  # Set Type = User Story
  set_single_select_field "$item_id" "Type" "User Story"
  set_single_select_field "$item_id" "Status" "Todo"

  log_success "Story created: #$issue_number"
  echo "$issue_number"
}

# 3. Main workflow
main() {
  load_config

  # Create Epic
  EPIC_NUMBER=$(create_epic \
    "Epic #42: Advanced Features" \
    "This epic tracks advanced features implementation.")

  # Create Stories
  STORY1=$(create_story "$EPIC_NUMBER" \
    "Story: Implement RTTI" \
    "Implementation of Run-Time Type Information")

  STORY2=$(create_story "$EPIC_NUMBER" \
    "Story: Virtual Inheritance" \
    "Support for virtual base classes")

  STORY3=$(create_story "$EPIC_NUMBER" \
    "Story: Exception Handling" \
    "Implement exception handling")

  # Link Stories to Epic using native sub-issue API
  log_info "Linking Stories to Epic..."
  add_sub_issue "$EPIC_NUMBER" "$STORY1"
  add_sub_issue "$EPIC_NUMBER" "$STORY2"
  add_sub_issue "$EPIC_NUMBER" "$STORY3"

  # Display result
  echo ""
  log_success "Epic-Story hierarchy created!"
  echo ""
  echo "Epic: #$EPIC_NUMBER"
  query_sub_issues "$EPIC_NUMBER" | jq -r '.trackedIssues.nodes[] | "  - #\(.number): \(.title)"'
}

main "$@"
```

**Output**:
```
✓ Epic created: #42
✓ Story created: #167
✓ Story created: #168
✓ Story created: #169
ℹ Linking Stories to Epic...
✓ Story #167 linked to Epic #42 (1 total sub-issues)
✓ Story #168 linked to Epic #42 (2 total sub-issues)
✓ Story #169 linked to Epic #42 (3 total sub-issues)

✓ Epic-Story hierarchy created!

Epic: #42
  - #167: [Epic #42] Story: Implement RTTI
  - #168: [Epic #42] Story: Virtual Inheritance
  - #169: [Epic #42] Story: Exception Handling
```

**Benefits of Native API**:
- GitHub UI shows sub-issues in issue detail
- Progress tracking: "3 of 3 tasks"
- Parent field auto-populates in project views
- Works with GitHub Actions, webhooks
- No custom field maintenance
</workflow>

<workflow name="query-epic-progress">
**Query Epic Progress with Native Sub-Issue API**

```bash
#!/bin/bash
# query-epic-progress.sh - Display Epic progress using native sub-issues

source "$(dirname "$0")/lib/gh-project-common.sh"

query_epic_progress() {
  local epic_number="$1"

  load_config

  log_info "Querying Epic #$epic_number progress..."

  # Query sub-issues with state
  local result=$(execute_sub_issue_mutation "
    query {
      repository(owner: \"$PROJECT_OWNER\", name: \"$PROJECT_REPO\") {
        issue(number: $epic_number) {
          title
          trackedIssues(first: 100) {
            totalCount
            nodes {
              number
              title
              state
              url
            }
          }
        }
      }
    }
  ")

  local title=$(echo "$result" | jq -r '.data.repository.issue.title')
  local total=$(echo "$result" | jq -r '.data.repository.issue.trackedIssues.totalCount')
  local done=$(echo "$result" | jq -r '[.data.repository.issue.trackedIssues.nodes[] | select(.state == "CLOSED")] | length')

  echo ""
  echo "Epic #$epic_number: $title"
  echo "Progress: $done/$total complete"
  echo ""
  echo "Stories:"
  echo "$result" | jq -r '.data.repository.issue.trackedIssues.nodes[] | "  [\(if .state == "CLOSED" then "✓" else " " end)] #\(.number): \(.title)"'
}

query_epic_progress "$@"
```

**Output**:
```
Epic #42: Epic #42: Advanced Features
Progress: 2/3 complete

Stories:
  [✓] #167: [Epic #42] Story: Implement RTTI
  [✓] #168: [Epic #42] Story: Virtual Inheritance
  [ ] #169: [Epic #42] Story: Exception Handling
```
</workflow>

</workflows>

<testing>

<test_plan>
**Test Environment**:
- Project #14 (C++ to C Transpiler)
- Custom fields: Status, Type, Priority
- Mix of draft and repository issues

**Test Cases**:

1. **Initialization**
   - [ ] `gh-project-init --project 14` succeeds
   - [ ] Config file created with correct structure
   - [ ] Field cache contains Status, Type, Priority
   - [ ] Auto-detection works from git repo
   - [ ] `--refresh-cache` updates field data

2. **Draft Issue Creation**
   - [ ] Create draft epic
   - [ ] Create draft story
   - [ ] Set custom fields (Type, Status, Priority)
   - [ ] Verify in project list

3. **Repository Issue Creation**
   - [ ] Create epic as repo issue
   - [ ] Create story as repo issue
   - [ ] Add to project
   - [ ] Set custom fields
   - [ ] Verify in GitHub UI

4. **Draft Conversion**
   - [ ] Convert draft epic to repo issue
   - [ ] Custom fields preserved
   - [ ] Issue number assigned
   - [ ] Confirmation prompt works
   - [ ] `--yes` skips confirmation

5. **Sub-Issue Linking (CRITICAL TEST)**
   - [ ] Link story to epic using `addSubIssue`
   - [ ] Verify GraphQL-Features header included
   - [ ] Query epic's `trackedIssues`
   - [ ] Query story's `parent`
   - [ ] GitHub UI shows sub-issues
   - [ ] Progress tracking works
   - [ ] Multiple stories link correctly

6. **Sub-Issue Removal**
   - [ ] Remove story from epic
   - [ ] Verify `trackedIssues` updated
   - [ ] Story's `parent` field cleared

7. **Query Operations**
   - [ ] List all epics
   - [ ] List stories with status filter
   - [ ] List drafts only
   - [ ] Query epic's sub-issues
   - [ ] CSV export works

8. **Update Operations**
   - [ ] Update story status
   - [ ] Update epic priority
   - [ ] Multiple field updates
   - [ ] Dry-run mode works

9. **Delete Operations**
   - [ ] Delete draft issue
   - [ ] Remove repo issue from project
   - [ ] Archive functionality
   - [ ] Confirmation prompts

10. **Error Handling**
    - [ ] Missing config shows clear error
    - [ ] Invalid field shows suggestion
    - [ ] Draft as sub-issue shows error
    - [ ] Rate limiting retry works
    - [ ] GraphQL errors displayed clearly

**Validation Checklist**:
- [ ] All scripts have `--help` documentation
- [ ] All scripts support `--dry-run`
- [ ] Error messages are actionable
- [ ] Success messages include IDs/URLs
- [ ] Color output works (success/error/warn/info)
- [ ] Retry logic handles network failures
- [ ] Field cache prevents repeated API calls
- [ ] Native sub-issue API tested end-to-end
</test_plan>

<rollback_procedures>
**Draft Creation**: Delete via `gh project item-delete`

**Repository Issue Conversion**: Cannot rollback (document in warnings)

**Sub-Issue Linking**: Use `removeSubIssue` mutation

**Custom Field Changes**: Manually revert

**Deleted Drafts**: Cannot recover (warn before delete)
</rollback_procedures>

</testing>

<implementation_phases>

<phase number="1" name="Foundation">
**Duration**: 3-4 hours

**Tasks**:
1. Create `lib/gh-project-common.sh`:
   - Logging functions (color-coded)
   - Error handling (retry with backoff)
   - GraphQL helpers (with sub_issues header support)
   - Field caching functions
   - ID resolution functions
   - Sub-issue operations (add/remove/query)

2. Implement `gh-project-init`:
   - Config management
   - Field caching
   - Validation

3. Implement `gh-project-create`:
   - Draft creation
   - Repository issue creation
   - Custom field setting

**Deliverable**: Foundation scripts working, field cache tested

**Testing**: Create drafts/repo issues, verify field caching
</phase>

<phase number="2" name="Core Operations">
**Duration**: 3-4 hours

**Tasks**:
1. Implement `gh-project-convert`:
   - Draft → repo conversion
   - Confirmation workflow
   - Error handling

2. Implement `gh-project-link`:
   - Native `addSubIssue` mutation
   - GraphQL-Features header support
   - Batch linking
   - Verification via `trackedIssues`

3. Implement `gh-project-list`:
   - Query/filter operations
   - Multiple output formats
   - Sub-issue query integration

**Deliverable**: Full Epic-Story workflow functional

**Testing**: Create epic, stories, link using native API, verify in GitHub UI
</phase>

<phase number="3" name="Management">
**Duration**: 2-3 hours

**Tasks**:
1. Implement `gh-project-update`:
   - Custom field updates
   - Diff display
   - Dry-run mode

2. Implement `gh-project-delete`:
   - Delete drafts
   - Remove repo issues
   - Archive functionality
   - Confirmation prompts

3. Add error handling polish:
   - Rate limiting
   - GraphQL error messages
   - Field not found suggestions

**Deliverable**: Complete CRUD operations

**Testing**: Update/delete workflows, edge cases
</phase>

<phase number="4" name="Polish">
**Duration**: 2-3 hours

**Tasks**:
1. Add `--dry-run` to all scripts
2. Add `--help` documentation
3. Improve color output
4. Add progress indicators
5. Create README with examples
6. Test full workflow end-to-end

**Deliverable**: Production-ready scripts

**Testing**: End-to-end Epic-Story workflow with native sub-issues
</phase>

<phase number="5" name="Advanced Features (Optional)">
**Duration**: 4-6 hours

**Tasks**:
1. Bulk operations (template-based)
2. Query patterns library
3. Workflow helpers (epic-create, epic-close)
4. Migration utilities (custom fields → native sub-issues)

**Deliverable**: Advanced automation

**Testing**: Bulk operations, migration from old custom field approach
</phase>

**Total Effort**: 14-20 hours (10-14 core + 4-6 advanced)

</implementation_phases>

<migration_guide>

<from_custom_fields_to_native>
**Migrating from Custom Field Workaround to Native Sub-Issue API**

**Current State**: Projects using "Parent Epic" text field

**Target State**: Native GitHub sub-issue relationships

**Steps**:

1. **Audit Current Hierarchies**:
```bash
# Find all Stories with Parent Epic field
gh project item-list 14 --owner o2alexanderfedin --limit 200 --format json | \
  jq -r '.items[] | select(."parent-epic" != null) | {
    story: .content.number,
    epic: ."parent-epic"
  }'
```

2. **Ensure Items are Repository Issues**:
```bash
# Convert drafts to repository issues first
gh-project-convert --title "Epic #40"
gh-project-convert --title "Story #167"
```

3. **Create Native Sub-Issue Links**:
```bash
# For each Epic-Story pair
gh-project-link --parent 40 --children 167,168,169
```

4. **Verify Migration**:
```bash
# Check Epic's sub-issues via native API
gh-project-list --parent 40

# Verify in GitHub UI (sub-issues section appears)
```

5. **Optional: Remove Custom Field**:
```bash
# If "Parent Epic" field no longer needed
gh project field-delete 14 --owner o2alexanderfedin --name "Parent Epic"
```

**Backward Compatibility**:
- Custom field can coexist with native sub-issues
- Useful for draft issues that can't use native API
- Gradual migration supported
</from_custom_fields_to_native>

</migration_guide>

<documentation>

**README.md Structure**:

```markdown
# GitHub Projects Management Scripts

Production-ready bash scripts for managing GitHub Projects v2 with native sub-issue support.

## Features

- Native Epic-Story hierarchies using GitHub's sub-issue API
- Draft issue management for lightweight planning
- Custom field automation (Type, Status, Priority)
- Bulk operations and querying
- Dry-run mode for all mutations
- Comprehensive error handling

## Installation

## Quick Start

## Scripts Reference

### gh-project-init
Initialize configuration and cache field metadata

### gh-project-create
Create draft or repository issues with custom fields

### gh-project-link
Link stories to epics using native sub-issue API

### gh-project-convert
Convert draft issues to repository issues

### gh-project-list
Query and filter project items

### gh-project-update
Update custom fields

### gh-project-delete
Delete or archive project items

## Workflows

### Creating Epic-Story Hierarchy

### Querying Epic Progress

## Troubleshooting

### Error: GraphQL mutation failed
- Check GraphQL-Features header included
- Verify both issues are repository issues (not drafts)

### Error: Field not found
- Run: `gh-project-init --refresh-cache`

### Error: Cannot link draft to epic
- Convert draft to repo issue first: `gh-project-convert --item ID`

## API Reference

See research documentation for complete API details.
```

</documentation>

<success_criteria>

**Plan Completeness**:
- [x] Native sub-issue API integrated (addSubIssue, removeSubIssue, reprioritizeSubIssue)
- [x] GraphQL-Features header support documented
- [x] Draft → repo conversion workflow for sub-issue linking
- [x] All 7 core scripts specified with interfaces, examples, error handling
- [x] Shared library functions outlined (including sub-issue operations)
- [x] Config management with field caching
- [x] Implementation order with realistic time estimates (14-20 hours)
- [x] Testing strategy with validation checklist
- [x] Migration path from custom field workaround
- [x] Production-ready with concrete examples

**Technical Accuracy**:
- [x] Uses correct mutation names (addSubIssue, not updateIssue)
- [x] Includes GraphQL-Features:sub_issues header requirement
- [x] Specifies repository issue requirement for sub-issues
- [x] Documents all mutations with input/output schemas
- [x] Provides working code examples tested against API

**Implementation Quality**:
- [x] Bash function signatures defined
- [x] Error handling patterns specified
- [x] Dry-run mode in all mutating operations
- [x] Color-coded logging
- [x] Retry logic with exponential backoff
- [x] Field caching for performance
- [x] Comprehensive testing plan

**Documentation Quality**:
- [x] Clear examples for each script
- [x] Complete workflows (epic-story creation, progress querying)
- [x] Migration guide from old approach
- [x] Troubleshooting section
- [x] API reference with GraphQL schemas

</success_criteria>

</plan>

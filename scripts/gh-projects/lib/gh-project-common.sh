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

  execute_graphql "
    query {
      node(id: \"$project_item_id\") {
        ... on ProjectV2Item {
          content {
            ... on DraftIssue {
              id
            }
          }
        }
      }
    }
  " | jq -r '.data.node.content.id // empty'
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
      --format json > /dev/null
}

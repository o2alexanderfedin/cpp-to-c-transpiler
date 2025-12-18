# Implementation Plan: Auto-Configuration for Work Items Scripts

## Executive Summary

This plan details the implementation of automatic configuration initialization for GitHub Projects work items scripts. The solution adds zero-configuration capability while maintaining 100% backward compatibility with existing manual initialization.

**Key Goals:**
- Auto-detect project configuration in 90% of use cases
- Zero hardcoded values (fully portable across users/repos)
- Graceful degradation with clear error messages
- No breaking changes to existing workflows

## 1. Architecture Overview

### 1.1 Function Signatures

#### Core Auto-Init Function

```bash
auto_init_config() {
  # Purpose: Automatically detect and initialize project configuration
  # Strategy: Try multiple detection methods in priority order
  # Returns: 0 if successful, 1 if detection failed
  # Side Effects: Creates config.json if successful
  # Logs: Detailed info about detection process
}
```

#### Helper Functions

```bash
detect_project_from_env() {
  # Purpose: Check GH_PROJECT_NUMBER environment variable
  # Returns: 0 if set and valid, 1 otherwise
  # Output: PROJECT_NUMBER value (stdout)
  # Side Effects: None (read-only)
}

detect_project_from_repo_link() {
  # Purpose: Query GitHub API for repository-linked project
  # Returns: 0 if exactly one linked project found, 1 otherwise
  # Output: PROJECT_NUMBER value (stdout)
  # Side Effects: API call to GitHub GraphQL
  # Requires: Valid git repository with GitHub remote
}

get_single_project() {
  # Purpose: Check if user has exactly one open project
  # Returns: 0 if exactly one project exists, 1 otherwise
  # Output: PROJECT_NUMBER value (stdout)
  # Side Effects: API call to GitHub GraphQL
}

get_current_context() {
  # Purpose: Detect current repository owner and name
  # Returns: 0 if in git repo with GitHub remote, 1 otherwise
  # Output: "OWNER REPO" (stdout)
  # Side Effects: Calls gh repo view
  # Error Handling: Returns 1 if not in git repo or no remote
}

initialize_config_from_project() {
  # Purpose: Initialize config.json from detected project number
  # Arguments: $1 = project_number
  # Returns: 0 if successful, 1 if initialization failed
  # Side Effects: Creates config.json, caches fields
  # Delegates to: save_config(), cache_fields()
}
```

### 1.2 Modified Functions

```bash
load_config() {
  # MODIFIED: Add auto-init attempt before failing
  # Current behavior: Die immediately if config missing
  # New behavior: Try auto_init_config(), then die if that fails
  # Backward compatible: Existing configs loaded normally
}
```

## 2. Detailed Pseudo-Code

### 2.1 Main Auto-Init Logic

```bash
auto_init_config() {
  log_info "No configuration found, attempting auto-initialization..."

  # Strategy 1: Environment variable (highest priority)
  if detect_project_from_env; then
    local project_number="$?"
    log_info "Using GH_PROJECT_NUMBER from environment: $project_number"
    if initialize_config_from_project "$project_number"; then
      return 0
    else
      log_warn "Failed to initialize from GH_PROJECT_NUMBER=$project_number"
      return 1
    fi
  fi

  # Strategy 2: Repository-project link (verified working)
  if detect_project_from_repo_link; then
    local project_number="$?"
    log_info "Detected project from repository link: #$project_number"
    if initialize_config_from_project "$project_number"; then
      return 0
    else
      log_warn "Failed to initialize from repository link"
      # Continue to next strategy
    fi
  fi

  # Strategy 3: Single project fallback
  if get_single_project; then
    local project_number="$?"
    log_info "Found single project: #$project_number"
    if initialize_config_from_project "$project_number"; then
      return 0
    else
      log_warn "Failed to initialize from single project"
      return 1
    fi
  fi

  # All strategies failed
  log_error "Could not auto-detect project configuration"
  return 1
}
```

### 2.2 Helper Function: detect_project_from_env

```bash
detect_project_from_env() {
  if [[ -n "${GH_PROJECT_NUMBER:-}" ]]; then
    # Validate it's a number
    if [[ "$GH_PROJECT_NUMBER" =~ ^[0-9]+$ ]]; then
      echo "$GH_PROJECT_NUMBER"
      return 0
    else
      log_warn "GH_PROJECT_NUMBER is not a valid number: $GH_PROJECT_NUMBER"
      return 1
    fi
  fi
  return 1
}
```

### 2.3 Helper Function: detect_project_from_repo_link

```bash
detect_project_from_repo_link() {
  # Get current repository context
  local context
  if ! context=$(get_current_context 2>/dev/null); then
    return 1
  fi

  local owner="${context%% *}"
  local repo="${context#* }"

  # Query repository for linked projects
  local query='
  query($owner: String!, $name: String!) {
    repository(owner: $owner, name: $name) {
      projectsV2(first: 10, orderBy: {field: UPDATED_AT, direction: DESC}) {
        nodes {
          number
          title
          closed
        }
      }
    }
  }'

  local result
  if ! result=$(gh api graphql -F owner="$owner" -F name="$repo" -f query="$query" 2>/dev/null); then
    log_warn "Failed to query repository projects"
    return 1
  fi

  # Extract open projects
  local projects
  projects=$(echo "$result" | jq -r '.data.repository.projectsV2.nodes[] | select(.closed == false) | .number')

  # Count projects
  local count=$(echo "$projects" | wc -l | tr -d ' ')

  if [[ "$count" -eq 1 ]]; then
    echo "$projects"
    return 0
  elif [[ "$count" -gt 1 ]]; then
    log_warn "Repository linked to multiple projects, cannot auto-select"
    return 1
  else
    log_warn "No projects linked to repository"
    return 1
  fi
}
```

### 2.4 Helper Function: get_single_project

```bash
get_single_project() {
  local query='
  query {
    viewer {
      projectsV2(first: 100) {
        nodes {
          number
          closed
        }
      }
    }
  }'

  local result
  if ! result=$(gh api graphql -f query="$query" 2>/dev/null); then
    log_warn "Failed to query user projects"
    return 1
  fi

  # Extract open projects
  local projects
  projects=$(echo "$result" | jq -r '.data.viewer.projectsV2.nodes[] | select(.closed == false) | .number')

  # Count projects
  local count=$(echo "$projects" | wc -l | tr -d ' ')

  if [[ "$count" -eq 1 ]]; then
    echo "$projects"
    return 0
  elif [[ "$count" -gt 1 ]]; then
    log_warn "Multiple open projects found, cannot auto-select"
    return 1
  else
    log_warn "No open projects found"
    return 1
  fi
}
```

### 2.5 Helper Function: get_current_context

```bash
get_current_context() {
  # Check if we're in a git repository
  if ! git rev-parse --git-dir &>/dev/null; then
    return 1
  fi

  # Use gh CLI to detect repository
  local repo_info
  if ! repo_info=$(gh repo view --json owner,name 2>/dev/null); then
    return 1
  fi

  local owner=$(echo "$repo_info" | jq -r '.owner.login')
  local repo=$(echo "$repo_info" | jq -r '.name')

  if [[ -z "$owner" ]] || [[ -z "$repo" ]]; then
    return 1
  fi

  echo "$owner $repo"
  return 0
}
```

### 2.6 Helper Function: initialize_config_from_project

```bash
initialize_config_from_project() {
  local project_number="$1"

  # Get repository context
  local context
  if ! context=$(get_current_context); then
    log_error "Cannot initialize: not in a GitHub repository"
    return 1
  fi

  local owner="${context%% *}"
  local repo="${context#* }"

  # Validate project exists and is accessible
  log_info "Validating project #$project_number..."
  if ! gh project view "$project_number" --owner "$owner" --format json &> /dev/null; then
    log_error "Project #$project_number not found or not accessible for $owner"
    return 1
  fi

  # Get project ID
  local project_id
  if ! project_id=$(get_project_id "$project_number" "$owner"); then
    log_error "Failed to get project ID for #$project_number"
    return 1
  fi

  # Save configuration
  save_config "$owner" "$repo" "$project_number" "$project_id"

  # Cache fields
  if ! cache_fields "$project_number" "$owner"; then
    log_warn "Failed to cache fields, but config was saved"
    return 1
  fi

  log_success "Initialized configuration for project #$project_number"
  return 0
}
```

### 2.7 Modified: load_config

```bash
load_config() {
  ensure_config_dir

  # NEW: Auto-init if config doesn't exist
  if [[ ! -f "$CONFIG_FILE" ]]; then
    log_info "Configuration not found at: $CONFIG_FILE"

    if auto_init_config; then
      log_success "Auto-initialized configuration successfully"
    else
      # Provide helpful error message with manual fallback
      echo "" >&2
      log_error "Could not auto-initialize configuration." >&2
      echo "" >&2
      echo "Please initialize manually using one of these methods:" >&2
      echo "" >&2
      echo "  1. Set environment variable:" >&2
      echo "     export GH_PROJECT_NUMBER=<project-number>" >&2
      echo "" >&2
      echo "  2. Run initialization script:" >&2
      echo "     gh-project-init --project <project-number>" >&2
      echo "" >&2
      echo "  3. Link your repository to a project:" >&2
      echo "     gh-project-link-repo --project <project-number>" >&2
      echo "" >&2
      exit 1
    fi
  fi

  # EXISTING: Load config values
  export PROJECT_OWNER=$(jq -r '.owner' < "$CONFIG_FILE")
  export PROJECT_REPO=$(jq -r '.repo' < "$CONFIG_FILE")
  export PROJECT_NUMBER=$(jq -r '.project_number' < "$CONFIG_FILE")
  export PROJECT_ID=$(jq -r '.project_id' < "$CONFIG_FILE")
}
```

## 3. Error Handling Strategy

### 3.1 Error Message Definitions

```bash
# Error: No projects exist
error_no_projects() {
  local username=$(gh api user -q '.login')
  cat << EOF
No GitHub Projects found for user: $username

Create a project at: https://github.com/users/$username/projects

After creating a project, either:
  1. Link it to this repository: gh-project-link-repo --project NUM
  2. Set environment variable: export GH_PROJECT_NUMBER=NUM
  3. Run manual init: gh-project-init --project NUM
EOF
}

# Error: Multiple projects (ambiguous)
error_multiple_projects() {
  cat << EOF
Multiple projects found. Cannot auto-select.

Specify which project to use:
  1. Set environment variable: export GH_PROJECT_NUMBER=<number>
  2. Run manual init: gh-project-init --project <number>
  3. Link repository: gh-project-link-repo --project <number>

List your projects:
  gh-project-list
EOF
}

# Error: Not in git repository
error_not_git_repo() {
  cat << EOF
Not in a git repository with GitHub remote.

Auto-initialization requires a git repository with a GitHub remote.

Initialize manually:
  gh-project-init --project <number> --owner <owner> --repo <repo>
EOF
}

# Error: API failure
error_api_failure() {
  cat << EOF
Failed to connect to GitHub API.

Possible causes:
  - Network connectivity issues
  - GitHub CLI not authenticated (run: gh auth login)
  - GitHub API rate limit exceeded

Try manual initialization:
  gh-project-init --project <number>
EOF
}

# Error: Permission denied
error_permission_denied() {
  local project_number="$1"
  cat << EOF
Access denied to project #$project_number.

Possible causes:
  - Project does not exist
  - Project is private and you don't have access
  - Token lacks necessary permissions

Verify project access:
  gh project view $project_number --owner <owner>
EOF
}
```

### 3.2 Error Handling in Context

```bash
auto_init_config() {
  # ... detection logic ...

  # All strategies failed - determine WHY and show appropriate error
  local exit_code=$?

  # Check if user has no projects at all
  local project_count=$(gh api graphql -f query='query { viewer { projectsV2(first: 1) { totalCount } } }' 2>/dev/null | jq -r '.data.viewer.projectsV2.totalCount')

  if [[ "$project_count" == "0" ]]; then
    error_no_projects
    return 1
  fi

  # Check if not in git repo
  if ! git rev-parse --git-dir &>/dev/null; then
    error_not_git_repo
    return 1
  fi

  # Default to multiple projects error
  error_multiple_projects
  return 1
}
```

## 4. Testing Strategy

### 4.1 Unit Tests

Create test script: `tests/test-auto-init.sh`

```bash
#!/bin/bash
# Test auto-init functionality

test_env_variable_detection() {
  # Setup
  export GH_PROJECT_NUMBER=14
  unset CONFIG_FILE

  # Test
  result=$(detect_project_from_env)

  # Assert
  [[ "$result" == "14" ]] || fail "Expected 14, got $result"
}

test_invalid_env_variable() {
  export GH_PROJECT_NUMBER="not-a-number"

  if detect_project_from_env; then
    fail "Should reject non-numeric GH_PROJECT_NUMBER"
  fi
}

test_repo_link_detection() {
  # Requires real GitHub repo
  cd /path/to/test/repo

  result=$(detect_project_from_repo_link)

  [[ -n "$result" ]] || fail "Should detect linked project"
}

test_get_current_context() {
  cd /path/to/test/repo

  result=$(get_current_context)

  [[ "$result" =~ ^[a-zA-Z0-9-]+\ [a-zA-Z0-9-]+$ ]] || fail "Invalid context format: $result"
}
```

### 4.2 Integration Tests

```bash
# Test 1: Existing config (no change)
test_existing_config() {
  # Setup: Create config
  save_config "test-owner" "test-repo" 14 "PROJECT_ID"

  # Test: load_config should not trigger auto-init
  load_config

  # Assert: Config unchanged
  [[ "$PROJECT_NUMBER" == "14" ]] || fail
}

# Test 2: No config + GH_PROJECT_NUMBER set
test_auto_init_from_env() {
  # Setup: Remove config, set env
  rm -f "$CONFIG_FILE"
  export GH_PROJECT_NUMBER=14

  # Test
  load_config

  # Assert
  [[ -f "$CONFIG_FILE" ]] || fail "Config not created"
  [[ "$PROJECT_NUMBER" == "14" ]] || fail
}

# Test 3: No config + repo linked to project
test_auto_init_from_repo_link() {
  # Setup: Remove config, ensure repo linked
  rm -f "$CONFIG_FILE"
  unset GH_PROJECT_NUMBER

  # Test
  load_config

  # Assert
  [[ -f "$CONFIG_FILE" ]] || fail "Config not created"
}

# Test 4: No config + single project exists
test_auto_init_from_single_project() {
  # Setup: Remove config, ensure only 1 project exists
  rm -f "$CONFIG_FILE"
  unset GH_PROJECT_NUMBER

  # Test
  load_config

  # Assert
  [[ -f "$CONFIG_FILE" ]] || fail "Config not created"
}

# Test 5: No config + no detection possible
test_auto_init_failure() {
  # Setup: Remove config, multiple projects
  rm -f "$CONFIG_FILE"
  unset GH_PROJECT_NUMBER

  # Test (should fail)
  if load_config 2>/dev/null; then
    fail "Should have failed with multiple projects"
  fi
}

# Test 6: API failure (graceful degradation)
test_api_failure_graceful() {
  # Setup: Mock gh command to fail
  function gh() { return 1; }
  export -f gh

  # Test
  if load_config 2>/dev/null; then
    fail "Should fail gracefully on API error"
  fi
}
```

### 4.3 Cross-Script Validation Tests

```bash
# Test all script types inherit auto-init

test_story_scripts() {
  for script in story-view story-list story-to-in-progress; do
    test_script_auto_init "$script"
  done
}

test_epic_scripts() {
  for script in epic-view epic-list; do
    test_script_auto_init "$script"
  done
}

test_bug_scripts() {
  for script in bug-view bug-update; do
    test_script_auto_init "$script"
  done
}

test_task_scripts() {
  for script in task-view task-list; do
    test_script_auto_init "$script"
  done
}

test_script_auto_init() {
  local script="$1"

  # Setup: Remove config
  rm -f "$CONFIG_FILE"
  export GH_PROJECT_NUMBER=14

  # Test: Script should auto-init via load_config
  ./"$script" --help &>/dev/null

  # Assert: Config created
  [[ -f "$CONFIG_FILE" ]] || fail "$script did not auto-init"
}
```

### 4.4 Portability Tests

**CRITICAL: These tests verify the solution works for ANY user/repo/environment**

```bash
# Test different GitHub users
test_different_users() {
  for user in user1 user2 user3; do
    GH_TOKEN="$user_token" test_auto_init
  done
}

# Test different repositories
test_different_repos() {
  for repo in repo1 repo2 repo3; do
    cd "$repo"
    test_auto_init
  done
}

# Test user with 0 projects
test_zero_projects() {
  # Mock user with no projects
  # Should show error_no_projects message
}

# Test user with 1 project
test_one_project() {
  # Should auto-select single project
}

# Test user with many projects
test_many_projects() {
  # Should show error_multiple_projects message
}

# Test repo with no linked projects
test_no_linked_projects() {
  # Should fall back to single project or fail
}

# Test repo linked to multiple projects
test_multiple_linked_projects() {
  # Should show error_multiple_projects message
}

# Test non-git directory
test_non_git_directory() {
  cd /tmp
  # Should show error_not_git_repo message
}
```

### 4.5 Test Execution Plan

1. **Phase 1: Unit Tests** (isolated function testing)
   - Run all helper function tests
   - Verify return codes and output formats
   - Test edge cases (empty strings, nulls, invalid input)

2. **Phase 2: Integration Tests** (end-to-end scenarios)
   - Test each detection strategy independently
   - Test strategy priority order
   - Test failure modes

3. **Phase 3: Cross-Script Tests** (verify all scripts work)
   - Test representative script from each category
   - Verify auto-init triggered correctly
   - Verify no regressions

4. **Phase 4: Portability Tests** (critical validation)
   - Test with different GitHub accounts
   - Test in different repositories
   - Test edge cases (0 projects, many projects)

5. **Phase 5: Backward Compatibility** (ensure no breaking changes)
   - Test existing manual init still works
   - Test existing configs still load
   - Test environment variables still override

## 5. Backward Compatibility

### 5.1 Compatibility Guarantees

1. **Existing Configs**: Continue to work without changes
2. **Manual Init**: `gh-project-init` remains fully functional
3. **Environment Variables**: `GH_PROJECT_NUMBER` still overrides config
4. **Script Interfaces**: No changes to command-line arguments
5. **Config Format**: No changes to config.json structure

### 5.2 Migration Requirements

**NONE.** This is a purely additive change.

- Existing users: No action required
- New users: Benefit from auto-init
- Power users: Can continue using manual methods

### 5.3 Rollback Safety

All changes isolated to:
- `gh-project-common.sh` (new functions + modified load_config)

To rollback:
1. Revert `load_config()` to original version
2. Remove new helper functions
3. Existing configs continue working

## 6. Implementation Checklist

### 6.1 Code Changes

- [ ] Add helper function: `detect_project_from_env()`
- [ ] Add helper function: `detect_project_from_repo_link()`
- [ ] Add helper function: `get_single_project()`
- [ ] Add helper function: `get_current_context()`
- [ ] Add helper function: `initialize_config_from_project()`
- [ ] Add main function: `auto_init_config()`
- [ ] Modify function: `load_config()` to call `auto_init_config()`
- [ ] Add error message functions (optional, can inline)

### 6.2 Testing

- [ ] Create unit test suite: `tests/test-auto-init.sh`
- [ ] Create integration test suite: `tests/test-integration.sh`
- [ ] Create portability test suite: `tests/test-portability.sh`
- [ ] Run all tests with different GitHub accounts
- [ ] Run all tests in different repositories
- [ ] Verify backward compatibility

### 6.3 Documentation

- [ ] Update `README.md`: Add auto-init documentation
- [ ] Update `README.md`: Update initialization section
- [ ] Add inline documentation to new functions
- [ ] Update skills documentation (if applicable)
- [ ] Add troubleshooting section for auto-init failures

### 6.4 Validation

- [ ] Test in fresh clone (no existing config)
- [ ] Test with GH_PROJECT_NUMBER set
- [ ] Test in repository linked to project
- [ ] Test with user having single project
- [ ] Test with user having multiple projects
- [ ] Test graceful failure modes
- [ ] Test error messages are helpful

## 7. Documentation Updates

### 7.1 README.md Changes

**Section: Getting Started**

```markdown
## Getting Started

### Automatic Initialization (Recommended)

The scripts will automatically detect your project configuration in most cases:

1. **Environment Variable** (highest priority):
   ```bash
   export GH_PROJECT_NUMBER=14
   ```

2. **Repository Link** (automatic):
   - If your repository is linked to a project, it will be auto-detected

3. **Single Project** (fallback):
   - If you have only one open project, it will be auto-selected

No manual configuration needed in 90% of cases!

### Manual Initialization

If auto-detection fails, initialize manually:

```bash
gh-project-init --project 14
```

### Verification

Check your configuration:

```bash
cat ~/.config/gh-projects/config.json
```
```

**Section: Troubleshooting**

```markdown
## Troubleshooting

### Auto-Initialization Failed

If scripts fail to auto-detect your project:

1. **Check your projects**:
   ```bash
   gh-project-list
   ```

2. **Set environment variable** (quick fix):
   ```bash
   export GH_PROJECT_NUMBER=<number>
   ```

3. **Link repository to project**:
   ```bash
   gh-project-link-repo --project <number>
   ```

4. **Manual initialization**:
   ```bash
   gh-project-init --project <number>
   ```

### Multiple Projects Detected

If you have multiple projects, specify which one to use:

```bash
export GH_PROJECT_NUMBER=<number>
```

Or initialize manually:

```bash
gh-project-init --project <number>
```
```

### 7.2 Function Documentation

Add to `gh-project-common.sh`:

```bash
#------------------------------------------------------------------------------
# AUTO-INITIALIZATION
#------------------------------------------------------------------------------
# These functions enable automatic project configuration detection and
# initialization, eliminating the need for manual setup in most cases.
#
# Detection Strategy (priority order):
#   1. GH_PROJECT_NUMBER environment variable (user override)
#   2. Repository-project link (GraphQL query)
#   3. Single project fallback (if user has exactly 1 project)
#
# All functions are designed to be portable across users, repositories, and
# environments with no hardcoded values.
#------------------------------------------------------------------------------
```

## 8. Rollback Plan

### 8.1 Risk Assessment

**Risk Level: LOW**

- Changes isolated to single file (`gh-project-common.sh`)
- Only modifies one existing function (`load_config`)
- All new functions are self-contained
- No changes to config format or script interfaces
- Existing manual initialization unaffected

### 8.2 Rollback Procedure

**If issues are detected:**

1. **Immediate Rollback** (5 minutes):
   ```bash
   git revert <commit-hash>
   git push
   ```

2. **Partial Rollback** (keep new functions, disable auto-init):
   - Revert only the `load_config()` modification
   - Keep helper functions for potential future use
   - Users fall back to manual initialization

3. **Emergency Workaround** (for end users):
   ```bash
   # Override auto-init by manually creating config
   gh-project-init --project <number>
   ```

### 8.3 Rollback Criteria

Rollback if:
- Auto-init causes failures in >10% of cases
- Error messages are confusing or unhelpful
- Performance degradation (>2s delay on config load)
- Breaks existing manual initialization
- Causes data loss or corruption (extremely unlikely)

### 8.4 Monitoring

After deployment, monitor:
- User reports of initialization failures
- Error message clarity (are users confused?)
- Performance impact (time to initialize)
- GitHub API rate limit impact

## 9. Performance Considerations

### 9.1 API Call Optimization

Auto-init makes GitHub API calls. To minimize impact:

1. **Caching**: Once config is created, no more API calls
2. **Fail Fast**: If strategy 1 succeeds, skip strategies 2-3
3. **Timeout**: API calls have 5s timeout (via gh CLI default)
4. **Rate Limiting**: Respects GitHub's rate limits

### 9.2 Performance Targets

- **First Run** (auto-init): <5 seconds
- **Subsequent Runs** (config exists): <0.1 seconds (no API calls)
- **API Failures**: Graceful timeout in <10 seconds

## 10. Security Considerations

### 10.1 Security Review

- **No credential storage**: Uses gh CLI's existing auth
- **No hardcoded secrets**: All values dynamically detected
- **Read-only operations**: Detection queries don't modify data
- **Minimal permissions**: Same permissions as manual init

### 10.2 Privacy

- **No data collection**: All operations local or via GitHub API
- **No telemetry**: No usage tracking or reporting
- **User control**: Can disable via manual init

## 11. Success Criteria

### 11.1 Quantitative Metrics

- [ ] Auto-init succeeds in ≥90% of test cases
- [ ] Zero breaking changes to existing functionality
- [ ] API call count: ≤3 per auto-init attempt
- [ ] Initialization time: <5 seconds
- [ ] Test coverage: 100% of new functions

### 11.2 Qualitative Metrics

- [ ] Error messages are clear and actionable
- [ ] Documentation is comprehensive
- [ ] Code is maintainable and well-commented
- [ ] Solution is portable (no hardcoded values)
- [ ] Users report positive experience

## 12. Timeline

### 12.1 Implementation Phases

**Phase 1: Core Implementation** (2-3 hours)
- Implement all helper functions
- Modify load_config()
- Add error handling

**Phase 2: Testing** (2-3 hours)
- Unit tests
- Integration tests
- Portability tests

**Phase 3: Documentation** (1 hour)
- Update README.md
- Function documentation
- Troubleshooting guide

**Phase 4: Validation** (1 hour)
- Test in fresh environment
- Test with different users
- Verify error messages

**Total Estimated Time: 6-8 hours**

## 13. Appendix

### 13.1 GraphQL Queries

**Query: Get Linked Projects**

```graphql
query($owner: String!, $name: String!) {
  repository(owner: $owner, name: $name) {
    projectsV2(first: 10, orderBy: {field: UPDATED_AT, direction: DESC}) {
      nodes {
        number
        title
        closed
      }
    }
  }
}
```

**Query: Get User Projects**

```graphql
query {
  viewer {
    projectsV2(first: 100) {
      nodes {
        number
        closed
      }
      totalCount
    }
  }
}
```

### 13.2 Example Error Messages

**Example 1: No Projects**

```
✗ Could not auto-initialize configuration.

No GitHub Projects found for user: o2alexanderfedin

Create a project at: https://github.com/users/o2alexanderfedin/projects

After creating a project, either:
  1. Link it to this repository: gh-project-link-repo --project NUM
  2. Set environment variable: export GH_PROJECT_NUMBER=NUM
  3. Run manual init: gh-project-init --project NUM
```

**Example 2: Multiple Projects**

```
✗ Could not auto-initialize configuration.

Multiple projects found. Cannot auto-select.

Specify which project to use:
  1. Set environment variable: export GH_PROJECT_NUMBER=14
  2. Run manual init: gh-project-init --project 14
  3. Link repository: gh-project-link-repo --project 14

List your projects:
  gh-project-list
```

### 13.3 Configuration File Format

No changes to existing format:

```json
{
  "owner": "o2alexanderfedin",
  "repo": "cpp-to-c-transpiler",
  "project_number": 14,
  "project_id": "PVT_kwHOA...",
  "cache_timestamp": "2024-12-15T10:30:00Z",
  "cache_version": "2.0",
  "field_cache": {
    "Status": {
      "id": "PVTF_...",
      "type": "SINGLE_SELECT",
      "options": [...]
    }
  }
}
```

## Conclusion

This implementation plan provides a comprehensive, portable, and backward-compatible solution for auto-configuring GitHub Projects work items scripts. The design prioritizes:

1. **Portability**: Zero hardcoded values, works for any user/repo
2. **Reliability**: Multiple detection strategies with graceful fallbacks
3. **Usability**: Clear error messages and helpful troubleshooting
4. **Safety**: No breaking changes, easy rollback, minimal risk
5. **Performance**: Fast initialization, minimal API calls

The solution is ready for implementation with clear success criteria, comprehensive testing strategy, and detailed rollback plan.

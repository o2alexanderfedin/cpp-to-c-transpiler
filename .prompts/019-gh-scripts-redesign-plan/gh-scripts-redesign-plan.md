# GitHub Projects Scripts Redesign - Implementation Plan

**Comprehensive phased roadmap for SOLID/KISS/DRY/YAGNI/TRIZ-compliant GitHub Projects CRUD scripts**

v1 • 2025-12-15

---

<implementation_plan>
  <meta>
    <version>v1</version>
    <date>2025-12-15</date>
    <based_on>
      .prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md
    </based_on>
    <confidence>high</confidence>
  </meta>

  <architecture>
    <decisions>
      <script_organization>
        **Decision: Flat resource-operation scripts**

        Pattern: `gh-{resource}-{operation}.sh`

        Rationale:
        - Each script has ONE responsibility (SOLID - Single Responsibility)
        - No complex argument parsing (KISS)
        - Tab-completion friendly
        - Self-documenting filenames
        - No subcommand infrastructure needed

        Rejected alternative: Subcommand style (`gh-epic create`)
        - Would require complex case statements
        - Violates Single Responsibility (one script = multiple operations)
        - Harder to maintain
        - Only needed when 50+ commands (we have ~30)

        **Script count: ~32 total**
        - 1 common library
        - 5 project operations (create, list, view, delete, init)
        - 5 item types × 5 operations = 25 item scripts
        - 1 configuration helper

        Benefits:
        ✅ Each script under 100 lines
        ✅ Simple to understand
        ✅ Hard to misuse
        ✅ Easy to test
      </script_organization>

      <naming_convention>
        **Pattern: `gh-{resource}-{operation}.sh`**

        Resources:
        - `project` - GitHub Project itself
        - `epic` - Epic items (Type=Epic)
        - `story` - User Story items (Type="User Story")
        - `task` - Task items (Type=Task)
        - `spike` - Spike items (Type=Spike)
        - `bug` - Bug items (Type=Bug)

        Operations (CRUD):
        - `create` - Create new resource
        - `list` - List resources (read multiple)
        - `view` - View single resource details (read one)
        - `update` - Update resource fields
        - `delete` - Delete/remove resource

        Special operations:
        - `init` - Initialize project configuration

        Examples:
        - `gh-project-create.sh` - Create a new GitHub Project
        - `gh-epic-create.sh` - Create an Epic (repo issue + project item)
        - `gh-story-list.sh` - List all User Stories (Type="User Story")
        - `gh-task-update.sh` - Update Task fields (status, priority)
        - `gh-project-init.sh` - Initialize configuration

        Consistency rules:
        - Lowercase resource names (epic, not Epic)
        - Singular resources (epic, not epics)
        - Standard CRUD verbs (create/list/view/update/delete)
        - Always .sh extension
        - Always executable (chmod +x)
      </naming_convention>

      <configuration>
        **Multi-tier configuration with precedence**

        Precedence (highest to lowest):
        1. Command-line flags (--project NUM, --owner NAME)
        2. Environment variables (GH_PROJECT_NUMBER, GH_PROJECT_OWNER)
        3. Config file (~/.config/gh-projects/config.json)
        4. Auto-detection (git remote, gh auth status)
        5. Error (fail with helpful message)

        **Config file format:**
        Location: `~/.config/gh-projects/config.json`

        ```json
        {
          "version": "2.0",
          "owner": "alexanderfedin",
          "repo": "hupyy-cpp-to-c",
          "project_number": 1,
          "project_id": "PVT_kwDOA...",
          "cache_timestamp": "2025-12-15T10:30:00Z",
          "field_cache": {
            "status": {
              "id": "PVTF_lADOA...",
              "type": "SINGLE_SELECT",
              "options": [
                {"id": "opt_123", "name": "Todo"},
                {"id": "opt_456", "name": "In Progress"},
                {"id": "opt_789", "name": "Done"}
              ]
            },
            "priority": {
              "id": "PVTF_lADOB...",
              "type": "SINGLE_SELECT",
              "options": [
                {"id": "opt_111", "name": "Low"},
                {"id": "opt_222", "name": "Medium"},
                {"id": "opt_333", "name": "High"},
                {"id": "opt_444", "name": "Critical"}
              ]
            },
            "type": {
              "id": "PVTF_lADOC...",
              "type": "SINGLE_SELECT",
              "options": [
                {"id": "opt_e1", "name": "Epic"},
                {"id": "opt_s1", "name": "User Story"},
                {"id": "opt_t1", "name": "Task"},
                {"id": "opt_b1", "name": "Bug"},
                {"id": "opt_p1", "name": "Spike"}
              ]
            }
          }
        }
        ```

        **Environment variable overrides:**
        - `GH_PROJECT_NUMBER` - Override project number for one command
        - `GH_PROJECT_OWNER` - Override owner
        - `GH_PROJECT_REPO` - Override repository
        - `GH_PROJECT_CONFIG` - Use alternate config file

        **Initialization:**
        Run once per project: `gh-project-init.sh --project 1`
        - Auto-detects owner from `gh auth status`
        - Auto-detects repo from git remote
        - Fetches and caches field metadata
        - Saves to config file

        **Field caching rationale:**
        - GitHub API requires field IDs and option IDs (not names)
        - Fetching fields on every operation is slow + rate-limited
        - Fields rarely change after project setup
        - Cache eliminates repeated API calls
        - Auto-refresh on field not found error

        **CRITICAL: Field name normalization**
        - UI shows: "Type", "Status", "Priority" (PascalCase)
        - JSON uses: "type", "status", "priority" (lowercase)
        - Common library normalizes to lowercase always
        - Prevents case-sensitivity bugs (discovered in prompt 015)
      </configuration>

      <common_library>
        **Location:** `~/.claude/skills/lib/gh-projects/lib/gh-project-common.sh`

        **Sourcing pattern:**
        ```bash
        #!/usr/bin/env bash
        set -euo pipefail

        SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
        source "$SCRIPT_DIR/lib/gh-project-common.sh"

        # Script code here...
        ```

        **Responsibilities:**

        1. **Configuration management**
           - `load_config()` - Load from file with env var override
           - `save_config()` - Write config file
           - `auto_detect_config()` - Detect from git/gh
           - `get_config_value(key)` - Get single value

        2. **Field operations**
           - `cache_fields()` - Fetch and cache all field metadata
           - `get_field_id(field_name)` - Lookup field ID (lowercase normalized)
           - `get_option_id(field_name, option_name)` - Lookup option ID
           - `normalize_field_name(name)` - Convert to lowercase

        3. **API wrappers**
           - `gh_api()` - Wrapper ensuring PATH correct
           - `retry_command()` - Execute with retries
           - `execute_graphql()` - GraphQL query execution

        4. **Error handling**
           - `die(message, [exit_code])` - Exit with error
           - `validate_prerequisites()` - Check gh, jq, auth
           - `validate_config()` - Ensure config loaded

        5. **Logging**
           - `log_success(message)` - Green success message (stderr)
           - `log_error(message)` - Red error message (stderr)
           - `log_warn(message)` - Yellow warning (stderr)
           - `log_info(message)` - Blue info (stderr)

        6. **High-level operations** (NEW in redesign)
           - `create_repo_issue(title, body, labels, assignee)` - Create + return URL
           - `add_issue_to_project(issue_url)` - Add to project + return item_id
           - `set_item_field(item_id, field_name, value)` - Update single field
           - `get_item_by_issue(issue_num)` - Find item_id from issue number
           - `list_items_by_type(type, limit)` - Filter items by Type field

        **What DOES NOT belong in common library:**
        - Argument parsing (each script has different args)
        - Help text (each script unique)
        - Script-specific validation
        - Output formatting (script's choice)

        **DRY vs duplication tradeoff:**
        ✅ Abstract: Repeated patterns (create issue + add to project)
        ✅ Abstract: API calls, error handling, config loading
        ❌ Don't abstract: Single-line validations
        ❌ Don't abstract: Help text structure
        ❌ Don't abstract: Argument parsing patterns
      </common_library>

      <path_handling>
        **CRITICAL FIX: Resolve PATH issues in restricted environments**

        Problem discovered in prompt 015:
        - Skills run in restricted environment with limited PATH
        - `gh` CLI not found even when installed
        - Temporary workaround: hardcoded PATH in common library

        **Permanent solution:**
        Common library exports wrapper function:

        ```bash
        # In gh-project-common.sh
        gh() {
          # Ensure gh is in PATH by checking common locations
          local gh_cmd=""
          if command -v gh &>/dev/null; then
            gh_cmd="gh"
          elif [[ -x "/opt/homebrew/bin/gh" ]]; then
            gh_cmd="/opt/homebrew/bin/gh"
          elif [[ -x "/usr/local/bin/gh" ]]; then
            gh_cmd="/usr/local/bin/gh"
          else
            die "GitHub CLI (gh) not found. Install: https://cli.github.com/"
          fi

          "$gh_cmd" "$@"
        }
        ```

        All scripts use `gh` function from common library.
        No hardcoded PATH needed.
        Searches standard locations automatically.
      </path_handling>
    </decisions>

    <directory_structure>
      ```
      ~/.claude/skills/lib/gh-projects/
      ├── lib/
      │   └── gh-project-common.sh           # Shared library (388+ lines)
      │
      ├── gh-project-init.sh                 # Initialize configuration
      ├── gh-project-create.sh               # Create project
      ├── gh-project-list.sh                 # List projects
      ├── gh-project-view.sh                 # View project details
      ├── gh-project-delete.sh               # Delete project
      │
      ├── gh-epic-create.sh                  # Create epic
      ├── gh-epic-list.sh                    # List epics
      ├── gh-epic-view.sh                    # View epic details
      ├── gh-epic-update.sh                  # Update epic fields
      ├── gh-epic-delete.sh                  # Delete epic
      │
      ├── gh-story-create.sh                 # Create user story
      ├── gh-story-list.sh                   # List stories
      ├── gh-story-view.sh                   # View story details
      ├── gh-story-update.sh                 # Update story fields
      ├── gh-story-delete.sh                 # Delete story
      │
      ├── gh-task-create.sh                  # Create task
      ├── gh-task-list.sh                    # List tasks
      ├── gh-task-view.sh                    # View task details
      ├── gh-task-update.sh                  # Update task fields
      ├── gh-task-delete.sh                  # Delete task
      │
      ├── gh-spike-create.sh                 # Create spike
      ├── gh-spike-list.sh                   # List spikes
      ├── gh-spike-view.sh                   # View spike details
      ├── gh-spike-update.sh                 # Update spike fields
      ├── gh-spike-delete.sh                 # Delete spike
      │
      ├── gh-bug-create.sh                   # Create bug
      ├── gh-bug-list.sh                     # List bugs
      ├── gh-bug-view.sh                     # View bug details
      ├── gh-bug-update.sh                   # Update bug fields
      ├── gh-bug-delete.sh                   # Delete bug
      │
      └── README.md                          # Usage documentation

      ~/.claude/skills/lib/gh-projects-legacy/
      └── [old scripts archived here]         # Preserved for reference
      ```

      **Total: 32 files**
      - 1 common library
      - 1 init script
      - 5 project scripts (create, list, view, delete, + init)
      - 25 item scripts (5 types × 5 operations)
      - 1 README
    </directory_structure>

    <principles_applied>
      <solid>
        **Single Responsibility Principle:**
        - Each script does ONE operation on ONE resource
        - `gh-epic-create` creates epics (only)
        - `gh-epic-update` updates epic fields (only)
        - No multi-mode scripts with --create/--update flags

        **Open/Closed Principle:**
        - Scripts open for extension via config file
        - No hardcoded project numbers, field IDs
        - Environment variable overrides for one-offs
        - Closed for modification (stable interfaces)

        **Liskov Substitution Principle:**
        - All create scripts use same flag names (--title, --body)
        - All list scripts use same flags (--limit, --format)
        - All update scripts use same flags (--status, --priority)
        - Consistent behavior across similar operations

        **Interface Segregation Principle:**
        - Minimal required options per script
        - No forced options user doesn't need
        - Epic create: just --title (no --parent needed)
        - Story create: --title and --epic (parent explicit)
        - Task create: --title and --story (parent explicit)

        **Dependency Inversion Principle:**
        - Scripts depend on common library abstractions
        - Don't construct gh CLI commands directly
        - Use `create_repo_issue()` not `gh issue create ...`
        - High-level scripts call high-level functions
      </solid>

      <kiss>
        **Keep It Simple, Stupid:**

        Simplicity decisions:
        - ✅ Flat script organization (not hierarchical)
        - ✅ One script per operation (not subcommands)
        - ✅ Positional args for required (title is just arg, not --title)
        - ✅ Named flags for optional (--status, --priority)
        - ✅ Sensible defaults (status=Todo, priority=Medium)
        - ✅ No mode flags (--create/--update)
        - ✅ No complex option combinations
        - ✅ Help text under 30 lines
        - ✅ Each script under 100 lines

        Complexity avoided:
        - ❌ No universal CRUD script (gh-item --type epic --action create)
        - ❌ No complex parsers (--fields "status:Done,priority:High")
        - ❌ No boolean flag soup (--force --skip --no-cache)
        - ❌ No implicit modes (behavior changes based on flags)

        Result: Scripts so simple they need no documentation beyond --help
      </kiss>

      <dry>
        **Don't Repeat Yourself:**

        What's shared (in common library):
        ✅ Configuration loading
        ✅ Field caching and lookup
        ✅ Error handling and logging
        ✅ API wrappers (gh, GraphQL)
        ✅ Retry logic
        ✅ Validation (auth, config, fields)
        ✅ High-level operations (create issue + add to project)

        What's intentionally duplicated:
        ❌ Argument parsing - each script different
        ❌ Help text - each script unique
        ❌ Simple validations - inline clearer
        ❌ Error messages - context-specific

        Rule of three:
        - First occurrence: Write it
        - Second occurrence: Notice pattern
        - Third occurrence: Abstract to library

        Create issue + add to project pattern:
        - Appears in all create scripts (epic, story, task, spike, bug)
        - Third occurrence triggers abstraction
        - Result: `create_project_item(type, title, body)` in library
      </dry>

      <yagni>
        **You Aren't Gonna Need It:**

        Features deferred to future (not in v1):
        ❌ Multi-project support - config file per project
        ❌ Bulk operations - create many items from CSV
        ❌ Undo/rollback - transaction log
        ❌ Custom field types - only single-select in v1
        ❌ Projects V1 compatibility - deprecated by GitHub
        ❌ Pagination - assumes <30 items per type
        ❌ Advanced filters - complex queries
        ❌ GitHub Actions integration - CI/CD
        ❌ Batch updates - update many items at once
        ❌ Templates - create from templates
        ❌ Auto-update - check for new script versions

        Features included in v1 (proven necessary):
        ✅ --dry-run flag - safety for destructive ops
        ✅ --format json - machine readability
        ✅ Field caching - performance (already proven)
        ✅ Retry logic - network resilience (already proven)
        ✅ Help text - discoverability (essential)
        ✅ Config file - avoid repeating project number
        ✅ Environment overrides - one-off operations

        Decision criteria: Only include if:
        1. GitHub API requires it, OR
        2. Common use case demands it, OR
        3. Safety/reliability requires it
      </yagni>

      <triz>
        **Theory of Inventive Problem Solving:**

        Ideal Final Result (IFR):
        "The perfect CRUD script does its job with ZERO user effort"

        Approaching ideal:
        1. **Auto-detection over configuration**
           - Detect owner from `gh auth status`
           - Detect repo from git remote
           - Only ask for project number (can't auto-detect)
           - Config stored, never asked again

        2. **Graceful degradation**
           - Network fails → retry with backoff
           - Field missing → auto-refresh cache
           - Auth expired → show re-auth command

        3. **Self-documenting**
           - Flag names match GitHub UI exactly
           - Error messages include fix suggestions
           - Help text has examples for common cases

        4. **Intuitive defaults**
           - Status defaults to "Todo" (obvious start)
           - Priority defaults to "Medium" (safe middle)
           - Type implied by script (gh-epic-create → Type=Epic)

        5. **Predictable behavior**
           - Same command = same result (idempotent where possible)
           - No hidden side effects
           - Exit codes consistent

        Contradiction resolved: Simplicity vs Power
        - Problem: Users want simple AND powerful
        - TRIZ: Separate in space
        - Solution: Many simple scripts, each powerful alone
        - Result: `gh-epic-create` is simple, full suite is powerful
      </triz>
    </principles_applied>
  </architecture>

  <script_inventory>
    <common_library>
      <script>
        <path>~/.claude/skills/lib/gh-projects/lib/gh-project-common.sh</path>
        <purpose>Shared utilities, configuration, error handling, API wrappers</purpose>
        <responsibilities>
          • Load/save configuration (project number, owner, repo)
          • Field caching and resolution (handle case sensitivity)
          • API wrapper functions (gh CLI with PATH handling)
          • Error handling (die, retry_command)
          • Logging (colored output to stderr)
          • Validation (prerequisites, config, fields)
          • High-level operations (create item, update field, list by type)
        </responsibilities>
        <exports>
          # Configuration
          - load_config() - Load from ~/.config/gh-projects/config.json
          - save_config() - Write config
          - auto_detect_config() - Detect from git/gh
          - get_config_value(key) - Get single value

          # Field operations
          - cache_fields() - Fetch and cache field metadata
          - get_field_id(field_name) - Lookup field ID (lowercase)
          - get_option_id(field_name, option_name) - Lookup option ID
          - normalize_field_name(name) - Convert to lowercase

          # API wrappers
          - gh() - Wrapper with PATH handling
          - retry_command(cmd, args...) - Execute with retries
          - execute_graphql(query, variables) - GraphQL execution

          # Error handling
          - die(message, exit_code=1) - Exit with error
          - validate_prerequisites() - Check gh, jq, auth
          - validate_config() - Ensure config loaded

          # Logging
          - log_success(message) - Green (stderr)
          - log_error(message) - Red (stderr)
          - log_warn(message) - Yellow (stderr)
          - log_info(message) - Blue (stderr)

          # High-level operations (NEW)
          - create_repo_issue(title, body, labels, assignee) - Create issue, return URL
          - add_issue_to_project(issue_url) - Add to project, return item_id
          - set_item_field(item_id, field_name, value) - Update field
          - get_item_by_issue(issue_num) - Find item_id from issue number
          - list_items_by_type(type, limit) - Filter by Type field

          # Constants
          - CONFIG_FILE - Path to config
          - EXIT_SUCCESS=0
          - EXIT_ERROR=1
          - EXIT_MISUSE=2
          - EXIT_CONFIG=3
          - EXIT_API=4
        </exports>
        <complexity>Medium - 400+ lines of well-organized code</complexity>
      </script>
    </common_library>

    <project_scripts>
      <script>
        <name>gh-project-init.sh</name>
        <path>~/.claude/skills/lib/gh-projects/gh-project-init.sh</path>
        <purpose>Initialize project configuration</purpose>
        <responsibility>Single operation: configuration initialization</responsibility>
        <interface>
          <usage>gh-project-init.sh --project NUMBER [OPTIONS]</usage>
          <options>
            --project NUMBER    Project number (required)
            --owner OWNER       Project owner (default: auto-detect from gh auth)
            --repo REPO         Repository (default: auto-detect from git remote)
            --refresh-cache     Refresh field cache
            -h, --help          Show help
          </options>
        </interface>
        <help_text>
Usage: gh-project-init.sh --project NUMBER [OPTIONS]

Initialize GitHub Projects configuration for this repository.

Auto-detects owner and repo, fetches and caches project field metadata.
Configuration saved to ~/.config/gh-projects/config.json

Options:
  --project NUMBER    Project number (required)
  --owner OWNER       Project owner (default: auto-detect from gh auth)
  --repo REPO         Repository (default: auto-detect from git remote)
  --refresh-cache     Refresh field cache (use after field changes)
  -h, --help          Show this help

Examples:
  # Initialize for project #1 (auto-detect owner and repo)
  gh-project-init.sh --project 1

  # Refresh field cache after adding new field in GitHub UI
  gh-project-init.sh --project 1 --refresh-cache

  # Explicit owner and repo
  gh-project-init.sh --project 1 --owner myorg --repo myrepo

Configuration saved to: ~/.config/gh-projects/config.json
        </help_text>
        <errors>
          - Project not found → "Project #N not found for owner X"
          - Not authenticated → "Run: gh auth login && gh auth refresh -s project"
          - Config dir not writable → "Cannot write to ~/.config/gh-projects/"
        </errors>
        <exit_codes>
          0 - Success, config initialized
          1 - General error
          3 - Configuration error (invalid project, auth)
          4 - API error (network, rate limit)
        </exit_codes>
        <complexity>Simple - ~80 lines</complexity>
      </script>

      <script>
        <name>gh-project-create.sh</name>
        <path>~/.claude/skills/lib/gh-projects/gh-project-create.sh</path>
        <purpose>Create a new GitHub Project</purpose>
        <responsibility>Single operation: project creation</responsibility>
        <interface>
          <usage>gh-project-create.sh TITLE [OPTIONS]</usage>
          <options>
            TITLE               Project title (required, positional)
            --owner OWNER       Project owner (default: from config)
            --format json       Output as JSON
            -h, --help          Show help
          </options>
        </interface>
        <help_text>
Usage: gh-project-create.sh TITLE [OPTIONS]

Create a new GitHub Project.

Options:
  TITLE               Project title (required)
  --owner OWNER       Project owner (default: from config or @me)
  --format json       Output as JSON (default: human-readable)
  -h, --help          Show this help

Examples:
  # Create project with current user as owner
  gh-project-create.sh "Q1 2025 Roadmap"

  # Create project for organization
  gh-project-create.sh "Q1 2025 Roadmap" --owner myorg

  # Create and capture project number in JSON
  PROJECT_NUM=$(gh-project-create.sh "Q1 2025" --format json | jq -r '.number')

Output: Project number and URL
        </help_text>
        <errors>
          - No title → "Title required"
          - Insufficient permissions → "Need admin access to create projects for owner X"
        </errors>
        <exit_codes>0=success, 1=error, 4=API error</exit_codes>
        <complexity>Simple - ~60 lines</complexity>
      </script>

      <script>
        <name>gh-project-list.sh</name>
        <path>~/.claude/skills/lib/gh-projects/gh-project-list.sh</path>
        <purpose>List GitHub Projects</purpose>
        <responsibility>Single operation: list projects</responsibility>
        <interface>
          <usage>gh-project-list.sh [OPTIONS]</usage>
          <options>
            --owner OWNER       Project owner (default: from config or @me)
            --limit NUMBER      Max projects to list (default: 30)
            --format json       Output as JSON
            -h, --help          Show help
          </options>
        </interface>
        <help_text>
Usage: gh-project-list.sh [OPTIONS]

List GitHub Projects for owner.

Options:
  --owner OWNER       Project owner (default: from config or @me)
  --limit NUMBER      Max projects to list (default: 30)
  --format json       Output as JSON (default: table)
  -h, --help          Show this help

Examples:
  # List your projects
  gh-project-list.sh

  # List organization projects
  gh-project-list.sh --owner myorg

  # List first 10 projects as JSON
  gh-project-list.sh --limit 10 --format json

Output: Table or JSON of projects (number, title, state)
        </help_text>
        <errors>
          - No permissions → "Cannot access projects for owner X"
        </errors>
        <exit_codes>0=success, 1=error, 4=API error</exit_codes>
        <complexity>Simple - ~50 lines</complexity>
      </script>

      <script>
        <name>gh-project-view.sh</name>
        <path>~/.claude/skills/lib/gh-projects/gh-project-view.sh</path>
        <purpose>View GitHub Project details</purpose>
        <responsibility>Single operation: view project</responsibility>
        <interface>
          <usage>gh-project-view.sh NUMBER [OPTIONS]</usage>
          <options>
            NUMBER              Project number (required, positional)
            --owner OWNER       Project owner (default: from config)
            --format json       Output as JSON
            --web               Open in browser
            -h, --help          Show help
          </options>
        </interface>
        <help_text>
Usage: gh-project-view.sh NUMBER [OPTIONS]

View GitHub Project details.

Options:
  NUMBER              Project number (required)
  --owner OWNER       Project owner (default: from config)
  --format json       Output as JSON (default: human-readable)
  --web               Open project in browser
  -h, --help          Show this help

Examples:
  # View project #1
  gh-project-view.sh 1

  # View project as JSON
  gh-project-view.sh 1 --format json

  # Open project in browser
  gh-project-view.sh 1 --web

Output: Project details (title, description, items count, fields)
        </help_text>
        <errors>
          - Project not found → "Project #N not found for owner X"
        </errors>
        <exit_codes>0=success, 1=error, 4=API error</exit_codes>
        <complexity>Simple - ~50 lines</complexity>
      </script>

      <script>
        <name>gh-project-delete.sh</name>
        <path>~/.claude/skills/lib/gh-projects/gh-project-delete.sh</path>
        <purpose>Delete GitHub Project</purpose>
        <responsibility>Single operation: project deletion</responsibility>
        <interface>
          <usage>gh-project-delete.sh NUMBER [OPTIONS]</usage>
          <options>
            NUMBER              Project number (required, positional)
            --owner OWNER       Project owner (default: from config)
            --confirm           Skip confirmation prompt
            --dry-run           Show what would be deleted
            -h, --help          Show help
          </options>
        </interface>
        <help_text>
Usage: gh-project-delete.sh NUMBER [OPTIONS]

Delete a GitHub Project permanently.

WARNING: This is destructive and cannot be undone.

Options:
  NUMBER              Project number (required)
  --owner OWNER       Project owner (default: from config)
  --confirm           Skip confirmation prompt (use with caution)
  --dry-run           Show what would be deleted without deleting
  -h, --help          Show this help

Examples:
  # Delete project with confirmation
  gh-project-delete.sh 1

  # Preview deletion (dry-run)
  gh-project-delete.sh 1 --dry-run

  # Delete without confirmation (scripts/automation)
  gh-project-delete.sh 1 --confirm

Note: Repository issues are NOT deleted, only project is removed.
        </help_text>
        <errors>
          - Project not found → "Project #N not found"
          - No confirmation → "Deletion cancelled"
          - Insufficient permissions → "Need admin access to delete project"
        </errors>
        <exit_codes>0=success, 1=error, 2=cancelled, 4=API error</exit_codes>
        <complexity>Simple - ~70 lines (includes confirmation)</complexity>
      </script>
    </project_scripts>

    <item_scripts>
      <!-- Pattern applies to: Epic, Story, Task, Spike, Bug -->
      <!-- Each type gets: create, list, view, update, delete -->

      <script>
        <name>gh-epic-create.sh</name>
        <path>~/.claude/skills/lib/gh-projects/gh-epic-create.sh</path>
        <purpose>Create a new Epic in the project</purpose>
        <responsibility>Single operation: epic creation</responsibility>
        <interface>
          <usage>gh-epic-create.sh TITLE [OPTIONS]</usage>
          <options>
            TITLE               Epic title (required, positional)
            --body TEXT         Epic description
            --body-file FILE    Read description from file
            --status STATUS     Status (default: Todo)
            --priority PRIORITY Priority (default: Medium)
            --assignee USER     Assignee username
            --labels LABEL,...  Comma-separated labels
            --format json       Output as JSON
            --dry-run           Preview without creating
            -h, --help          Show help
          </options>
        </interface>
        <help_text>
Usage: gh-epic-create.sh TITLE [OPTIONS]

Create a new Epic (repository issue + project item with Type=Epic).

Options:
  TITLE               Epic title (required)
  --body TEXT         Epic description (optional)
  --body-file FILE    Read description from file (alternative to --body)
  --status STATUS     Status (default: Todo)
                      Options: Todo, In Progress, Done, Blocked
  --priority PRIORITY Priority (default: Medium)
                      Options: Low, Medium, High, Critical
  --assignee USER     Assignee GitHub username
  --labels LABEL,...  Comma-separated labels (e.g., "epic,backend")
  --format json       Output as JSON (default: human-readable)
  --dry-run           Preview without creating
  -h, --help          Show this help

Examples:
  # Create simple epic
  gh-epic-create.sh "Authentication System"

  # Create epic with description and priority
  gh-epic-create.sh "Authentication System" \
    --body "Implement OAuth2 and SSO" \
    --priority High

  # Create epic from file
  gh-epic-create.sh "Authentication System" \
    --body-file epic-description.md \
    --assignee johndoe \
    --labels "epic,security"

  # Create and capture issue number
  ISSUE=$(gh-epic-create.sh "Test Epic" --format json | jq -r '.number')

Output: Epic issue number and URL

Note: Epic is created as a repository issue AND added to the project.
      Use the issue number to reference it in commits/PRs.
        </help_text>
        <implementation>
          1. Validate title (required)
          2. Load config (project, owner, repo)
          3. Create repository issue (gh issue create)
          4. Add issue to project (gh project item-add)
          5. Set Type=Epic field
          6. Set Status field (default: Todo)
          7. Set Priority field (default: Medium)
          8. Return issue number and URL
        </implementation>
        <errors>
          - No title → "Epic title required"
          - No config → "Run: gh-project-init.sh --project NUMBER"
          - Field not found → "Refresh cache: gh-project-init.sh --refresh-cache"
          - Partial creation → "Issue #N created but not added to project (error: X)"
        </errors>
        <exit_codes>0=success, 1=error, 3=config error, 4=API error</exit_codes>
        <complexity>Medium - ~100 lines (uses common library functions)</complexity>
      </script>

      <script>
        <name>gh-epic-list.sh</name>
        <path>~/.claude/skills/lib/gh-projects/gh-epic-list.sh</path>
        <purpose>List all Epics in the project</purpose>
        <responsibility>Single operation: list epics</responsibility>
        <interface>
          <usage>gh-epic-list.sh [OPTIONS]</usage>
          <options>
            --status STATUS     Filter by status (optional)
            --priority PRIORITY Filter by priority (optional)
            --limit NUMBER      Max items to list (default: 30)
            --format json       Output as JSON
            -h, --help          Show help
          </options>
        </interface>
        <help_text>
Usage: gh-epic-list.sh [OPTIONS]

List all Epics (Type=Epic) in the project.

Options:
  --status STATUS     Filter by status (e.g., "In Progress")
  --priority PRIORITY Filter by priority (e.g., "High")
  --limit NUMBER      Max epics to list (default: 30)
  --format json       Output as JSON (default: table)
  -h, --help          Show this help

Examples:
  # List all epics
  gh-epic-list.sh

  # List high-priority epics
  gh-epic-list.sh --priority High

  # List epics in progress
  gh-epic-list.sh --status "In Progress"

  # List as JSON
  gh-epic-list.sh --format json

Output: Table or JSON (issue number, title, status, priority)
        </help_text>
        <implementation>
          1. Load config
          2. Fetch all project items (gh project item-list)
          3. Filter by Type=Epic
          4. Apply status/priority filters (if specified)
          5. Format as table or JSON
        </implementation>
        <errors>
          - No config → "Run: gh-project-init.sh --project NUMBER"
        </errors>
        <exit_codes>0=success, 1=error, 3=config error, 4=API error</exit_codes>
        <complexity>Simple - ~70 lines</complexity>
      </script>

      <script>
        <name>gh-epic-view.sh</name>
        <path>~/.claude/skills/lib/gh-projects/gh-epic-view.sh</path>
        <purpose>View Epic details</purpose>
        <responsibility>Single operation: view epic</responsibility>
        <interface>
          <usage>gh-epic-view.sh ISSUE_NUMBER [OPTIONS]</usage>
          <options>
            ISSUE_NUMBER        Issue number (required, positional)
            --format json       Output as JSON
            --web               Open in browser
            -h, --help          Show help
          </options>
        </interface>
        <help_text>
Usage: gh-epic-view.sh ISSUE_NUMBER [OPTIONS]

View Epic details.

Options:
  ISSUE_NUMBER        Epic issue number (required)
  --format json       Output as JSON (default: human-readable)
  --web               Open epic in browser
  -h, --help          Show this help

Examples:
  # View epic #42
  gh-epic-view.sh 42

  # View as JSON
  gh-epic-view.sh 42 --format json

  # Open in browser
  gh-epic-view.sh 42 --web

Output: Epic details (title, body, status, priority, sub-issues)
        </help_text>
        <implementation>
          1. Load config
          2. Fetch issue details (gh issue view)
          3. Find project item (get_item_by_issue)
          4. Fetch field values (status, priority, type)
          5. Query sub-issues (children)
          6. Format output
        </implementation>
        <errors>
          - Issue not found → "Issue #N not found in repository"
          - Not in project → "Issue #N exists but is not in project"
        </errors>
        <exit_codes>0=success, 1=error, 3=config error, 4=API error</exit_codes>
        <complexity>Simple - ~80 lines</complexity>
      </script>

      <script>
        <name>gh-epic-update.sh</name>
        <path>~/.claude/skills/lib/gh-projects/gh-epic-update.sh</path>
        <purpose>Update Epic fields</purpose>
        <responsibility>Single operation: update epic fields</responsibility>
        <interface>
          <usage>gh-epic-update.sh ISSUE_NUMBER [OPTIONS]</usage>
          <options>
            ISSUE_NUMBER        Issue number (required, positional)
            --status STATUS     Update status
            --priority PRIORITY Update priority
            --title TITLE       Update title
            --body TEXT         Update body
            --assignee USER     Update assignee
            --add-labels LABEL  Add labels
            --dry-run           Preview without updating
            -h, --help          Show help
          </options>
        </interface>
        <help_text>
Usage: gh-epic-update.sh ISSUE_NUMBER [OPTIONS]

Update Epic fields (status, priority, title, body, assignee).

Options:
  ISSUE_NUMBER        Epic issue number (required)
  --status STATUS     Update status (Todo, In Progress, Done, Blocked)
  --priority PRIORITY Update priority (Low, Medium, High, Critical)
  --title TITLE       Update title
  --body TEXT         Update body/description
  --assignee USER     Update assignee
  --add-labels LABEL  Add labels (comma-separated)
  --dry-run           Preview without updating
  -h, --help          Show this help

Examples:
  # Update epic status
  gh-epic-update.sh 42 --status "In Progress"

  # Update priority and assignee
  gh-epic-update.sh 42 --priority High --assignee johndoe

  # Update title
  gh-epic-update.sh 42 --title "New Epic Title"

  # Multiple updates at once
  gh-epic-update.sh 42 --status Done --priority High --add-labels "completed"

Note: Issue fields (title, body, assignee) updated via gh issue edit.
      Project fields (status, priority) updated via gh project item-edit.
        </help_text>
        <implementation>
          1. Validate issue number
          2. Load config
          3. Find project item (get_item_by_issue)
          4. Update issue fields if specified (gh issue edit)
          5. Update project fields if specified (set_item_field)
          6. Report what was updated
        </implementation>
        <errors>
          - Issue not found → "Issue #N not found"
          - Not in project → "Issue #N not in project (cannot update project fields)"
          - Invalid status → "Invalid status 'X'. Options: Todo, In Progress, Done, Blocked"
          - No changes → "No changes specified. Use --status, --priority, etc."
        </errors>
        <exit_codes>0=success, 1=error, 2=no changes, 3=config error, 4=API error</exit_codes>
        <complexity>Medium - ~100 lines (handles multiple field types)</complexity>
      </script>

      <script>
        <name>gh-epic-delete.sh</name>
        <path>~/.claude/skills/lib/gh-projects/gh-epic-delete.sh</path>
        <purpose>Delete Epic</purpose>
        <responsibility>Single operation: delete epic</responsibility>
        <interface>
          <usage>gh-epic-delete.sh ISSUE_NUMBER [OPTIONS]</usage>
          <options>
            ISSUE_NUMBER        Issue number (required, positional)
            --from-project-only Remove from project but keep issue
            --confirm           Skip confirmation
            --dry-run           Preview without deleting
            -h, --help          Show help
          </options>
        </interface>
        <help_text>
Usage: gh-epic-delete.sh ISSUE_NUMBER [OPTIONS]

Delete Epic (removes from project AND deletes issue).

WARNING: This is destructive and cannot be undone.

Options:
  ISSUE_NUMBER        Epic issue number (required)
  --from-project-only Remove from project but keep repository issue
  --confirm           Skip confirmation prompt
  --dry-run           Preview without deleting
  -h, --help          Show this help

Examples:
  # Delete epic with confirmation
  gh-epic-delete.sh 42

  # Remove from project only (keep issue)
  gh-epic-delete.sh 42 --from-project-only

  # Delete without confirmation
  gh-epic-delete.sh 42 --confirm

  # Preview deletion
  gh-epic-delete.sh 42 --dry-run

Default behavior: Removes from project AND deletes repository issue.
Use --from-project-only to keep the issue but remove from project.
        </help_text>
        <implementation>
          1. Validate issue number
          2. Load config
          3. Find project item
          4. Show what will be deleted (dry-run or confirmation)
          5. Remove from project (gh project item-delete)
          6. Delete issue if not --from-project-only (gh issue delete)
          7. Report success
        </implementation>
        <errors>
          - Issue not found → "Issue #N not found"
          - Not in project → "Issue #N not in project (use gh issue delete directly)"
          - Cancelled → "Deletion cancelled"
        </errors>
        <exit_codes>0=success, 1=error, 2=cancelled, 3=config error, 4=API error</exit_codes>
        <complexity>Simple - ~80 lines</complexity>
      </script>

      <!-- PATTERN REPEATS FOR ALL ITEM TYPES -->

      <pattern>
        **Each item type (Story, Task, Spike, Bug) gets same 5 operations:**

        1. **create** - Create item (repo issue + project item)
           - Type field set automatically (Story/Task/Spike/Bug)
           - Options: --title, --body, --status, --priority, --assignee, --labels
           - Story/Task: Requires --epic or --story for parent relationship
           - Implementation: ~100 lines

        2. **list** - List items of this type
           - Filter by Type field automatically
           - Options: --status, --priority, --limit, --format
           - Implementation: ~70 lines

        3. **view** - View item details
           - Show issue + project fields + relationships
           - Options: --format, --web
           - Implementation: ~80 lines

        4. **update** - Update item fields
           - Options: --status, --priority, --title, --body, --assignee
           - Implementation: ~100 lines

        5. **delete** - Delete item
           - Options: --from-project-only, --confirm, --dry-run
           - Implementation: ~80 lines

        **Specific variations:**

        **gh-story-create:**
        - Requires --epic flag (parent Epic issue number)
        - Automatically links as sub-issue to Epic

        **gh-task-create:**
        - Requires --story flag (parent Story issue number)
        - Automatically links as sub-issue to Story

        **gh-bug-create:**
        - Optional --epic or --story flag (can be standalone)
        - Adds "bug" label automatically

        **gh-spike-create:**
        - Optional --epic flag (usually child of Epic)
        - Adds "spike" label automatically
      </pattern>
    </item_scripts>

    <script_count>
      Total scripts: 32

      Breakdown:
      - 1 common library (lib/gh-project-common.sh)
      - 1 init script (gh-project-init.sh)
      - 4 project operations (create, list, view, delete)
      - 25 item operations (5 types × 5 operations)

      Lines of code (estimated):
      - Common library: 450 lines
      - Init: 80 lines
      - Project scripts: 4 × 60 = 240 lines
      - Item scripts: 25 × 85 = 2,125 lines
      - Total: ~2,900 lines (well-organized, highly readable)

      Comparison to old implementation:
      - Old: 16 scripts, ~3,000 lines (complex, multi-mode)
      - New: 32 scripts, ~2,900 lines (simple, single-mode)
      - Result: More scripts, similar LOC, much simpler each
    </script_count>
  </script_inventory>

  <migration_strategy>
    <preservation>
      <action>Move existing scripts to legacy directory</action>
      <from>~/.claude/skills/lib/gh-projects/</from>
      <to>~/.claude/skills/lib/gh-projects-legacy/</to>
      <preserve>
        All existing scripts:
        - gh-project-*.sh (all variants)
        - lib/gh-project-common.sh (old version)
        - Any helper scripts
        - README.md (old docs)

        Why preserve:
        - Reference implementation for migration
        - Pattern comparison (old vs new)
        - Rollback option if issues found
        - Historical record

        Archive structure:
        ~/.claude/skills/lib/gh-projects-legacy/
        ├── ARCHIVED-README.md (explains why archived)
        ├── lib/gh-project-common.sh (old)
        └── [all old scripts]
      </preserve>
    </preservation>

    <mapping>
      <old_to_new>
        <!-- Project operations -->
        <entry>
          <old>gh-project-list.sh [--owner OWNER]</old>
          <new>gh-project-list.sh [--owner OWNER]</new>
          <notes>Same interface, improved implementation</notes>
        </entry>

        <entry>
          <old>gh-project-init.sh --project NUM</old>
          <new>gh-project-init.sh --project NUM</new>
          <notes>Same interface, improved field caching</notes>
        </entry>

        <entry>
          <old>gh-project-item-create.sh --title "Epic" --type Epic</old>
          <new>gh-epic-create.sh "Epic"</new>
          <notes>Type implicit, simpler interface</notes>
        </entry>

        <entry>
          <old>gh-project-item-create.sh --title "Story" --type "User Story" --parent 42</old>
          <new>gh-story-create.sh "Story" --epic 42</new>
          <notes>Type implicit, parent relationship explicit</notes>
        </entry>

        <entry>
          <old>gh-project-update.sh --issue 42 --status "In Progress"</old>
          <new>gh-epic-update.sh 42 --status "In Progress"</new>
          <notes>Type-specific script (requires knowing item type)</notes>
        </entry>

        <entry>
          <old>gh-project-list.sh --type Epic --format json</old>
          <new>gh-epic-list.sh --format json</new>
          <notes>Type implicit</notes>
        </entry>

        <entry>
          <old>gh-project-item-delete.sh --issue 42</old>
          <new>gh-epic-delete.sh 42</new>
          <notes>Type-specific (requires knowing item type)</notes>
        </entry>

        <!-- No direct equivalent (deprecated) -->
        <entry>
          <old>gh-project-setup-clone.sh</old>
          <new>N/A - Feature removed (YAGNI)</new>
          <notes>Clone project config not used in practice</notes>
        </entry>

        <entry>
          <old>gh-project-convert.sh</old>
          <new>N/A - Feature removed (unclear purpose)</new>
          <notes>Convert script had no clear use case</notes>
        </entry>
      </old_to_new>
    </mapping>

    <breaking_changes>
      **Changes that affect existing usage:**

      1. **Type must be known for item operations**
         - Old: `gh-project-update.sh --issue 42 --status Done` (works for any type)
         - New: `gh-epic-update.sh 42 --status Done` (must know it's an Epic)
         - Rationale: Type-specific scripts enforce correct parent relationships
         - Mitigation: Use `gh-{type}-view.sh` to check type first

      2. **Parent relationships explicit**
         - Old: `gh-project-item-create.sh --title "Story" --type "User Story" --parent 42`
         - New: `gh-story-create.sh "Story" --epic 42`
         - Rationale: Clearer what parent relationship means
         - Benefit: Prevents linking Task directly to Epic (should go through Story)

      3. **No generic item operations**
         - Old: `gh-project-item-create.sh --type Epic`
         - New: `gh-epic-create.sh` (type implied)
         - Rationale: Separate scripts simpler than multi-mode
         - Benefit: Can't create invalid type

      4. **Setup scripts consolidated**
         - Old: `gh-project-setup-init`, `gh-project-setup-apply`, `gh-project-setup-clone`
         - New: `gh-project-init.sh` only
         - Rationale: Other setup variants unused (YAGNI)
         - Benefit: One clear way to initialize

      5. **Positional arguments for required fields**
         - Old: `--title "Epic Title"` (named flag)
         - New: `"Epic Title"` (positional)
         - Rationale: Required field doesn't need flag
         - Benefit: Less typing for common case

      **Non-breaking improvements:**
      - Field name normalization (handles case automatically)
      - Better error messages
      - Consistent exit codes
      - Comprehensive help text
      - PATH handling fixed
    </breaking_changes>

    <skills_to_update>
      **Skills that reference old scripts:**

      Check and update these skills:
      - execute-epic.skill.md - Uses gh-project-item-create
      - execute-user-story.skill.md - Uses gh-project-item-create
      - epic-to-user-stories.skill.md - Uses gh-project-item-create
      - prd-to-epics.skill.md - Uses gh-project-item-create

      **Update pattern:**
      ```diff
      - gh-project-item-create.sh --title "$TITLE" --type Epic --status Todo
      + gh-epic-create.sh "$TITLE" --status Todo
      ```

      ```diff
      - gh-project-item-create.sh --title "$TITLE" --type "User Story" --parent $EPIC_NUM
      + gh-story-create.sh "$TITLE" --epic $EPIC_NUM
      ```

      **Testing each skill after update:**
      1. Run skill in test environment
      2. Verify items created correctly
      3. Check field values set properly
      4. Confirm relationships (Epic ← Story) work
    </skills_to_update>

    <migration_checklist>
      **Pre-migration:**
      - [ ] Archive existing scripts to gh-projects-legacy/
      - [ ] Create ARCHIVED-README.md explaining migration
      - [ ] Verify all old scripts present in archive
      - [ ] Test old scripts still work from archive (rollback option)

      **Implementation:**
      - [ ] Implement Phase 1 (Foundation)
      - [ ] Test common library functions
      - [ ] Implement Phase 2 (Project CRUD)
      - [ ] Test project operations
      - [ ] Implement Phase 3 (Epic & Story)
      - [ ] Test epic and story operations
      - [ ] Implement Phase 4 (Task, Spike, Bug)
      - [ ] Test all item types

      **Skill updates:**
      - [ ] List all skills referencing old scripts
      - [ ] Update each skill to use new scripts
      - [ ] Test each updated skill
      - [ ] Document skill changes

      **Verification:**
      - [ ] Create test project
      - [ ] Run through common workflows with new scripts
      - [ ] Verify all operations work
      - [ ] Check error messages helpful
      - [ ] Confirm field values correct

      **Cleanup:**
      - [ ] Update main README.md
      - [ ] Add migration guide
      - [ ] Document old → new script mappings
      - [ ] Archive verified complete
    </migration_checklist>
  </migration_strategy>

  <implementation_phases>
    <phase number="1">
      <name>Foundation</name>
      <goal>Establish common library, configuration, and utilities</goal>
      <deliverables>
        <deliverable>
          <file>lib/gh-project-common.sh</file>
          <description>Enhanced common library with high-level functions</description>
          <complexity>Medium</complexity>
          <loc>450 lines</loc>
          <functions>
            - All existing functions (config, fields, logging, error handling)
            - NEW: create_repo_issue()
            - NEW: add_issue_to_project()
            - NEW: set_item_field()
            - NEW: get_item_by_issue()
            - NEW: list_items_by_type()
            - NEW: normalize_field_name()
            - NEW: gh() wrapper with PATH handling
          </functions>
        </deliverable>

        <deliverable>
          <file>gh-project-init.sh</file>
          <description>Configuration initialization script</description>
          <complexity>Simple</complexity>
          <loc>80 lines</loc>
          <features>
            - Auto-detect owner from gh auth
            - Auto-detect repo from git remote
            - Fetch and cache field metadata
            - Save to ~/.config/gh-projects/config.json
            - --refresh-cache option
          </features>
        </deliverable>

        <deliverable>
          <file>README.md</file>
          <description>Usage documentation</description>
          <complexity>Simple</complexity>
          <content>
            - Overview of script suite
            - Installation instructions
            - Quick start guide
            - Script organization explanation
            - Common workflows
            - Troubleshooting
          </content>
        </deliverable>
      </deliverables>

      <dependencies>None (foundation layer)</dependencies>

      <acceptance_criteria>
        - [ ] Common library can be sourced without errors
        - [ ] Config loads from file with env var override
        - [ ] Field name normalization handles case correctly
        - [ ] gh() wrapper finds gh CLI in restricted environments
        - [ ] create_repo_issue() creates issue and returns URL
        - [ ] add_issue_to_project() adds issue and returns item_id
        - [ ] set_item_field() updates fields correctly
        - [ ] get_item_by_issue() finds item from issue number
        - [ ] list_items_by_type() filters by Type field
        - [ ] gh-project-init.sh creates valid config
        - [ ] All logging functions work (colors, stderr)
        - [ ] Error messages include actionable suggestions
      </acceptance_criteria>

      <testing>
        **Unit tests (manual):**
        - Source common library → no errors
        - Call each function with test data → correct results
        - Test error paths → helpful messages

        **Integration test:**
        - Run gh-project-init.sh → config created
        - Verify config structure → all fields present
        - Load config in test script → values accessible
        - Override with env var → env var takes precedence
      </testing>

      <estimated_effort>4-6 hours</estimated_effort>
    </phase>

    <phase number="2">
      <name>Project CRUD</name>
      <goal>Implement basic project management operations</goal>
      <deliverables>
        <deliverable>
          <file>gh-project-create.sh</file>
          <description>Create new project</description>
          <complexity>Simple</complexity>
          <loc>60 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-project-list.sh</file>
          <description>List projects</description>
          <complexity>Simple</complexity>
          <loc>50 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-project-view.sh</file>
          <description>View project details</description>
          <complexity>Simple</complexity>
          <loc>50 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-project-delete.sh</file>
          <description>Delete project</description>
          <complexity>Simple</complexity>
          <loc>70 lines (includes confirmation)</loc>
        </deliverable>
      </deliverables>

      <dependencies>
        Phase 1 (common library, config)
      </dependencies>

      <acceptance_criteria>
        - [ ] gh-project-create creates project and returns number
        - [ ] gh-project-list shows projects in table format
        - [ ] gh-project-list --format json outputs valid JSON
        - [ ] gh-project-view shows project details
        - [ ] gh-project-view --web opens in browser
        - [ ] gh-project-delete prompts for confirmation
        - [ ] gh-project-delete --confirm skips prompt
        - [ ] gh-project-delete --dry-run previews without deleting
        - [ ] All scripts have comprehensive --help
        - [ ] All scripts handle errors gracefully
      </acceptance_criteria>

      <testing>
        **Workflow test:**
        1. Create project: `gh-project-create.sh "Test Project"`
        2. List projects: `gh-project-list.sh` → includes new project
        3. View project: `gh-project-view.sh 1` → shows details
        4. Delete project (dry): `gh-project-delete.sh 1 --dry-run` → previews
        5. Delete project: `gh-project-delete.sh 1` → deleted after confirmation

        **Edge cases:**
        - Create with no title → error with help
        - View non-existent project → clear error
        - Delete with --confirm → no prompt
      </testing>

      <estimated_effort>2-3 hours</estimated_effort>
    </phase>

    <phase number="3">
      <name>Epic & Story CRUD</name>
      <goal>Implement core item types (Epic and User Story)</goal>
      <deliverables>
        <deliverable>
          <file>gh-epic-create.sh</file>
          <description>Create epic</description>
          <complexity>Medium</complexity>
          <loc>100 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-epic-list.sh</file>
          <description>List epics</description>
          <complexity>Simple</complexity>
          <loc>70 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-epic-view.sh</file>
          <description>View epic details</description>
          <complexity>Simple</complexity>
          <loc>80 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-epic-update.sh</file>
          <description>Update epic fields</description>
          <complexity>Medium</complexity>
          <loc>100 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-epic-delete.sh</file>
          <description>Delete epic</description>
          <complexity>Simple</complexity>
          <loc>80 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-story-create.sh</file>
          <description>Create user story (linked to epic)</description>
          <complexity>Medium</complexity>
          <loc>110 lines (includes parent linking)</loc>
        </deliverable>

        <deliverable>
          <file>gh-story-list.sh</file>
          <description>List user stories</description>
          <complexity>Simple</complexity>
          <loc>70 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-story-view.sh</file>
          <description>View story details</description>
          <complexity>Simple</complexity>
          <loc>80 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-story-update.sh</file>
          <description>Update story fields</description>
          <complexity>Medium</complexity>
          <loc>100 lines</loc>
        </deliverable>

        <deliverable>
          <file>gh-story-delete.sh</file>
          <description>Delete story</description>
          <complexity>Simple</complexity>
          <loc>80 lines</loc>
        </deliverable>
      </deliverables>

      <dependencies>
        Phase 1 (common library)
        Phase 2 (project must exist)
      </dependencies>

      <acceptance_criteria>
        **Epic operations:**
        - [ ] gh-epic-create creates issue + project item with Type=Epic
        - [ ] Epic has default status=Todo, priority=Medium
        - [ ] gh-epic-list filters items where Type=Epic
        - [ ] gh-epic-view shows epic with sub-issues (stories)
        - [ ] gh-epic-update changes status/priority correctly
        - [ ] gh-epic-delete removes from project and/or deletes issue

        **Story operations:**
        - [ ] gh-story-create requires --epic flag
        - [ ] Story created with Type="User Story"
        - [ ] Story linked as sub-issue to Epic (parent-child)
        - [ ] gh-story-list filters items where Type="User Story"
        - [ ] gh-story-view shows story with parent epic
        - [ ] gh-story-update changes fields correctly
        - [ ] gh-story-delete removes from project and/or deletes issue

        **Relationships:**
        - [ ] Epic view shows child stories
        - [ ] Story view shows parent epic
        - [ ] Deleting epic doesn't auto-delete stories (by design)
      </acceptance_criteria>

      <testing>
        **Workflow test:**
        1. Create epic: `gh-epic-create.sh "Auth System"`
        2. List epics: `gh-epic-list.sh` → shows new epic
        3. Create story: `gh-story-create.sh "OAuth Login" --epic 1`
        4. View epic: `gh-epic-view.sh 1` → shows story #2 as child
        5. View story: `gh-story-view.sh 2` → shows epic #1 as parent
        6. Update epic: `gh-epic-update.sh 1 --status "In Progress"`
        7. List in-progress epics: `gh-epic-list.sh --status "In Progress"` → shows #1
        8. Delete story: `gh-story-delete.sh 2`
        9. Delete epic: `gh-epic-delete.sh 1`

        **Edge cases:**
        - Create story without --epic → error
        - Create story with non-existent epic → error
        - Update with invalid status → error with valid options
      </testing>

      <estimated_effort>6-8 hours</estimated_effort>
    </phase>

    <phase number="4">
      <name>Task, Spike, Bug CRUD</name>
      <goal>Implement remaining item types following established pattern</goal>
      <deliverables>
        **Task scripts (5):**
        - gh-task-create.sh (requires --story)
        - gh-task-list.sh
        - gh-task-view.sh
        - gh-task-update.sh
        - gh-task-delete.sh

        **Spike scripts (5):**
        - gh-spike-create.sh (optional --epic)
        - gh-spike-list.sh
        - gh-spike-view.sh
        - gh-spike-update.sh
        - gh-spike-delete.sh

        **Bug scripts (5):**
        - gh-bug-create.sh (optional --epic or --story)
        - gh-bug-list.sh
        - gh-bug-view.sh
        - gh-bug-update.sh
        - gh-bug-delete.sh
      </deliverables>

      <dependencies>
        Phase 3 (pattern established with Epic/Story)
      </dependencies>

      <acceptance_criteria>
        **Task operations:**
        - [ ] gh-task-create requires --story flag
        - [ ] Task linked as sub-issue to Story
        - [ ] gh-task-list filters Type=Task
        - [ ] All CRUD operations work

        **Spike operations:**
        - [ ] gh-spike-create allows optional --epic
        - [ ] Spike can be standalone or child of epic
        - [ ] "spike" label added automatically
        - [ ] All CRUD operations work

        **Bug operations:**
        - [ ] gh-bug-create allows optional --epic or --story
        - [ ] "bug" label added automatically
        - [ ] Bug can be standalone or child
        - [ ] All CRUD operations work

        **Consistency:**
        - [ ] All item types follow same patterns
        - [ ] Help text consistent across types
        - [ ] Error messages follow same format
        - [ ] Exit codes consistent
      </acceptance_criteria>

      <testing>
        **Task workflow:**
        1. Create story (prerequisite)
        2. Create task: `gh-task-create.sh "Implement login" --story 2`
        3. Verify task linked to story
        4. Test all CRUD operations

        **Spike workflow:**
        1. Create epic (prerequisite)
        2. Create spike: `gh-spike-create.sh "Research OAuth libs" --epic 1`
        3. Verify spike linked and labeled
        4. Test all CRUD operations

        **Bug workflow:**
        1. Create bug: `gh-bug-create.sh "Login fails on Safari"`
        2. Verify standalone bug created with label
        3. Create bug with parent: `gh-bug-create.sh "Safari CORS" --story 2`
        4. Test all CRUD operations
      </testing>

      <estimated_effort>4-5 hours (pattern reuse)</estimated_effort>
    </phase>

    <phase number="5">
      <name>Migration and Testing</name>
      <goal>Archive old scripts, update skills, verify equivalence, document</goal>
      <deliverables>
        <deliverable>
          <file>~/.claude/skills/lib/gh-projects-legacy/</file>
          <description>Archived old scripts</description>
          <complexity>Simple</complexity>
          <action>Move all old scripts to legacy directory</action>
        </deliverable>

        <deliverable>
          <file>~/.claude/skills/lib/gh-projects-legacy/ARCHIVED-README.md</file>
          <description>Explanation of migration</description>
          <complexity>Simple</complexity>
          <content>
            - Why scripts were archived
            - Migration date
            - Mapping to new scripts
            - How to rollback if needed
          </content>
        </deliverable>

        <deliverable>
          <file>MIGRATION-GUIDE.md</file>
          <description>Old → new script migration guide</description>
          <complexity>Simple</complexity>
          <content>
            - Complete mapping table
            - Breaking changes explained
            - Common workflow conversions
            - Troubleshooting
          </content>
        </deliverable>

        <deliverable>
          <description>Updated skills</description>
          <complexity>Medium</complexity>
          <action>Update all skills that reference old scripts</action>
          <affected_skills>
            - execute-epic
            - execute-user-story
            - epic-to-user-stories
            - prd-to-epics
          </affected_skills>
        </deliverable>

        <deliverable>
          <file>test-suite.sh</file>
          <description>Integration test suite</description>
          <complexity>Medium</complexity>
          <tests>
            - Test all create operations
            - Test all list operations
            - Test all update operations
            - Test all delete operations
            - Test parent-child relationships
            - Test field updates
            - Test error handling
          </tests>
        </deliverable>
      </deliverables>

      <dependencies>
        Phases 1-4 (all scripts implemented)
      </dependencies>

      <acceptance_criteria>
        **Archive:**
        - [ ] All old scripts moved to gh-projects-legacy/
        - [ ] ARCHIVED-README.md explains migration
        - [ ] Old scripts still work from legacy location (rollback option)

        **Documentation:**
        - [ ] MIGRATION-GUIDE.md complete with mappings
        - [ ] README.md updated with new script organization
        - [ ] Each script has comprehensive --help

        **Skills:**
        - [ ] All affected skills identified
        - [ ] Each skill updated to use new scripts
        - [ ] Each skill tested and working

        **Testing:**
        - [ ] Integration test suite runs all operations
        - [ ] All tests pass
        - [ ] No regressions from old implementation

        **Verification:**
        - [ ] Common workflows tested end-to-end
        - [ ] Error messages validated
        - [ ] Performance acceptable
      </acceptance_criteria>

      <testing>
        **Integration test suite:**
        ```bash
        #!/usr/bin/env bash
        # test-suite.sh - Integration tests for gh-projects scripts

        set -euo pipefail

        echo "=== GitHub Projects Script Test Suite ==="

        # Test 1: Project operations
        echo "Test 1: Project CRUD"
        PROJECT_NUM=$(gh-project-create.sh "Test Project" --format json | jq -r '.number')
        gh-project-list.sh | grep "Test Project"
        gh-project-view.sh "$PROJECT_NUM"
        gh-project-delete.sh "$PROJECT_NUM" --confirm

        # Test 2: Epic operations
        echo "Test 2: Epic CRUD"
        EPIC_NUM=$(gh-epic-create.sh "Test Epic" --format json | jq -r '.number')
        gh-epic-list.sh | grep "Test Epic"
        gh-epic-view.sh "$EPIC_NUM"
        gh-epic-update.sh "$EPIC_NUM" --status "In Progress"
        gh-epic-delete.sh "$EPIC_NUM" --confirm

        # Test 3: Story with Epic relationship
        echo "Test 3: Story → Epic relationship"
        EPIC_NUM=$(gh-epic-create.sh "Parent Epic" --format json | jq -r '.number')
        STORY_NUM=$(gh-story-create.sh "Child Story" --epic "$EPIC_NUM" --format json | jq -r '.number')
        gh-epic-view.sh "$EPIC_NUM" | grep "Child Story"
        gh-story-view.sh "$STORY_NUM" | grep "Parent Epic"
        gh-story-delete.sh "$STORY_NUM" --confirm
        gh-epic-delete.sh "$EPIC_NUM" --confirm

        # Test 4: Task with Story relationship
        echo "Test 4: Task → Story relationship"
        EPIC_NUM=$(gh-epic-create.sh "Epic" --format json | jq -r '.number')
        STORY_NUM=$(gh-story-create.sh "Story" --epic "$EPIC_NUM" --format json | jq -r '.number')
        TASK_NUM=$(gh-task-create.sh "Task" --story "$STORY_NUM" --format json | jq -r '.number')
        gh-story-view.sh "$STORY_NUM" | grep "Task"
        gh-task-delete.sh "$TASK_NUM" --confirm
        gh-story-delete.sh "$STORY_NUM" --confirm
        gh-epic-delete.sh "$EPIC_NUM" --confirm

        # Test 5: Bug (standalone)
        echo "Test 5: Bug CRUD"
        BUG_NUM=$(gh-bug-create.sh "Test Bug" --format json | jq -r '.number')
        gh-bug-list.sh | grep "Test Bug"
        gh-bug-update.sh "$BUG_NUM" --priority High
        gh-bug-delete.sh "$BUG_NUM" --confirm

        # Test 6: Spike with Epic
        echo "Test 6: Spike → Epic relationship"
        EPIC_NUM=$(gh-epic-create.sh "Research Epic" --format json | jq -r '.number')
        SPIKE_NUM=$(gh-spike-create.sh "Research Spike" --epic "$EPIC_NUM" --format json | jq -r '.number')
        gh-epic-view.sh "$EPIC_NUM" | grep "Research Spike"
        gh-spike-delete.sh "$SPIKE_NUM" --confirm
        gh-epic-delete.sh "$EPIC_NUM" --confirm

        echo "=== All tests passed! ==="
        ```
      </testing>

      <estimated_effort>3-4 hours</estimated_effort>
    </phase>

    <summary>
      **5 phases, 19-26 hours total effort**

      Phase 1: Foundation (4-6h) - Common library, init, docs
      Phase 2: Project CRUD (2-3h) - 4 project scripts
      Phase 3: Epic & Story (6-8h) - 10 item scripts
      Phase 4: Task/Spike/Bug (4-5h) - 15 item scripts
      Phase 5: Migration (3-4h) - Archive, update skills, test

      **Parallelization opportunity:**
      - Phase 4 scripts can be implemented in parallel (same pattern)
      - Skill updates can be done in parallel
      - Testing can start during Phase 4

      **Critical path:**
      Phase 1 → Phase 2 → Phase 3 → Phase 4 → Phase 5
      (Each phase depends on previous)
    </summary>
  </implementation_phases>

  <quality_standards>
    <help_text>
      <format>
        Every script must provide comprehensive --help following this template:
      </format>

      <template>
```bash
usage() {
  cat << 'EOF'
Usage: SCRIPT_NAME REQUIRED_ARG [OPTIONS]

One-line description of what this script does.

Options:
  REQUIRED_ARG        Description (required)
  --option VALUE      Description (default: DEFAULT)
  --flag              Boolean flag description
  --format json       Output as JSON (default: human-readable)
  --dry-run           Preview without executing
  -h, --help          Show this help

Examples:
  # Common use case description
  SCRIPT_NAME example-arg

  # Advanced use case description
  SCRIPT_NAME example-arg --option value --flag

  # JSON output for scripting
  SCRIPT_NAME example-arg --format json | jq '.field'

Additional notes:
- Requirement or caveat
- Tip or best practice

Learn more: Link to documentation (future)
EOF
}
```
      </template>

      <requirements>
        - Usage line shows positional args and optional flags
        - One-line description (under 80 chars)
        - Options listed with defaults
        - Required vs optional clear (positional = required)
        - At least 2 examples (simple + advanced)
        - Examples use realistic values (not PLACEHOLDER)
        - Additional notes for caveats/requirements
        - Help text under 30 lines (fits one screen)
      </requirements>

      <examples>
        **Good help text:**
        - Clear what script does from first line
        - Options organized (required first, flags last)
        - Examples can be copy-pasted
        - Defaults documented

        **Bad help text:**
        - Vague description "Manages items"
        - No examples
        - Options not explained
        - No defaults shown
      </examples>
    </help_text>

    <error_messages>
      <guidelines>
        **3-part error messages:**
        1. What went wrong (specific)
        2. Why it went wrong (context)
        3. How to fix it (actionable)

        Format:
        ```
        Error: SPECIFIC_PROBLEM

        CONTEXT_OR_REASON

        Fix: CONCRETE_ACTION
        ```
      </guidelines>

      <examples>
        **Good error:**
        ```
        Error: Field 'Status' not found in project.

        This usually means:
        - Field cache is stale
        - Field was renamed in project settings

        Fix: Run 'gh-project-init.sh --refresh-cache' to update
        ```

        **Bad error:**
        ```
        Error: Field not found
        ```

        **Good error:**
        ```
        Error: Issue #42 exists but is not in project.

        The issue is a repository issue but hasn't been added to the project.

        Fix: Add to project first:
        gh project item-add 1 --owner @me --url $(gh issue view 42 --json url -q .url)
        ```

        **Bad error:**
        ```
        Error: Item not in project
        ```

        **Good error:**
        ```
        Error: Not authenticated with GitHub CLI.

        Projects operations require 'project' scope.

        Fix:
        1. gh auth login
        2. gh auth refresh -s project
        ```

        **Bad error:**
        ```
        Error: Auth failed
        ```
      </examples>

      <common_errors>
        **Configuration:**
        - No config file → Point to gh-project-init.sh
        - Invalid config → Show what's wrong, how to fix
        - Missing required field → List available fields

        **API:**
        - Network error → Mention retries, check connection
        - Rate limit → Show wait time, how to check quota
        - Permission denied → Show required permissions

        **Input:**
        - Missing required arg → Show usage, example
        - Invalid option → List valid options
        - Invalid value → Show format, example
      </common_errors>
    </error_messages>

    <exit_codes>
      <standard>
        0 - Success
        1 - General error (default)
        2 - Cancelled by user (--dry-run, confirmation)
        3 - Configuration error (missing config, invalid)
        4 - API error (network, auth, rate limit)
      </standard>

      <usage>
        ```bash
        # Success
        exit 0

        # General error
        die "Error message" 1

        # Configuration error
        die "Config not found. Run: gh-project-init.sh" 3

        # API error
        die "GitHub API error: $response" 4

        # Cancelled
        if [[ "$DRY_RUN" == "true" ]]; then
          log_warn "[DRY-RUN] Would create..."
          exit 2
        fi
        ```
      </usage>

      <consistency>
        All scripts use same exit codes for same conditions:
        - Missing config → 3
        - Network failure → 4
        - User cancellation → 2
        - Invalid argument → 1 (or show help and exit 0)
      </consistency>
    </exit_codes>

    <validation>
      <input_validation>
        **Validate early, fail fast:**

        1. Check required arguments
        2. Check prerequisites (gh, jq, auth)
        3. Load and validate configuration
        4. Validate field names/values
        5. Check resource exists (issue, project)
        6. Proceed with operation

        ```bash
        # Example validation in create script
        [[ -z "$TITLE" ]] && die "Title required. Usage: $(basename "$0") TITLE [OPTIONS]" 1
        validate_prerequisites || exit $?
        load_config || exit $?
        validate_config || exit $?
        ```
      </input_validation>

      <pre_flight_checks>
        **Common library validates:**
        - gh CLI installed
        - jq installed
        - Authenticated with GitHub
        - Project scope authorized
        - Config file exists and valid
        - Field cache present

        ```bash
        validate_prerequisites() {
          command -v jq &>/dev/null || die "jq not found. Install: https://stedolan.github.io/jq/" 1
          gh auth status &>/dev/null || die "Not authenticated. Run: gh auth login && gh auth refresh -s project" 4
        }
        ```
      </pre_flight_checks>
    </validation>

    <testing>
      <unit_tests>
        **Manual unit testing approach:**

        For each script:
        1. Test with valid inputs → success
        2. Test with missing required args → helpful error
        3. Test with invalid options → error with valid options
        4. Test --help → comprehensive output
        5. Test --dry-run → preview without changes
        6. Test --format json → valid JSON output

        Example:
        ```bash
        # Test gh-epic-create.sh
        ./gh-epic-create.sh "Test Epic"  # Should succeed
        ./gh-epic-create.sh  # Should error: title required
        ./gh-epic-create.sh "Test" --status Invalid  # Should error: invalid status
        ./gh-epic-create.sh --help  # Should show help
        ./gh-epic-create.sh "Test" --dry-run  # Should preview
        ./gh-epic-create.sh "Test" --format json  # Should output JSON
        ```
      </unit_tests>

      <integration_tests>
        **Full workflow testing:**

        Test common workflows end-to-end:

        1. **Epic → Stories → Tasks**
           - Create epic
           - Create 2 stories linked to epic
           - Create 3 tasks linked to stories
           - Verify all relationships
           - Update statuses
           - Delete in reverse order

        2. **Bug tracking**
           - Create standalone bug
           - Create bug linked to story
           - Update bug priority
           - Close bug
           - Delete bug

        3. **Spike research**
           - Create spike linked to epic
           - Update spike status
           - Convert spike to story (manual)
           - Delete spike

        **Automated with test-suite.sh (Phase 5)**
      </integration_tests>
    </testing>
  </quality_standards>

  <examples>
    <workflow name="Create Epic with Stories and Tasks">
      <old_way>
```bash
# Old approach with gh-project-item-create.sh

# Create Epic
gh-project-item-create.sh \
  --title "Authentication System" \
  --type Epic \
  --status Todo \
  --priority High \
  --body "Implement OAuth2 and SSO"

# Create Story (manual issue number tracking)
gh-project-item-create.sh \
  --title "OAuth Login" \
  --type "User Story" \
  --parent 1 \
  --status Todo

# Create Task
gh-project-item-create.sh \
  --title "Implement OAuth client" \
  --type Task \
  --parent 2 \
  --status Todo

# Issues:
# - Too many options (confusing)
# - Type must be specified every time
# - Parent relationship not clear (what is issue #1?)
# - Easy to forget required flags
```
      </old_way>

      <new_way>
```bash
# New approach with type-specific scripts

# Create Epic (Type=Epic implicit)
gh-epic-create.sh "Authentication System" \
  --body "Implement OAuth2 and SSO" \
  --priority High

# Create Story (Type="User Story" implicit, parent explicit)
gh-story-create.sh "OAuth Login" \
  --epic 1

# Create Task (Type=Task implicit, parent explicit)
gh-task-create.sh "Implement OAuth client" \
  --story 2

# Benefits:
# - Fewer options (simpler)
# - Type implicit in script name
# - Parent relationship clear (--epic, --story)
# - Hard to misuse (required args positional)
# - Self-documenting (script name tells you what it does)
```
      </new_way>

      <comparison>
        **Simplicity:**
        - Old: 7 flags per create (--title, --type, --status, --priority, --body, --parent, etc.)
        - New: 2-3 flags per create (title positional, --epic/--story for parent, optional fields)

        **Clarity:**
        - Old: `--parent 1` (parent of what type?)
        - New: `--epic 1` (clearly Epic #1)

        **Safety:**
        - Old: Can create Story without parent (invalid hierarchy)
        - New: Story requires --epic (enforced by script)

        **Discoverability:**
        - Old: Must read help to know all --type options
        - New: See gh-epic-*, gh-story-*, etc. in directory listing
      </comparison>
    </workflow>

    <workflow name="Update Item Status">
      <old_way>
```bash
# Old: Generic update script
gh-project-update.sh --issue 42 --status "In Progress"

# Issue: Must know issue #42 exists and is in project
# No indication what type of item it is
```
      </old_way>

      <new_way>
```bash
# New: Type-specific update
gh-epic-update.sh 42 --status "In Progress"

# Benefits:
# - Clear that #42 is an Epic
# - Can't accidentally update wrong type
# - Positional arg (less typing)
```
      </new_way>

      <comparison>
        **Type safety:**
        - Old: Can update any item type (might update Task when you meant Epic)
        - New: Type explicit in script name (can't mix up)

        **Clarity:**
        - Old: Generic "update" (update what?)
        - New: "Update Epic" (clear intent)
      </comparison>
    </workflow>

    <workflow name="List Items by Type and Status">
      <old_way>
```bash
# Old: Generic list with filters
gh-project-list.sh --type Epic --status "In Progress" --format json

# Issues:
# - Many filter combinations possible
# - Easy to forget --type (lists all items)
```
      </old_way>

      <new_way>
```bash
# New: Type-specific list
gh-epic-list.sh --status "In Progress" --format json

# Benefits:
# - Type implicit (can't forget)
# - Fewer options (simpler)
# - Clear what you're listing
```
      </new_way>

      <comparison>
        **Simplicity:**
        - Old: 3 flags (--type, --status, --format)
        - New: 2 flags (--status, --format) - type implicit

        **Safety:**
        - Old: Forget --type → lists all items (slow, wrong results)
        - New: Can't forget type (it's in the script name)
      </comparison>
    </workflow>

    <workflow name="Configuration and Initialization">
      <old_way>
```bash
# Old: Multiple setup scripts (confusing)
gh-project-setup-init.sh --project 1
# or
gh-project-setup-apply.sh config.json
# or
gh-project-setup-clone.sh --from-project 1 --to-project 2

# Issues:
# - Three different ways to initialize
# - Unclear when to use which
# - Clone feature rarely used (YAGNI violation)
```
      </old_way>

      <new_way>
```bash
# New: Single init script
gh-project-init.sh --project 1

# Benefits:
# - One way to initialize (KISS)
# - Auto-detects owner and repo (less typing)
# - Clear purpose (no confusion)
# - YAGNI: Removed unused clone/apply variants
```
      </new_way>

      <comparison>
        **Simplicity:**
        - Old: 3 scripts for configuration (which one to use?)
        - New: 1 script (obvious choice)

        **Auto-detection:**
        - Old: Must specify owner and repo
        - New: Auto-detects from gh auth and git remote

        **YAGNI:**
        - Old: Clone feature never used in practice
        - New: Removed (can add back if needed)
      </comparison>
    </workflow>
  </examples>

  <open_questions>
    <questions>
      1. **Projects V1 compatibility:**
         - Question: Should scripts detect and reject Projects V1?
         - Recommendation: Yes - detect and fail with "Projects V2 required" message
         - Rationale: V1 is deprecated by GitHub, different API entirely

      2. **Rollback on partial failure:**
         - Question: If "create issue" succeeds but "add to project" fails, delete the issue?
         - Recommendation: No rollback in v1 (complex), but clear error message showing issue URL
         - Rationale: User can manually add to project or delete issue
         - Future: Add --atomic flag for rollback behavior (v2)

      3. **Draft issues:**
         - Question: Support draft issues (project-only) or always use repository issues?
         - Recommendation: Repository issues only in v1 (default), add draft support in v2 if needed
         - Rationale: 99% use case is repository issues (full GitHub functionality)

      4. **Pagination:**
         - Question: Handle projects with >30 items per type?
         - Recommendation: Document limitation in v1, add pagination in v2 if needed
         - Rationale: YAGNI - most projects have <30 epics

      5. **Multi-project support:**
         - Question: Support working with multiple projects (switch contexts)?
         - Recommendation: Not in v1 (single config file), add in v2 if needed
         - Rationale: Solo development typically uses one project per repo

      6. **Field validation:**
         - Question: Validate field values against options or let API reject?
         - Recommendation: Validate in script (better error messages)
         - Rationale: "Invalid status" vs API error message

      7. **Sub-issue deletion:**
         - Question: When deleting Epic, auto-delete child Stories?
         - Recommendation: No (by design) - warn user about orphaned children
         - Rationale: Prevents accidental data loss, user makes explicit choice
    </questions>
  </open_questions>

  <assumptions>
    <technical_assumptions>
      • Users have gh CLI 2.0+ installed
      • Users are authenticated with project scope
      • Users have initialized config (gh-project-init.sh)
      • Projects use standard fields: "Type", "Status", "Priority" (lowercase in JSON)
      • One project per repository (config stored per repo)
      • Field options static after setup (rare changes)
      • Items limited to <30 per type (pagination not needed in v1)
    </technical_assumptions>

    <workflow_assumptions>
      • SCRUM/Kanban methodology (Epic → Story → Task hierarchy)
      • Status workflow: Todo → In Progress → Done (+ Blocked)
      • Priority levels: Low, Medium, High, Critical
      • Item types: Epic, User Story, Task, Bug, Spike
      • Parent-child: Epic ← Story ← Task (two-level hierarchy)
      • Bugs and Spikes can be standalone or children
    </workflow_assumptions>

    <usage_assumptions>
      • Scripts used by humans (interactive CLI)
      • Solo development or small teams
      • Single project context (not switching frequently)
      • Repository issues preferred over draft issues
      • Users understand GitHub Projects V2 concepts
    </usage_assumptions>
  </assumptions>

  <dependencies>
    <required>
      • GitHub CLI (gh) 2.0+ - Projects V2 support
      • jq 1.6+ - JSON parsing
      • bash 4.0+ or zsh 5.0+ - Shell environment
      • git 2.0+ - Auto-detection of repo
      • GitHub Projects V2 - NOT V1
    </required>

    <optional>
      • GitHub auth with project scope - gh auth refresh -s project
    </optional>
  </dependencies>

  <confidence>high</confidence>

  <next_steps>
    **Ready for implementation!**

    **Option A: Automated sequential execution**
    - Implement all 5 phases in order
    - Fully automated with verification
    - Total time: 19-26 hours

    **Option B: Manual phase-by-phase**
    - Implement Phase 1, test
    - Implement Phase 2, test
    - Continue through Phase 5
    - More control, can adjust

    **Option C: Parallel implementation**
    - Phase 1 first (foundation)
    - Phase 4 items in parallel (same pattern)
    - Phase 5 last (migration)
    - Faster if multiple developers

    **Recommended: Option B (manual phase-by-phase)**
    - Test each phase thoroughly
    - Adjust based on learnings
    - Lower risk
  </next_steps>
</implementation_plan>

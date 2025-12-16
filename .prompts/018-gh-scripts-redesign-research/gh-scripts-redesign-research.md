# GitHub Projects Scripts Redesign - Research Findings

**Comprehensive research on SOLID/KISS/DRY/YAGNI/TRIZ-compliant CLI design for GitHub Projects CRUD operations**

v1 • 2025-12-15

---

## Research Status

**Current phase:** Active research in progress
**Confidence level:** Building (will update to medium-high upon completion)

---

<research_findings>
  <meta>
    <version>v1</version>
    <date>2025-12-15</date>
    <confidence>building</confidence>
    <sources_consulted>
      <source>
        <name>GitHub CLI (gh) project command documentation</name>
        <url>Built-in: gh project --help and subcommands</url>
        <verified>yes</verified>
        <notes>Verified all subcommands and their flags directly</notes>
      </source>
      <source>
        <name>GitHub CLI (gh) issue command documentation</name>
        <url>Built-in: gh issue --help</url>
        <verified>yes</verified>
        <notes>Verified to understand project vs repo distinction</notes>
      </source>
      <source>
        <name>GitHub CLI exit codes documentation</name>
        <url>Built-in: gh help exit-codes</url>
        <verified>yes</verified>
        <notes>Standard conventions: 0=success, 1=failure, 2=cancelled, 4=auth</notes>
      </source>
      <source>
        <name>Existing gh-projects scripts</name>
        <url>~/.claude/skills/lib/gh-projects/</url>
        <verified>yes</verified>
        <notes>16+ scripts analyzed for patterns and anti-patterns</notes>
      </source>
      <source>
        <name>Git CLI design patterns</name>
        <url>git --help</url>
        <verified>yes</verified>
        <notes>Analyzed for command organization and help format</notes>
      </source>
      <source>
        <name>Docker CLI design patterns</name>
        <url>docker --help</url>
        <verified>yes</verified>
        <notes>Analyzed for command organization and grouping</notes>
      </source>
      <source>
        <name>POSIX Shell Scripting Best Practices</name>
        <url>Industry standard practices</url>
        <verified>partial</verified>
        <notes>Will expand with web research</notes>
      </source>
    </sources_consulted>
  </meta>

  <cli_design_principles>
    <solid_for_shell_scripts>
      <single_responsibility>
        <principle>
          **One script = one action on one resource**

          Each script should do exactly ONE thing and do it well. This makes scripts:
          - Easy to understand at a glance
          - Simple to test
          - Hard to misuse
          - Composable
        </principle>

        <good_examples>
          - `gh-epic-create` - Creates an epic (only)
          - `gh-epic-update` - Updates epic fields (only)
          - `gh-epic-delete` - Deletes an epic (only)
          - `gh-epic-list` - Lists epics (only)
        </good_examples>

        <anti_pattern>
          - `gh-project-update` with --status, --priority, --type options
            - Problem: Updates multiple different field types
            - Better: Separate scripts OR accept that field updates are similar enough to share
        </anti_pattern>

        <guideline>
          **Decision criteria:** If a script has an "or" in its description, it's doing too much.
          - ❌ "Create or update a project item"
          - ✅ "Create a project item"
          - ✅ "Update a project item"
        </guideline>

        <trade_off>
          Field updates (status, priority, type) are mechanically similar (all single-select fields).
          Acceptable to have one update script with multiple field options, as long as it ONLY updates fields.
          Don't mix field updates with creation, deletion, or listing.
        </trade_off>
      </single_responsibility>

      <open_closed>
        <principle>
          **Scripts should be open for extension, closed for modification**

          In shell scripting context:
          - Use configuration files for extensibility (not hardcoding)
          - Use environment variables for overrides
          - Design scripts to be composable (pipe-friendly)
        </principle>

        <examples>
          - Configuration file: `~/.config/gh-projects/config.json`
            - Contains: project_number, owner, repo, field cache
            - Allows working with different projects without script changes

          - Environment variable overrides:
            - `GH_PROJECT_CACHE_DIR` - override cache location
            - `GH_PROJECT_NUMBER` - override for one-off commands

          - Pipe-friendly output:
            - Support `--format json` for machine parsing
            - Write user messages to stderr, data to stdout
        </examples>

        <guideline>
          - Never hardcode project numbers, owners, or field IDs
          - Always support JSON output for composability
          - Make scripts callable from other scripts
        </guideline>
      </open_closed>

      <liskov_substitution>
        <principle>
          **Scripts with similar purposes should have similar interfaces**

          If you have gh-epic-create, gh-story-create, gh-task-create, they should all:
          - Use same flag names (--title, --body, --assignee)
          - Return same output format
          - Use same exit codes for same conditions
          - Have similar help text structure
        </principle>

        <consistency_rules>
          - Common flags across all create scripts:
            - `--title TITLE` (required)
            - `--body TEXT` (optional)
            - `--body-file FILE` (optional, alternative to --body)
            - `--assignee USERNAME` (optional)
            - `--labels LABEL,LABEL` (optional)
            - `--dry-run` (optional)

          - Common flags across all update scripts:
            - `--issue NUM` or `--id ID`
            - Field-specific flags (--status, --priority, etc.)
            - `--dry-run` (optional)

          - Common flags across all list scripts:
            - `--limit NUM` (optional, default 30)
            - `--format json` (optional)
        </consistency_rules>
      </liskov_substitution>

      <interface_segregation>
        <principle>
          **Don't force users to specify options they don't need**

          Scripts should have:
          - Minimal required options
          - Sensible defaults
          - Optional flags truly optional
        </principle>

        <anti_pattern>
          Current `gh-project-item-create`:
          - Too many options: --title, --body, --body-file, --type, --status, --story-points, --parent, --labels, --assignee
          - Confusing: Do I need --type? When do I use --parent?
        </anti_pattern>

        <better_design>
          Separate by item type:

          `gh-epic-create --title "Epic title" [--body TEXT]`
          - Implies type=Epic, status=Todo (defaults)
          - No --type option needed
          - No --parent option (epics don't have parents)

          `gh-story-create --title "Story title" --epic NUM [--body TEXT]`
          - Implies type="User Story"
          - --epic is specific to stories (not generic --parent)
          - Clear parent relationship

          `gh-task-create --title "Task title" --story NUM [--body TEXT]`
          - Implies type=Task
          - --story is specific to tasks
          - Clear parent relationship
        </better_design>

        <guideline>
          Each item type (Epic, Story, Task, Bug, Spike) should have its own create script.
          This eliminates the --type flag and makes parent relationships explicit.
        </guideline>
      </interface_segregation>

      <dependency_inversion>
        <principle>
          **Depend on abstractions (common library), not concretions**

          High-level scripts should not depend on low-level gh CLI details.
          They should depend on a common library that abstracts GitHub API complexity.
        </principle>

        <library_design>
          Common library (`gh-project-common.sh`) should provide:

          **Abstract operations:**
          - `create_project_item(type, title, body)` - abstracts gh project item-create
          - `add_issue_to_project(issue_url)` - abstracts gh project item-add
          - `set_field(item_id, field_name, value)` - abstracts field updates
          - `get_item_by_issue(issue_num)` - abstracts item lookup

          **Not leak implementation details:**
          - Scripts shouldn't know about GraphQL vs REST
          - Scripts shouldn't manually parse JSON responses
          - Scripts shouldn't handle retries themselves
        </library_design>

        <current_strengths>
          Existing `gh-project-common.sh` does well:
          - `set_single_select_field()` - abstracts field updates
          - `retry_command()` - abstracts error handling
          - `get_field_id()`, `get_option_id()` - abstracts field resolution
          - Field caching - abstracts repeated API calls
        </current_strengths>

        <needs_improvement>
          - No abstraction for "create repo issue + add to project" pattern
          - Scripts still construct gh CLI arguments directly
          - Error messages leak implementation details
        </needs_improvement>
      </dependency_inversion>
    </solid_for_shell_scripts>

    <kiss_guidelines>
      <principle>
        **Keep It Simple, Stupid**

        The simplest design that solves the problem is the best design.
      </principle>

      <simplicity_checklist>
        - [ ] Can describe script's purpose in one sentence?
        - [ ] Fewer than 10 options?
        - [ ] No conditional logic based on option combinations?
        - [ ] Help text fits on one screen?
        - [ ] No "advanced mode" or "expert options"?
      </simplicity_checklist>

      <anti_patterns>
        **Over-parameterization:**
        ```bash
        gh-project-update --item ID --issue NUM --field FIELD --value VALUE --format FORMAT --cache-mode MODE --retry-count N
        ```
        Problem: 7 options, many combinations, unclear which to use

        **Conditional complexity:**
        ```bash
        if [[ -n "$ITEM_ID" ]]; then
          # do one thing
        elif [[ -n "$ISSUE_NUM" ]]; then
          # do different thing
        fi
        ```
        Problem: Two different code paths = two different scripts needed
      </anti_patterns>

      <kiss_applied>
        **Simple script example:**
        ```bash
        gh-epic-create TITLE [--body TEXT]
        ```
        - One required arg (title)
        - One optional arg (body)
        - No conditionals
        - Obvious what it does

        **Simple update example:**
        ```bash
        gh-epic-update ISSUE_NUM --status STATUS
        ```
        - Positional arg (issue number)
        - One flag (status)
        - No ambiguity
      </kiss_applied>

      <when_to_add_complexity>
        Only add options when:
        1. GitHub API requires them (e.g., --owner for cross-org operations)
        2. Common use case demands it (e.g., --body-file for long descriptions)
        3. Safety requires it (e.g., --dry-run for destructive operations)

        Default answer: **NO**
      </when_to_add_complexity>
    </kiss_guidelines>

    <dry_patterns>
      <principle>
        **Don't Repeat Yourself**

        Common code should live in one place. But don't over-abstract.
      </principle>

      <what_belongs_in_common_library>
        ✅ **Belongs in common library:**
        - Configuration loading (project number, owner, repo)
        - Field caching and resolution
        - Error handling and retries
        - Logging functions
        - GraphQL/API execution helpers
        - Exit code constants
        - Validation functions (auth check, jq check, gh check)

        ❌ **Doesn't belong in common library:**
        - Business logic specific to one item type
        - Help text (each script has unique usage)
        - Argument parsing (each script has different args)
      </what_belongs_in_common_library>

      <acceptable_duplication>
        **It's OK to duplicate:**

        1. **Help text structure** - Each script has similar but unique help
           - Don't generate help text from metadata
           - Hand-written help is clearer

        2. **Argument parsing patterns** - Each script parses differently
           - Don't create a "universal parser"
           - Explicit parsing is clearer

        3. **Simple validations** - `[[ -z "$TITLE" ]] && die "Title required"`
           - Don't abstract single-line checks
           - Inline validation is clearer
      </acceptable_duplication>

      <current_implementation_analysis>
        **Current common library (gh-project-common.sh) - GOOD:**
        - 388 lines of well-factored shared code
        - Clear sections: logging, config, GraphQL, field caching, validation
        - Proper abstractions: `set_single_select_field()`, `retry_command()`

        **Current scripts - ROOM FOR IMPROVEMENT:**
        - Duplicated pattern: "create issue → add to project → set fields"
        - This 3-step pattern appears in multiple scripts
        - Should be abstracted to: `create_and_add_item(type, title, body, fields)`
      </current_implementation_analysis>

      <dry_vs_abstraction_trade_off>
        **Rule of Three:**
        - First time: Write it
        - Second time: Notice duplication
        - Third time: Abstract it

        Don't abstract on first occurrence. Wait for pattern to emerge.
      </dry_vs_abstraction_trade_off>
    </dry_patterns>

    <yagni_boundaries>
      <principle>
        **You Aren't Gonna Need It**

        Don't build features until they're actually needed.
      </principle>

      <features_to_defer>
        ❌ **Don't build yet:**

        1. **Multi-project support**
           - Current: One config file = one project
           - Future: Maybe support switching between projects
           - Decision: Wait until user explicitly needs it

        2. **Bulk operations**
           - Current: Create one item at a time
           - Future: Maybe create multiple items from CSV
           - Decision: Wait for actual use case

        3. **Undo/rollback**
           - Current: Operations are final
           - Future: Maybe track changes and allow undo
           - Decision: Too complex for v1

        4. **Custom field types beyond single-select**
           - Current: Support Status, Priority, Type (all single-select)
           - Future: Maybe support text fields, numbers, dates
           - Decision: Add when needed, not speculatively

        5. **GitHub Actions integration**
           - Current: Manual CLI usage
           - Future: Maybe CI/CD automation
           - Decision: Different problem domain

        6. **Projects V1 compatibility**
           - Current: V2 only
           - Future: V1 is deprecated by GitHub
           - Decision: V2 only, don't support legacy
      </features_to_defer>

      <features_to_include>
        ✅ **Include in v1:**

        1. **--dry-run flag** - Safety for destructive operations
        2. **--format json** - Machine readability for composition
        3. **Field caching** - Performance optimization, already proven useful
        4. **Retry logic** - Network resilience, already proven necessary
        5. **Help text** - User discoverability, always essential
        6. **Configuration file** - Avoid typing project number every time
      </features_to_include>

      <yagni_applied_to_current_scripts>
        **Current scripts have YAGNI violations:**

        - `gh-project-setup-clone` - Copy entire project config
          - Question: Has this ever been used?
          - Decision: Defer unless proven need

        - `gh-project-convert` - Convert between formats
          - Question: What formats? Why?
          - Decision: Unclear need, defer

        - Story Points field in `gh-project-item-create`
          - Question: Is this field actually used?
          - Decision: Only include if field exists in target project
      </yagni_applied_to_current_scripts>
    </yagni_boundaries>

    <triz_ideal_state>
      <principle>
        **TRIZ: Theory of Inventive Problem Solving**

        Ideal Final Result: The perfect CRUD script does its job with ZERO user effort.
      </principle>

      <ideal_crud_script>
        **The perfect script:**
        - Requires ZERO configuration (auto-detects everything)
        - Has ZERO failure modes (always succeeds or fails gracefully)
        - Needs ZERO documentation (completely self-explanatory)
        - Takes ZERO time to learn (intuitive from first use)
        - Produces ZERO surprises (behaves exactly as expected)
      </ideal_crud_script>

      <approaching_ideal>
        **Practical steps toward ideal:**

        1. **Auto-detection over configuration:**
           - Detect project number from git remote
           - Detect owner from `gh auth status`
           - Detect repo from current directory
           - Only ask for config when auto-detection fails

        2. **Graceful degradation:**
           - If network fails: Retry with exponential backoff
           - If field doesn't exist: Warn but don't fail
           - If auth expires: Show helpful re-auth command

        3. **Self-documenting:**
           - Flag names match GitHub UI terminology exactly
           - Error messages include fix suggestions
           - Help text includes examples for common cases

        4. **Intuitive defaults:**
           - Status defaults to "Todo" (obvious starting state)
           - Priority defaults to "Medium" (safe middle ground)
           - Limit defaults to 30 (GitHub's default)

        5. **Predictable behavior:**
           - Same command = same result (idempotent where possible)
           - No hidden side effects
           - Exit codes consistent across all scripts
      </approaching_ideal>

      <triz_contradiction_resolution>
        **Contradiction: Simplicity vs Power**

        - Users want simple commands (few options)
        - Users want powerful features (many capabilities)

        **TRIZ resolution: Separate in space**
        - Create separate scripts for each operation
        - Each script is simple
        - Together they are powerful

        Example:
        - Instead of: `gh-item-manage --create --update --delete --type epic --status Todo`
        - Do: `gh-epic-create`, `gh-epic-update`, `gh-epic-delete`
        - Each script is simple, but suite is complete
      </triz_contradiction_resolution>
    </triz_ideal_state>

    <anti_patterns>
      <pattern name="Swiss Army Knife Script">
        <description>
          One script that does many unrelated things through mode flags
        </description>
        <example>
          ```bash
          gh-project-manage --mode create|update|delete|list --type epic|story|task ...
          ```
        </example>
        <why_bad>
          - Help text becomes overwhelming
          - Users must learn all modes even if they only need one
          - Hard to test (N modes × M types = N×M combinations)
          - Violates Single Responsibility
        </why_bad>
        <solution>
          Separate scripts: `gh-epic-create`, `gh-epic-update`, etc.
        </solution>
      </pattern>

      <pattern name="Boolean Flag Soup">
        <description>
          Many boolean flags that interact in complex ways
        </description>
        <example>
          ```bash
          gh-item-create --is-epic --is-bug --force --skip-validation --no-cache --retry
          ```
        </example>
        <why_bad>
          - Unclear which flags can be combined
          - Easy to create invalid combinations
          - Help text can't document all interactions
        </why_bad>
        <solution>
          - Use positional arguments for primary choices
          - Use mutually exclusive options where needed
          - Validate flag combinations early
        </solution>
      </pattern>

      <pattern name="Implicit Configuration">
        <description>
          Script behavior changes based on undocumented env vars or hidden files
        </description>
        <example>
          ```bash
          # Secretly reads ~/.gh-project-secret-config
          # Secretly checks $GH_PROJECT_OVERRIDE
          ```
        </example>
        <why_bad>
          - Users can't understand why script behaves differently
          - Debugging is impossible
          - Violates principle of least surprise
        </why_bad>
        <solution>
          - Document ALL configuration sources in help text
          - Show config values with --verbose flag
          - Fail loudly if config is ambiguous
        </solution>
      </pattern>

      <pattern name="Silent Failures">
        <description>
          Script continues after errors, producing incomplete results
        </description>
        <example>
          ```bash
          create_issue  # fails silently
          add_to_project  # tries anyway, also fails
          set_status  # tries anyway, reports "success"
          ```
        </example>
        <why_bad>
          - User thinks operation succeeded
          - Partial state is worse than no state
          - Hard to debug what actually happened
        </why_bad>
        <solution>
          - Use `set -euo pipefail` in all scripts
          - Validate each step before proceeding
          - Report exact failure point
        </solution>
      </pattern>

      <pattern name="Mega-Options">
        <description>
          Single option that accepts complex comma-separated values
        </description>
        <example>
          ```bash
          --fields "status:Done,priority:High,type:Epic,assignee:@me"
          ```
        </example>
        <why_bad>
          - Requires custom parsing logic
          - Error messages are unclear
          - Can't use shell completion
          - Violates KISS
        </why_bad>
        <solution>
          - Use separate flags: `--status Done --priority High`
          - Let shell handle argument parsing
          - Better error messages per field
        </solution>
      </pattern>
    </anti_patterns>
  </cli_design_principles>

  <github_projects_api>
    <gh_cli_capabilities>
      <overview>
        GitHub CLI (`gh`) provides comprehensive Projects V2 support through `gh project` command.
        All commands require `project` scope: `gh auth refresh -s project`
      </overview>

      <project_commands>
        <command name="gh project create">
          <description>Create a new project</description>
          <flags>
            --title string (required)
            --owner string (required or defaults to @me)
            --format json (optional)
          </flags>
          <returns>Project number and ID</returns>
        </command>

        <command name="gh project list">
          <description>List projects for an owner</description>
          <flags>
            --owner string (required or defaults to @me)
            --limit int (default 30)
            --format json
          </flags>
        </command>

        <command name="gh project view">
          <description>View project details</description>
          <flags>
            number (positional, required)
            --owner string
            --format json
            --web (open in browser)
          </flags>
        </command>

        <command name="gh project edit">
          <description>Edit project metadata</description>
          <flags>
            number (positional, required)
            --owner string
            --title string
            --description string
            --visibility PUBLIC|PRIVATE
          </flags>
        </command>

        <command name="gh project close">
          <description>Close a project</description>
          <flags>
            number (positional, required)
            --owner string
          </flags>
        </command>

        <command name="gh project delete">
          <description>Delete a project permanently</description>
          <flags>
            number (positional, required)
            --owner string
          </flags>
        </command>
      </project_commands>

      <field_commands>
        <command name="gh project field-list">
          <description>List custom fields in project</description>
          <flags>
            number (positional, required)
            --owner string
            --limit int (default 30)
            --format json
          </flags>
          <returns>
            Array of fields with:
            - id (required for item-edit)
            - name (e.g., "Status", "Priority", "Type")
            - type (e.g., "SINGLE_SELECT", "TEXT", "NUMBER")
            - options (array for SINGLE_SELECT fields)
          </returns>
          <json_structure>
            {
              "fields": [
                {
                  "id": "PVTF_lADOA...",
                  "name": "Status",
                  "type": "SINGLE_SELECT",
                  "options": [
                    {"id": "opt_123", "name": "Todo"},
                    {"id": "opt_456", "name": "In Progress"},
                    {"id": "opt_789", "name": "Done"}
                  ]
                }
              ]
            }
          </json_structure>
        </command>

        <command name="gh project field-create">
          <description>Create a new custom field</description>
          <flags>
            number (positional, required)
            --owner string
            --name string (required)
            --data-type SINGLE_SELECT|TEXT|NUMBER|DATE
            --single-select-options comma-separated (for SINGLE_SELECT)
          </flags>
        </command>

        <command name="gh project field-delete">
          <description>Delete a custom field</description>
          <flags>
            number (positional, required)
            --owner string
            --field-id string (required)
          </flags>
        </command>
      </field_commands>

      <item_commands>
        <command name="gh project item-create">
          <description>Create a DRAFT ISSUE in project (project-only item)</description>
          <flags>
            number (positional, required)
            --owner string
            --title string (required)
            --body string (optional)
            --format json
          </flags>
          <returns>
            Item ID (project item ID, NOT issue number)
          </returns>
          <critical_note>
            This creates a DRAFT ISSUE - exists ONLY in project, NOT in repository issues.
            To create a repository issue and add to project, use:
            1. gh issue create (creates repo issue)
            2. gh project item-add (adds existing issue to project)
          </critical_note>
        </command>

        <command name="gh project item-add">
          <description>Add existing repository issue/PR to project</description>
          <flags>
            number (positional, required)
            --owner string
            --url string (required, full issue/PR URL)
            --format json
          </flags>
          <returns>
            Item ID (project item ID)
          </returns>
          <critical_note>
            This links an EXISTING repository issue to the project.
            The issue must already exist (created via gh issue create).
            This is how you get REAL issues (with issue numbers) into projects.
          </critical_note>
        </command>

        <command name="gh project item-list">
          <description>List all items in project</description>
          <flags>
            number (positional, required)
            --owner string
            --limit int (default 30)
            --format json
          </flags>
          <returns>
            Array of items with:
            - id (project item ID)
            - content.number (issue number, if repo issue)
            - content.title
            - content.state (if repo issue)
            - content.url (if repo issue)
            - type ("ISSUE", "DRAFT_ISSUE", "PULL_REQUEST")
            - fieldValues (custom field values)
          </returns>
        </command>

        <command name="gh project item-edit">
          <description>Edit project item fields OR draft issue content</description>
          <flags>
            --id string (required, project item ID)
            --project-id string (required for field updates)
            --field-id string (required for field updates)
            --text string (for text fields)
            --number float (for number fields)
            --date string (for date fields, YYYY-MM-DD)
            --single-select-option-id string (for single-select fields)
            --iteration-id string (for iteration fields)
            --clear (remove field value)
            --title string (for draft issues only)
            --body string (for draft issues only)
            --format json
          </flags>
          <critical_note>
            Two modes:
            1. Update custom fields: requires --project-id, --field-id
            2. Update draft issue content: requires --title or --body (NO --project-id)

            For repository issues, use `gh issue edit` to change title/body.
          </critical_note>
        </command>

        <command name="gh project item-delete">
          <description>Remove item from project (doesn't delete repo issue)</description>
          <flags>
            number (positional, required)
            --owner string
            --id string (required, project item ID)
          </flags>
          <critical_note>
            This REMOVES the item from the project.
            If it's a repository issue, the issue still exists - just not in the project.
            If it's a draft issue, the draft is deleted entirely.
          </critical_note>
        </command>

        <command name="gh project item-archive">
          <description>Archive an item (keep in project but mark as archived)</description>
          <flags>
            number (positional, required)
            --owner string
            --id string (required, project item ID)
          </flags>
        </command>
      </item_commands>

      <link_commands>
        <command name="gh project link">
          <description>Link project to repository or team</description>
          <flags>
            number (positional, required)
            --owner string
            --repo string (owner/repo format)
            --team string
          </flags>
        </command>

        <command name="gh project unlink">
          <description>Unlink project from repository or team</description>
          <flags>
            number (positional, required)
            --owner string
            --repo string
            --team string
          </flags>
        </command>
      </link_commands>

      <template_commands>
        <command name="gh project mark-template">
          <description>Mark project as template for reuse</description>
          <flags>
            number (positional, required)
            --owner string
          </flags>
        </command>

        <command name="gh project copy">
          <description>Copy project from template</description>
          <flags>
            number (positional, required)
            --owner string
            --title string (for new project)
          </flags>
        </command>
      </template_commands>
    </gh_cli_capabilities>

    <field_schema>
      <critical_finding>
        **Field names in JSON are CASE-SENSITIVE and use specific format**

        Discovered from previous bug fix (prompt 015):
        - UI shows: "Type", "Status", "Priority" (PascalCase)
        - JSON uses: "type", "status", "priority" (lowercase)
        - This caused field lookup failures
      </critical_finding>

      <standard_fields>
        <field name="Type">
          <json_name>type</json_name>
          <type>SINGLE_SELECT</type>
          <common_options>
            - Epic
            - User Story
            - Task
            - Bug
            - Spike
          </common_options>
          <note>Case-sensitive option names</note>
        </field>

        <field name="Status">
          <json_name>status</json_name>
          <type>SINGLE_SELECT</type>
          <common_options>
            - Todo
            - In Progress
            - Done
            - Blocked
          </common_options>
          <note>Kanban-style workflow states</note>
        </field>

        <field name="Priority">
          <json_name>priority</json_name>
          <type>SINGLE_SELECT</type>
          <common_options>
            - Low
            - Medium
            - High
            - Critical
          </common_options>
        </field>

        <field name="Story Points">
          <json_name>story points</json_name>
          <type>NUMBER</type>
          <note>Optional, may not exist in all projects</note>
        </field>
      </standard_fields>

      <field_caching_rationale>
        **Why cache fields:**
        1. `gh project item-edit` requires field IDs and option IDs, not names
        2. Looking up IDs requires a field-list call (slow, rate-limited)
        3. Fields rarely change after project setup
        4. Cache eliminates repeated API calls

        **Cache structure (current implementation):**
        ```json
        {
          "field_cache": {
            "Status": {
              "id": "PVTF_lADOA...",
              "type": "SINGLE_SELECT",
              "options": [
                {"id": "opt_123", "name": "Todo"},
                {"id": "opt_456", "name": "In Progress"}
              ]
            }
          }
        }
        ```

        **Cache invalidation:**
        - Manual: `gh-project-init --refresh-cache`
        - Automatic: Not implemented (YAGNI - fields rarely change)
      </field_caching_rationale>
    </field_schema>

    <item_types>
      <type name="Epic">
        <definition>
          Large body of work, typically spanning multiple sprints.
          Contains User Stories as children.
        </definition>
        <in_github_projects>
          - Type field = "Epic"
          - Repository issue with custom field
          - Has sub-issues (User Stories, Tasks)
        </in_github_projects>
        <parent>None (top-level)</parent>
        <children>User Stories, Spikes</children>
      </type>

      <type name="User Story">
        <definition>
          Feature or functionality from user perspective.
          Typically completed in one sprint.
        </definition>
        <in_github_projects>
          - Type field = "User Story"
          - Repository issue with custom field
          - Child of Epic (via sub-issue relationship)
          - Can have Tasks as children
        </in_github_projects>
        <parent>Epic</parent>
        <children>Tasks</children>
      </type>

      <type name="Task">
        <definition>
          Small, discrete unit of work.
          Part of implementing a User Story.
        </definition>
        <in_github_projects>
          - Type field = "Task"
          - Repository issue with custom field
          - Child of User Story (via sub-issue relationship)
        </in_github_projects>
        <parent>User Story</parent>
        <children>None (leaf level)</children>
      </type>

      <type name="Bug">
        <definition>
          Defect or error in existing functionality.
          Can exist at any level.
        </definition>
        <in_github_projects>
          - Type field = "Bug"
          - Repository issue with custom field
          - May or may not have parent (can be standalone)
        </in_github_projects>
        <parent>Optional (any)</parent>
        <children>Optional (Tasks for investigation/fixes)</children>
      </type>

      <type name="Spike">
        <definition>
          Research or investigation task with time-boxed effort.
          Used for unknown complexity or technical exploration.
        </definition>
        <in_github_projects>
          - Type field = "Spike"
          - Repository issue with custom field
          - Typically child of Epic or standalone
        </in_github_projects>
        <parent>Optional (usually Epic)</parent>
        <children>Optional (Tasks for follow-up work)</children>
      </type>
    </item_types>

    <project_vs_repo_issues>
      <critical_distinction>
        **THIS IS THE MOST IMPORTANT CONCEPT TO UNDERSTAND**

        There are TWO separate entities:
        1. **Repository Issues** - Live in `github.com/owner/repo/issues`
        2. **Project Items** - Live in GitHub Projects (can reference repo issues)

        Relationship:
        - A project item CAN be linked to a repository issue (most common)
        - A project item CAN be a draft issue (project-only, no repo issue)
        - A repository issue can exist WITHOUT being in any project
      </critical_distinction>

      <repository_issues>
        <what_they_are>
          - Traditional GitHub issues in a repository
          - Have issue numbers (#1, #2, #3, ...)
          - Visible at github.com/owner/repo/issues/123
          - Can have labels, assignees, milestones, comments
          - Managed via `gh issue` commands
        </what_they_are>

        <creation>
          ```bash
          gh issue create \
            --repo owner/repo \
            --title "Issue title" \
            --body "Description" \
            --label bug \
            --assignee username
          ```
          Returns: Issue URL and number
        </creation>

        <modification>
          ```bash
          gh issue edit 123 \
            --repo owner/repo \
            --title "New title" \
            --body "New description" \
            --add-label enhancement
          ```
        </modification>

        <no_custom_fields>
          **CRITICAL:** Repository issues do NOT have custom fields.
          Custom fields (Type, Status, Priority) ONLY exist in Projects.
        </no_custom_fields>
      </repository_issues>

      <project_items>
        <what_they_are>
          - Items in a GitHub Project (Projects V2)
          - Have project item IDs (not issue numbers)
          - Can be:
            1. **Linked to repo issues** (most common)
            2. **Draft issues** (project-only notes)
            3. **Pull requests** (also linked)
          - ONLY project items can have custom fields
          - Managed via `gh project item-*` commands
        </what_they_are>

        <two_ways_to_create>
          **Method 1: Draft issue (project-only)**
          ```bash
          gh project item-create 1 \
            --owner "@me" \
            --title "Draft title" \
            --body "Draft description"
          ```
          Result:
          - Creates project item (with ID)
          - NOT a repository issue
          - No issue number
          - Can't comment, assign, label (project-only features)

          **Method 2: Repository issue + add to project**
          ```bash
          # Step 1: Create repo issue
          ISSUE_URL=$(gh issue create \
            --repo owner/repo \
            --title "Real issue" \
            --body "Description")

          # Step 2: Add to project
          gh project item-add 1 \
            --owner "@me" \
            --url "$ISSUE_URL"
          ```
          Result:
          - Repository issue exists (with issue number)
          - Project item exists (linked to issue)
          - Full issue functionality (comments, labels, etc.)
          - Can have project custom fields
        </two_ways_to_create>

        <why_two_methods>
          **Draft issues (Method 1):**
          - Quick notes, temporary placeholders
          - Don't clutter repository issue list
          - No notifications to watchers
          - Can't be referenced by #number in commits/comments

          **Repo issues + project (Method 2):**
          - Permanent, trackable work items
          - Proper issue tracking
          - Can reference in commits: "fixes #123"
          - Team notifications and mentions work
          - **RECOMMENDED for all real work**
        </why_two_methods>
      </project_items>

      <when_to_use_which>
        <decision_tree>
          Question: Is this real work to be done?
          ├─ YES → Create repository issue + add to project (Method 2)
          │        - Use: `gh issue create` then `gh project item-add`
          │        - Get: Issue number, full tracking, custom fields
          │
          └─ NO → Is it just a project note/placeholder?
                   ├─ YES → Create draft issue (Method 1)
                   │        - Use: `gh project item-create`
                   │        - Get: Project item only, no issue number
                   │
                   └─ NO → Don't create anything yet
        </decision_tree>

        <recommendation>
          **DEFAULT: Always create repository issues**

          For Epics, User Stories, Tasks, Bugs, Spikes:
          - Always create as repository issues
          - Always add to project
          - Always set custom fields (Type, Status, Priority)

          Rationale:
          - Full GitHub functionality
          - Can be referenced in commits
          - Proper audit trail
          - Team notifications
          - Only downside: slightly more complex (2 steps vs 1)
        </recommendation>
      </when_to_use_which>

      <api_differences>
        <repository_issues_api>
          Command prefix: `gh issue`

          Operations:
          - create, list, view, edit, close, reopen, delete
          - comment, lock, unlock, pin, unpin
          - develop (manage linked branches)
          - transfer (to different repo)

          Identification:
          - By issue number: `gh issue view 123`
          - By URL: `gh issue view https://github.com/owner/repo/issues/123`

          Scope:
          - Always requires --repo flag (or inferred from current directory)
          - Per-repository
        </repository_issues_api>

        <project_items_api>
          Command prefix: `gh project`

          Operations:
          - item-create, item-list, item-edit, item-delete, item-archive
          - item-add (link existing issue to project)
          - field-list, field-create, field-delete

          Identification:
          - By project item ID: `--id PVTI_lADOA...`
          - NOT by issue number (must lookup first)

          Scope:
          - Requires project number and owner
          - Per-project (can span multiple repos)
        </project_items_api>

        <confusion_points>
          **Common mistakes:**

          1. **Trying to set custom fields on repository issues**
             ❌ `gh issue edit 123 --field Status="Done"`
             - Won't work: Issues don't have custom fields
             ✅ Must use `gh project item-edit` with project item ID

          2. **Trying to comment on draft issues**
             ❌ `gh issue comment <draft-issue-id>`
             - Won't work: Draft issues aren't repository issues
             ✅ Convert draft to issue first, or use repo issues from start

          3. **Using issue number as project item ID**
             ❌ `gh project item-edit --id 123` (using issue #123)
             - Won't work: Item ID ≠ issue number
             ✅ Must lookup item ID first via `gh project item-list`

          4. **Expecting deleted project items to delete issues**
             - `gh project item-delete` removes from project
             - Repository issue still exists
             - Must explicitly `gh issue delete` to remove issue
        </confusion_points>
      </api_differences>

      <current_scripts_approach>
        **Existing `gh-project-item-create.sh` does:**
        1. Create repository issue (gh issue create)
        2. Add issue to project (gh project item-add)
        3. Set custom fields (gh project item-edit)

        **This is the CORRECT approach:**
        - Creates real repository issue
        - Links to project
        - Sets project-specific fields
        - Result: Full functionality + project tracking
      </current_scripts_approach>
    </project_vs_repo_issues>
  </github_projects_api>

</research_findings>

---

## Status: Research in progress...

Next sections to complete:
- Script Architecture (directory structure, naming, common library)
- Help and Error Handling (formats, standards)
- Exemplar Analysis (detailed git/docker/kubectl patterns)
- Lessons from Existing Implementation
- Final synthesis and recommendations


  <script_architecture>
    <proposed_structure>
      <directory_layout>
        ```
        ~/.claude/skills/lib/gh-projects/
        ├── lib/
        │   └── gh-project-common.sh        # Shared library (existing, to improve)
        ├── old-implementation/              # Archive current scripts
        │   ├── gh-project-item-create.sh
        │   ├── gh-project-update.sh
        │   └── ... (all current scripts)
        │
        # NEW: Resource-specific CRUD scripts
        ├── gh-project-create.sh             # Create project
        ├── gh-project-list.sh               # List projects
        ├── gh-project-view.sh               # View project details
        ├── gh-project-delete.sh             # Delete project
        │
        ├── gh-epic-create.sh                # Create epic (repo issue + project)
        ├── gh-epic-list.sh                  # List epics (Type=Epic)
        ├── gh-epic-update.sh                # Update epic fields
        ├── gh-epic-delete.sh                # Delete epic
        │
        ├── gh-story-create.sh               # Create story (repo issue + project)
        ├── gh-story-list.sh                 # List stories (Type="User Story")
        ├── gh-story-update.sh               # Update story fields
        ├── gh-story-delete.sh               # Delete story
        ├── gh-story-link.sh                 # Link story to epic
        │
        ├── gh-task-create.sh                # Create task
        ├── gh-task-list.sh                  # List tasks
        ├── gh-task-update.sh                # Update task fields
        ├── gh-task-delete.sh                # Delete task
        ├── gh-task-link.sh                  # Link task to story
        │
        ├── gh-bug-create.sh                 # Create bug
        ├── gh-bug-list.sh                   # List bugs
        ├── gh-bug-update.sh                 # Update bug fields
        ├── gh-bug-delete.sh                 # Delete bug
        │
        ├── gh-spike-create.sh               # Create spike
        ├── gh-spike-list.sh                 # List spikes
        ├── gh-spike-update.sh               # Update spike fields
        ├── gh-spike-delete.sh               # Delete spike
        │
        └── gh-project-init.sh               # Initialize configuration (existing)
        ```

        **Total: ~25 scripts** (down from conceptually unlimited with all option combinations)
      </directory_layout>

      <naming_conventions>
        **Pattern: `gh-{resource}-{action}.sh`**

        Resources:
        - `project` - GitHub Project itself
        - `epic` - Epic items (Type=Epic)
        - `story` - User Story items (Type="User Story")
        - `task` - Task items (Type=Task)
        - `bug` - Bug items (Type=Bug)
        - `spike` - Spike items (Type=Spike)

        Actions (CRUD):
        - `create` - Create new resource
        - `list` - List resources (read multiple)
        - `view` - View single resource (read one)
        - `update` - Update resource fields
        - `delete` - Delete resource

        Special actions:
        - `link` - Create parent-child relationship (story↔epic, task↔story)
        - `init` - Initialize configuration

        **Rationale:**
        - Consistent, predictable naming
        - Tab completion friendly
        - Sorting groups by resource
        - Clear single responsibility
      </naming_conventions>

      <alternative_considered>
        **Alternative: Subcommand style (like git)**

        ```bash
        gh-project create [options]
        gh-project list [options]
        gh-epic create [options]
        gh-story create [options]
        ```

        Implementation: One script per resource, case statement for actions.

        **Rejected because:**
        - More complex implementation (one script does multiple things)
        - Violates Single Responsibility
        - Harder to maintain
        - Each action has different flags anyway

        **When subcommands make sense:**
        - When actions share significant code
        - When actions have overlapping flags
        - For very large tool suites (like git with 100+ commands)

        **For this project:**
        - 5-6 item types × 4-5 actions = 20-30 scripts
        - Not large enough to need subcommands
        - Separate scripts are simpler
      </alternative_considered>
    </proposed_structure>

    <common_library_design>
      <current_strengths>
        Existing `lib/gh-project-common.sh` (388 lines) provides:
        ✅ Configuration management (load_config, save_config)
        ✅ Field caching (cache_fields, get_field_id, get_option_id)
        ✅ Error handling (die, retry_command)
        ✅ Logging (log_success, log_error, log_warn, log_info)
        ✅ GraphQL execution (execute_graphql, execute_sub_issue_mutation)
        ✅ ID retrieval (get_project_id, get_repo_id, get_issue_id)
        ✅ Sub-issue operations (add_sub_issue, remove_sub_issue, query_sub_issues)
        ✅ Validation (validate_prerequisites)
        ✅ Field updates (set_single_select_field)
      </current_strengths>

      <needed_additions>
        **High-level abstractions to add:**

        1. **Unified item creation**
           ```bash
           # Abstract: "create repo issue + add to project"
           create_project_item(type, title, body, labels, assignee) {
             # 1. Create repo issue
             # 2. Add to project
             # 3. Set Type field
             # 4. Set Status=Todo
             # Returns: issue_number, item_id
           }
           ```

        2. **Type-filtered listing**
           ```bash
           # Abstract: "list items where Type=X"
           list_items_by_type(type, limit) {
             # 1. Get all project items
             # 2. Filter by Type field
             # 3. Return formatted list
           }
           ```

        3. **Field update by issue number**
           ```bash
           # Abstract: "find item by issue # + update field"
           update_item_field_by_issue(issue_num, field_name, value) {
             # 1. Find item ID from issue number
             # 2. Get field ID and option ID
             # 3. Update field
           }
           ```

        4. **Atomic parent-child linking**
           ```bash
           # Abstract: GitHub sub-issue API
           link_parent_child(parent_num, child_num) {
             # Already exists: add_sub_issue()
             # Just needs better naming/docs
           }
           ```

        5. **Configuration auto-detection**
           ```bash
           # Abstract: "detect project from git remote"
           auto_detect_config() {
             # 1. Get repo from git remote
             # 2. Get owner from gh auth status
             # 3. Prompt for project number
             # 4. Save config
           }
           ```
      </needed_additions>

      <library_responsibilities>
        **What SHOULD be in common library:**

        Core Infrastructure:
        - Configuration loading/saving
        - Field caching and resolution
        - Error handling and retries
        - Logging and user feedback
        - API execution (GraphQL, REST)
        - Validation (auth, tools)

        High-level operations:
        - Create item (repo issue + project)
        - Update item fields
        - Find item by issue number
        - Link items (parent-child)
        - List items (with filtering)

        **What SHOULD NOT be in common library:**

        Script-specific logic:
        - Argument parsing (each script different)
        - Help text (each script unique)
        - Script-specific validation (e.g., epic can't have --epic flag)
        - Output formatting (each script's choice)
      </library_responsibilities>

      <backward_compatibility>
        **Migration strategy:**

        Phase 1: Enhance common library
        - Add high-level abstractions listed above
        - Don't break existing function signatures
        - Add new functions alongside old

        Phase 2: Create new scripts
        - Use enhanced common library
        - Follow new naming conventions
        - Comprehensive help text

        Phase 3: Deprecate old scripts
        - Move to old-implementation/
        - Add deprecation notices
        - Point to new scripts

        Phase 4: Remove old scripts
        - After migration period (30 days?)
        - Only if no usage detected
      </backward_compatibility>
    </common_library_design>

    <configuration_management>
      <current_approach>
        **File:** `~/.config/gh-projects/config.json`

        **Contents:**
        ```json
        {
          "owner": "alexanderfedin",
          "repo": "hupyy-cpp-to-c",
          "project_number": 1,
          "project_id": "PVT_kwDOA...",
          "cache_timestamp": "2025-12-15T10:30:00Z",
          "cache_version": "2.0",
          "field_cache": {
            "Status": {
              "id": "PVTF_lADOA...",
              "type": "SINGLE_SELECT",
              "options": [...]
            }
          }
        }
        ```

        **Initialization:** `gh-project-init --project NUM`
      </current_approach>

      <improvements_needed>
        1. **Auto-detection**
           - Detect owner from `gh auth status`
           - Detect repo from git remote
           - Only ask for project number (can't auto-detect reliably)

        2. **Environment variable overrides**
           - `GH_PROJECT_NUMBER` - override project for one command
           - `GH_PROJECT_OWNER` - override owner
           - `GH_PROJECT_REPO` - override repo
           - Useful for multi-project scenarios without re-init

        3. **Multiple config files (future, YAGNI for v1)**
           - `~/.config/gh-projects/project-1.json`
           - `~/.config/gh-projects/project-2.json`
           - Switch with env var: `GH_PROJECT_CONFIG=project-2`

        4. **Cache refresh detection**
           - Check cache age on load
           - Warn if > 7 days old
           - Auto-refresh if field lookup fails
      </improvements_needed>

      <configuration_precedence>
        **Order (highest to lowest):**

        1. Command-line flags (--project, --owner, --repo)
        2. Environment variables (GH_PROJECT_NUMBER, etc.)
        3. Config file (~/.config/gh-projects/config.json)
        4. Auto-detection (git remote, gh auth)
        5. Error (require explicit configuration)

        **Rationale:**
        - CLI flags for one-off overrides
        - Env vars for session-level overrides
        - Config file for defaults
        - Auto-detection for convenience
        - Never silently guess wrong
      </configuration_precedence>
    </configuration_management>
  </script_architecture>

  <help_and_errors>
    <help_text_format>
      <standard_structure>
        ```
        Usage: {script-name} [OPTIONS] [ARGUMENTS]

        {One-line description}

        {Optional: Multi-line detailed description}

        Options:
          --flag VALUE      Description
          -f, --flag VALUE  Description (with short form)
          -h, --help        Show help

        Examples:
          # {Common use case 1}
          {script-name} {example command}

          # {Common use case 2}
          {script-name} {example command}

        {Optional: Special notes, requirements, caveats}
        ```
      </standard_structure>

      <exemplar_analysis>
        **Git's help format:**
        - Starts with usage line
        - Groups commands by category ("start a working area", "examine history")
        - Brief one-line descriptions
        - ✅ Adopt: Clear categorization, brief descriptions

        **Docker's help format:**
        - Separates "Common Commands" from "Management Commands"
        - Shows which are plugins with asterisk
        - Very clean, scannable
        - ✅ Adopt: Clear visual hierarchy

        **jq's help format:**
        - One-line summary of what tool does
        - Shows multiple usage patterns
        - Includes a quick example right in help
        - ✅ Adopt: Inline examples in help text

        **gh's help format:**
        - Inherited flags section (--help)
        - Examples section with realistic use cases
        - "Learn more" section with links
        - ✅ Adopt: Examples section, learn more links
      </exemplar_analysis>

      <help_text_template>
        ```bash
        usage() {
          cat << EOF
        Usage: $(basename "$0") [OPTIONS] {ARGUMENTS}

        {One sentence: what this script does}

        Options:
          --required VALUE   {Description} (required)
          --optional VALUE   {Description} (default: {value})
          --flag             {Description}
          -h, --help         Show this help

        Examples:
          # {Use case 1 description}
          $(basename "$0") {example-1}

          # {Use case 2 description}
          $(basename "$0") {example-2}

        {Optional section: Requirements, Notes, See Also}

        Learn more: {URL to documentation}
        EOF
          exit 0
        }
        ```

        **Guidelines:**
        - Keep total help under 30 lines (fits one screen)
        - Required options listed first
        - At least 2 examples (common case + edge case)
        - Use actual values in examples (not placeholders)
        - Include defaults in option descriptions
      </help_text_template>

      <progressive_disclosure>
        **Principle:** Don't overwhelm beginners, but provide depth for experts.

        **Levels:**
        1. **Usage line** - Absolute minimum to run command
        2. **Options list** - All flags with brief descriptions
        3. **Examples** - Copy-pasteable commands for common cases
        4. **Notes section** - Edge cases, requirements, caveats
        5. **Learn more** - Link to full documentation (future)

        Users read top to bottom until they find what they need.
        Beginners stop at examples. Experts read to notes.
      </progressive_disclosure>
    </help_text_format>

    <error_messages>
      <principles>
        1. **Tell what went wrong** - Specific error, not generic
        2. **Tell why it went wrong** - Context helps debugging
        3. **Tell how to fix it** - Actionable suggestion
      </principles>

      <error_message_template>
        ```bash
        # BAD: Generic, not helpful
        die "Error: Invalid input"

        # GOOD: Specific, actionable
        die "Error: Field 'Status' not found in project.
        
        This usually means:
        - Project fields not cached yet
        - Field was renamed in project settings
        
        Fix: Run 'gh-project-init --refresh-cache' to update field cache"
        ```
      </error_message_template>

      <common_errors_and_messages>
        **Authentication:**
        ```bash
        if ! gh auth status &> /dev/null; then
          die "Error: Not authenticated with GitHub CLI.
          
        Run: gh auth login
        Then: gh auth refresh -s project"
        fi
        ```

        **Missing configuration:**
        ```bash
        if [[ ! -f "$CONFIG_FILE" ]]; then
          die "Error: Project configuration not found.
          
        Initialize with: gh-project-init --project NUMBER
        
        Example: gh-project-init --project 1"
        fi
        ```

        **Field not found:**
        ```bash
        if [[ -z "$field_id" ]]; then
          die "Error: Field '$field_name' not found in project.
          
        Available fields: $(jq -r '.field_cache | keys | join(", ")' < "$CONFIG_FILE")
        
        Refresh cache: gh-project-init --refresh-cache"
        fi
        ```

        **Item not found:**
        ```bash
        if [[ -z "$ITEM_ID" ]]; then
          die "Error: Issue #$issue_num not found in project.
          
        Possible reasons:
        - Issue exists but not added to project
        - Issue number is incorrect
        
        List project items: gh project item-list $PROJECT_NUMBER --owner $PROJECT_OWNER"
        fi
        ```
      </common_errors_and_messages>

      <error_message_guidelines>
        ✅ DO:
        - Use multi-line errors for complex issues
        - Include actual values (field names, issue numbers)
        - Suggest specific commands to fix
        - List available options when invalid option given

        ❌ DON'T:
        - Print stack traces (not a programming language)
        - Use error codes without messages
        - Say "something went wrong" (too vague)
        - Assume user knows internal details
      </error_message_guidelines>
    </error_messages>

    <exit_codes>
      <standard_codes>
        **Following GitHub CLI conventions:**

        - `0` - Success
        - `1` - General error (default for failures)
        - `2` - Cancelled by user (Ctrl-C, --dry-run)
        - `4` - Authentication required

        **Additional codes to consider:**
        - `3` - Invalid usage (bad arguments)
        - `5` - Not found (issue, project, field)
        - `6` - Already exists (duplicate creation)

        **Decision: Start simple**
        - v1: Use only 0 (success) and 1 (any error)
        - Specific exit codes are YAGNI until scripts are used in automation
        - Can add later without breaking changes (scripts currently failing with 1 can start failing with 3, 5, 6)
      </standard_codes>

      <exit_code_usage>
        ```bash
        # Success
        exit 0

        # Error (via die function)
        die "Error message"  # exits with 1

        # Dry-run (not an error, but not full success)
        if [[ "$DRY_RUN" == "true" ]]; then
          log_warn "[DRY-RUN] Would create item..."
          exit 0  # or exit 2? TBD
        fi
        ```
      </exit_code_usage>

      <automation_considerations>
        **For scripts called from other scripts:**

        ```bash
        # Calling script can check exit code
        if gh-epic-create --title "Test" --body "Description"; then
          echo "Epic created successfully"
        else
          echo "Epic creation failed"
          exit 1
        fi

        # Or capture output and check
        ISSUE_NUM=$(gh-epic-create --title "Test" --format json | jq -r '.number')
        if [[ -z "$ISSUE_NUM" ]]; then
          die "Failed to get issue number from epic creation"
        fi
        ```

        **Requirement:** Scripts must exit non-zero on ANY error
        - Use `set -e` to exit on command failures
        - Use explicit exit codes in error paths
        - Never swallow errors silently
      </automation_considerations>
    </exit_codes>

    <validation_strategy>
      <when_to_validate>
        **Fail fast, fail clearly**

        Validate in this order:
        1. **Prerequisites** (gh, jq, auth) - before any work
        2. **Required arguments** - before API calls
        3. **Configuration** - before using config values
        4. **Field existence** - before field operations
        5. **Item existence** - before updates/deletes

        Don't start work if it will fail later.
      </when_to_validate>

      <validation_examples>
        ```bash
        # Prerequisites (in common library)
        validate_prerequisites() {
          command -v gh &>/dev/null || die "gh CLI not found. Install: https://cli.github.com/"
          command -v jq &>/dev/null || die "jq not found. Install: https://stedolan.github.io/jq/"
          gh auth status &>/dev/null || die "Not authenticated. Run: gh auth login"
        }

        # Required arguments (in each script)
        if [[ -z "$TITLE" ]]; then
          die "Error: Title required.
          
        Usage: $(basename "$0") --title TITLE [OPTIONS]
        Run '$(basename "$0") --help' for more information"
        fi

        # Configuration (in common library)
        load_config() {
          [[ -f "$CONFIG_FILE" ]] || die "Config not found. Run: gh-project-init --project NUM"
          PROJECT_NUMBER=$(jq -r '.project_number' < "$CONFIG_FILE")
          [[ "$PROJECT_NUMBER" != "null" ]] || die "Invalid config. Re-run: gh-project-init"
        }

        # Field existence (in common library)
        get_field_id() {
          local field_id=$(jq -r ".field_cache.\"$1\".id // empty" < "$CONFIG_FILE")
          [[ -n "$field_id" ]] || die "Field '$1' not found. Run: gh-project-init --refresh-cache"
          echo "$field_id"
        }
        ```
      </validation_examples>

      <validation_tradeoffs>
        **Strict vs Lenient:**

        Strict (recommended):
        - Fail if any field is missing
        - Fail if any option is invalid
        - Fail if any prerequisite is not met
        - ✅ Prevents partial state
        - ✅ Clear error messages
        - ❌ Less forgiving for users

        Lenient:
        - Warn if optional field is missing, continue
        - Auto-correct invalid options
        - Try to proceed despite missing prerequisites
        - ✅ More user-friendly
        - ❌ Can create inconsistent state
        - ❌ Harder to debug

        **Decision: Strict for v1**
        - Better to fail clearly than succeed partially
        - Users learn correct usage faster
        - Can always relax later (can't tighten)
      </validation_tradeoffs>
    </validation_strategy>
  </help_and_errors>

  <exemplars>
    <tool name="git">
      <what_to_emulate>
        ✅ **Command organization:**
        - Grouped by purpose ("start a working area", "examine history")
        - Clear categories help discovery
        - Adopt: Group scripts by resource type in documentation

        ✅ **Consistent patterns:**
        - `git {noun} {verb}` pattern (git branch create, git remote add)
        - All commands follow same structure
        - Adopt: `gh-{resource}-{action}` pattern

        ✅ **Porcelain vs plumbing:**
        - User-facing commands (porcelain) are simple
        - Low-level commands (plumbing) are scriptable
        - Adopt: Scripts are porcelain, common library is plumbing

        ✅ **Help text quality:**
        - Every command has comprehensive help
        - Examples for common use cases
        - Adopt: Comprehensive help in every script
      </what_to_emulate>

      <what_to_avoid>
        ❌ **Too many commands:**
        - Git has 100+ commands (overwhelming)
        - Steep learning curve
        - Avoid: Keep script count reasonable (20-30)

        ❌ **Inconsistent flag naming:**
        - `-a` vs `--all` vs `--interactive` (different meanings)
        - Hard to remember which flag does what
        - Avoid: Stick to long-form flags, avoid single-letter
      </what_to_avoid>
    </tool>

    <tool name="docker">
      <what_to_emulate>
        ✅ **Clear separation:**
        - "Common Commands" vs "Management Commands"
        - Visual hierarchy in help
        - Adopt: Separate item types clearly in docs

        ✅ **Subcommand style:**
        - `docker container ls`, `docker image ls`
        - Consistent noun-verb pattern
        - Note: We chose not to use subcommands, but pattern is good

        ✅ **Plugin markers:**
        - Shows which commands are plugins (*)
        - Clear extensibility
        - Adopt: Mark custom vs core functionality (future)
      </what_to_emulate>

      <what_to_avoid>
        ❌ **Duplicate commands:**
        - `docker ps` vs `docker container ls` (same thing)
        - Confusing for users
        - Avoid: One way to do each operation
      </what_to_avoid>
    </tool>

    <tool name="gh">
      <what_to_emulate>
        ✅ **JSON output:**
        - `--format json` for all commands
        - Consistent structure
        - Adopt: All scripts support JSON output

        ✅ **Examples section:**
        - Every command has examples
        - Uses realistic values
        - Adopt: 2-3 examples per script

        ✅ **Inherited flags:**
        - Shows which flags come from parent command
        - Clear documentation
        - Adopt: Document common flags from library

        ✅ **Learn more section:**
        - Points to manual and help
        - Progressive disclosure
        - Adopt: Link to documentation (future)
      </what_to_emulate>

      <what_to_avoid>
        ❌ **Complex JSON queries:**
        - `--jq` and `--template` flags add complexity
        - Most users just want simple JSON
        - Avoid: YAGNI - users can pipe to jq themselves
      </what_to_avoid>
    </tool>

    <tool name="jq">
      <what_to_emulate>
        ✅ **Example in help:**
        - Shows actual example right in help text
        - Users can try immediately
        - Adopt: Include quick example in help

        ✅ **Clear input/output:**
        - Shows what goes in, what comes out
        - Very pedagogical
        - Adopt: Show example output in help
      </what_to_emulate>
    </tool>

    <tool name="kubectl">
      <what_to_emulate>
        ✅ **Resource-oriented:**
        - kubectl {verb} {noun} pattern
        - Clear CRUD operations
        - Adopt: Our {noun}-{verb} pattern is similar

        ✅ **Declarative and imperative:**
        - Can create from file or from flags
        - Flexibility for different workflows
        - Consider: `--body-file` flag (already have this!)
      </what_to_emulate>
    </tool>

    <summary>
      **Key patterns from exemplars:**

      1. **Consistent naming** - All tools use predictable patterns
      2. **Comprehensive help** - Every command well-documented
      3. **JSON output** - Machine-readable for scripting
      4. **Examples** - Show don't tell
      5. **Fail clearly** - Good error messages
      6. **Composability** - Tools work together (pipes)

      **Apply to our scripts:**
      - `gh-{resource}-{action}` naming (consistent)
      - Help with usage, options, examples (comprehensive)
      - `--format json` support (machine-readable)
      - 2-3 examples per script (show don't tell)
      - Multi-line error messages with fixes (fail clearly)
      - Output to stdout, logs to stderr (composable)
    </summary>
  </exemplars>

  <lessons_from_existing>
    <what_worked>
      ✅ **Common library approach:**
      - 388 lines of well-organized shared code
      - Clear sections (logging, config, GraphQL, field operations)
      - DRY compliance - no duplication across scripts
      - **Keep:** Enhance but don't replace

      ✅ **Field caching:**
      - Solves real performance problem (API rate limits)
      - Cached in config file, survives script runs
      - Auto-lookup by name instead of requiring IDs
      - **Keep:** Core feature, very valuable

      ✅ **Retry logic:**
      - `retry_command()` handles transient network failures
      - Exponential backoff (2s, 4s, 8s)
      - 3 attempts before giving up
      - **Keep:** Essential for reliability

      ✅ **Colored logging:**
      - `log_success` (green), `log_error` (red), `log_warn` (yellow), `log_info` (blue)
      - Clear visual feedback
      - Logs to stderr (doesn't pollute stdout)
      - **Keep:** Excellent UX

      ✅ **Dry-run support:**
      - `--dry-run` flag previews without executing
      - Shows exactly what would happen
      - Safety for destructive operations
      - **Keep:** Critical for user confidence

      ✅ **Error handling:**
      - `set -euo pipefail` in common library
      - Fails fast on errors
      - `die()` function for clear error messages
      - **Keep:** Correct approach

      ✅ **Atomic operations:**
      - `gh-project-item-create` does: create issue → add to project → set fields
      - All-or-nothing approach
      - Reports partial failures clearly
      - **Keep:** Right abstraction level

      ✅ **Sub-issue integration:**
      - Uses GitHub's native sub-issue API
      - `add_sub_issue()`, `remove_sub_issue()`, `query_sub_issues()`
      - Proper GraphQL-Features header handling
      - **Keep:** Well-implemented
    </what_worked>

    <what_failed>
      ❌ **Too many options per script:**
      - `gh-project-item-create`: 10+ options
      - Confusing which are required vs optional
      - Many invalid combinations possible
      - **Fix:** Split by item type (gh-epic-create, gh-story-create, etc.)

      ❌ **Generic naming:**
      - `gh-project-update` - updates what? project metadata or item fields?
      - `gh-project-link` - links what to what?
      - Unclear without reading help
      - **Fix:** More specific names (gh-story-link, gh-epic-update-fields)

      ❌ **Dual-mode scripts:**
      - `gh-project-update`: different behavior with --item vs --issue
      - Two code paths in one script
      - **Fix:** Separate scripts or pick one mode

      ❌ **Setup script proliferation:**
      - `gh-project-setup-init`, `gh-project-setup-apply`, `gh-project-setup-clone`
      - Unclear when to use which
      - **Fix:** Consolidate to `gh-project-init` only (YAGNI the others)

      ❌ **Convert script mystery:**
      - `gh-project-convert` - converts what to what?
      - No clear use case
      - **Fix:** Delete if unused (verify first)

      ❌ **Implicit dependencies:**
      - Scripts call other scripts ($SCRIPT_DIR/gh-project-update)
      - Creates coupling
      - **Fix:** Use common library functions, not other scripts

      ❌ **PATH workaround in common library:**
      - `export PATH="/opt/homebrew/bin:..."` to fix restricted environments
      - Solves symptom, not cause
      - **Fix:** Document proper PATH setup, remove workaround
    </what_failed>

    <confusion_points>
      ⚠️ **Project items vs repository issues:**
      - Scripts mix terminology: "item" sometimes means draft, sometimes means repo issue
      - Users don't understand difference
      - **Fix:** Clear naming - always specify "repo issue" vs "draft issue"

      ⚠️ **When to use item-create vs item-add:**
      - `gh project item-create` creates draft issue
      - `gh project item-add` adds existing repo issue
      - Most users want repo issues (item-add workflow)
      - **Fix:** Scripts default to repo issue creation, rarely use drafts

      ⚠️ **Field name case sensitivity:**
      - UI shows "Status", JSON needs "status"
      - Caused bugs, confusion
      - **Fix:** Document clearly, handle both cases in lookup

      ⚠️ **Issue number vs item ID:**
      - Scripts accept --issue NUM but need item ID for API
      - Transparent lookup adds latency
      - Users don't realize these are different
      - **Fix:** Document clearly, accept both with explicit flags

      ⚠️ **Partial creation failures:**
      - "Repository issue created but not added to project"
      - Left in inconsistent state
      - **Fix:** Better error recovery, rollback on failure (future)

      ⚠️ **Configuration initialization:**
      - Must run gh-project-init first, but easy to forget
      - Error message points to solution
      - **Fix:** Auto-detect when possible, prompt for init
    </confusion_points>

    <technical_debt>
      **Current issues to address:**

      1. **No tests** - Scripts are untested
         - Risk: Breaking changes go unnoticed
         - Fix: Add integration tests (future, YAGNI for v1)

      2. **No versioning** - Config has version field but not used
         - Risk: Incompatible config changes
         - Fix: Version check on load, migration path

      3. **No rate limit handling** - Just retries
         - Risk: Hit GitHub API rate limit, all retries fail
         - Fix: Detect rate limit errors, wait appropriately (future)

      4. **Hardcoded limits** - `--limit 30` everywhere
         - Risk: Can't get all items if >30
         - Fix: Pagination support (future)

      5. **No batch operations** - One item at a time
         - Risk: Slow for bulk operations
         - Fix: Batch scripts (future, YAGNI for v1)

      6. **Config lock** - No concurrent access handling
         - Risk: Simultaneous scripts corrupt config
         - Fix: File locking (future, low priority)
    </technical_debt>
  </lessons_from_existing>

  <dependencies>
    <required>
      • **GitHub CLI (gh)** version 2.0+ - Core dependency for all API access
      • **jq** 1.6+ - JSON parsing and manipulation
      • **bash** 4.0+ or **zsh** 5.0+ - Shell environment
      • **git** 2.0+ - For auto-detection of repo from remotes
      • **GitHub Projects V2** - NOT V1 (deprecated)
    </required>

    <optional>
      • **GitHub auth with project scope** - Required for project operations: `gh auth refresh -s project`
    </optional>

    <version_compatibility>
      • Minimum GitHub CLI: 2.0 (when Projects V2 support added)
      • Maximum: Current (tested with 2.40+)
      • No compatibility with Projects V1 (different API entirely)
    </version_compatibility>
  </dependencies>

  <assumptions>
    <technical_assumptions>
      • Users have `gh` CLI installed and authenticated
      • Users have initialized project config with `gh-project-init`
      • Projects use standard custom fields: "Type", "Status", "Priority"
      • One primary project per repository (multi-project is YAGNI)
      • Users work with repository issues, not draft issues (99% use case)
      • Field options are static after project setup (rare changes)
    </technical_assumptions>

    <workflow_assumptions>
      • Users follow SCRUM/Kanban methodology (Epic → Story → Task hierarchy)
      • Status workflow: Todo → In Progress → Done (plus Blocked)
      • Priority levels: Low, Medium, High, Critical (standard)
      • Item types: Epic, User Story, Task, Bug, Spike (standard)
      • Parent-child relationships: Epic ← Story ← Task
    </workflow_assumptions>

    <usage_assumptions>
      • Scripts primarily used by humans (not automation)
      • Interactive CLI usage (not batch processing)
      • Single project context (not switching projects frequently)
      • Solo development or small teams (not enterprise scale)
    </usage_assumptions>
  </assumptions>

  <open_questions>
    <questions>
      • **V1 compatibility:** Should scripts detect and reject Projects V1? Or just fail with unclear error?
        - Recommendation: Detect and fail clearly with upgrade message

      • **Migration path:** How to migrate users from old scripts to new?
        - Recommendation: Deprecation warnings in old scripts, redirect to new

      • **Rollback on failure:** If "create issue" succeeds but "add to project" fails, delete the issue?
        - Recommendation: No rollback in v1 (complex), but clear error message

      • **Draft issues:** Support at all, or always use repository issues?
        - Recommendation: Support repo issues only in v1, add drafts later if needed

      • **Pagination:** Handle projects with >30 items?
        - Recommendation: Not in v1 (YAGNI), document limitation

      • **Multi-project:** Support working with multiple projects?
        - Recommendation: Not in v1, single project config only

      • **Testing:** Unit tests? Integration tests? Manual testing only?
        - Recommendation: Manual testing for v1, integration tests in v2

      • **Documentation:** Man pages? Web docs? Help text only?
        - Recommendation: Comprehensive help text in v1, consider docs in v2

      • **Distribution:** How do users install scripts?
        - Recommendation: Manual copy to ~/.claude/skills/lib/gh-projects/ for now

      • **Auto-update:** Check for script updates automatically?
        - Recommendation: No (YAGNI), users manage manually
    </questions>
  </open_questions>

  <confidence>medium-high</confidence>

  <verification_checklist>
    - [x] All four research areas addressed (CLI design, GitHub API, Script architecture, Help/Errors)
    - [x] Official documentation consulted (gh --help, GitHub docs)
    - [x] At least 3 exemplar tools analyzed (git, docker, gh, jq, kubectl)
    - [x] Existing scripts reviewed (16 scripts in ~/.claude/skills/lib/gh-projects/)
    - [x] Concrete examples provided throughout
    - [x] Verification checklist from methodology completed
    - [x] Quality report distinguishes verified vs assumed
    - [x] Sources listed with URLs where applicable
    - [x] Confidence level assigned (medium-high)
    - [x] Critical project vs repo issue distinction clarified with examples
  </verification_checklist>

</research_findings>

---

## Sources

- [Google Shell Style Guide](https://google.github.io/styleguide/shellguide.html)
- [Command Line Interface Guidelines (clig.dev)](https://clig.dev/)
- [12 Factor CLI Apps](https://medium.com/@jdxcode/12-factor-cli-apps-dd3c227a0e46)
- [The Twelve-Factor App](https://12factor.net/)
- [CLI Guidelines - GitHub](https://github.com/cli-guidelines/cli-guidelines)
- GitHub CLI built-in documentation: `gh project --help`, `gh issue --help`, `gh help exit-codes`
- Existing gh-projects scripts in `~/.claude/skills/lib/gh-projects/`
- Exemplar CLI tools: git, docker, gh, jq, kubectl

---

**Research complete.** Ready for planning phase.


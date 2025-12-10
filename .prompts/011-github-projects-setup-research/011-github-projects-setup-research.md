# GitHub Projects v2 Setup Research - Exhaustive Investigation

## Objective

Research **how to programmatically create, configure, and clone GitHub Projects v2** with complete field structure, views, and automation from an existing template project.

**Goal**: Comprehensive understanding enabling shell scripts to:
1. **[Optional]** Create new projects (user or organization scope)
2. **[Mandatory]** Copy complete field structure from template project (#14)
3. **[Mandatory]** Set up all necessary views (Kanban, Table, Roadmap, etc.)
4. **[Mandatory]** Configure view settings, filters, groupings, layouts

**Why This Matters**: Enable team members to quickly spin up new projects with consistent structure, eliminating manual UI configuration and ensuring standardization across projects.

## Context

**Existing Research**:
- Base project management research: `@.prompts/001-github-projects-management-research/github-projects-management-research.md`
- Corrected sub-issue API: `@.prompts/003-github-projects-research-refine/github-projects-research-refined.md`
- Implementation plan: `@.prompts/004-github-projects-scripts-plan-updated/github-projects-scripts-plan.md`

**Existing Scripts**:
- Location: `!ls -la scripts/gh-projects/`
- Config cache: `~/.config/gh-projects/config.json`

**Template Project**:
- Project #14 for owner `o2alexanderfedin` and repo `cpp-to-c-transpiler`
- Current field structure: `!gh project field-list 14 --owner o2alexanderfedin --format json`
- Current views: `!gh project view-list 14 --owner o2alexanderfedin --format json` (if available)

**Target Capabilities**:
1. Create new project (optional feature)
2. Clone/template existing project structure
3. Configure fields (custom fields with options)
4. Set up views (Kanban, Table, Roadmap, etc.)
5. Configure view properties (grouping, sorting, filtering, layout)

## Requirements

### Research Scope: EXHAUSTIVE

**Requirement 1: Project Creation (Optional Feature)**

Investigate all methods to create new GitHub Projects v2:

**CLI Investigation**:
- `gh project create` command capabilities
- User vs organization scope
- Public vs private projects
- Project metadata (title, description, readme)
- Default fields included in new projects
- Template support (if any)

**GraphQL API Investigation**:
- `createProjectV2` mutation
- Required vs optional fields
- Owner specification (user vs organization)
- Return values (project ID, number, URL)
- Permissions required
- Rate limiting considerations

**Testing Requirements**:
- Test project creation in user scope
- Test project creation in organization scope (if accessible)
- Document all parameters and their effects
- Capture created project metadata structure

**Deliverable**: Complete documentation of project creation methods with working examples.

---

**Requirement 2: Field Structure Templating (Mandatory)**

Research how to **query existing fields** and **replicate field structure** on another project.

**Field Querying**:
- CLI: `gh project field-list` capabilities and limitations
- GraphQL: Query all fields with full metadata
  - Field IDs, names, types, data types
  - Single-select options (IDs, names, descriptions, colors)
  - Number field settings (min, max, precision)
  - Date field settings
  - Iteration field settings (if applicable)
- Field ordering/positioning
- System fields vs custom fields distinction

**Field Creation**:
- CLI: `gh project field-create` for each field type:
  - Single-select: `--data-type SINGLE_SELECT`
  - Text: `--data-type TEXT`
  - Number: `--data-type NUMBER`
  - Date: `--data-type DATE`
  - Iteration: `--data-type ITERATION`
- GraphQL: Field creation mutations
  - `updateProjectV2` or specific field mutations
  - Setting field options for single-select
  - Setting field constraints
  - Field positioning/ordering
- Limitations: Maximum number of fields per project (verify)
- Option creation: Adding options to single-select fields

**Field Structure Export/Import**:
- Export template project fields to JSON/YAML
- Import field structure to new project
- Handle field ID mapping (template → new project)
- Preserve field types, options, and configurations

**Testing Requirements**:
- Query all fields from project #14
- Create test project with same field structure
- Verify field types, options match exactly
- Test all field types (single-select, text, number, date)

**Deliverable**: Field templating workflow with JSON export/import capability.

---

**Requirement 3: View Configuration (Mandatory - All View Types)**

Research **all view types** in GitHub Projects v2 and how to create/configure them programmatically.

**View Types to Research**:
1. **Table View** (default)
   - Column visibility and ordering
   - Column widths
   - Sorting configuration
   - Filtering rules
   - Grouping settings

2. **Board/Kanban View** (mandatory)
   - Column field (typically Status)
   - Column ordering (option order)
   - Card layout (compact vs full)
   - Filtering rules
   - Sorting within columns

3. **Roadmap View**
   - Date field selection (start/end dates)
   - Zoom level (days, weeks, months, quarters)
   - Markers and milestones
   - Filtering rules
   - Grouping by field

4. **Additional Views** (if exist)
   - Any other view types available
   - Their specific configurations

**View Management APIs**:

**CLI Investigation**:
- `gh project view-list` command (if available)
- `gh project view-create` command (if available)
- `gh project view-update` command (if available)
- Any subcommands for view management

**GraphQL Investigation**:
- Query views: ProjectV2 → views field
  - View IDs, names, layouts (TABLE, BOARD, ROADMAP)
  - View configurations (filters, sorting, grouping)
  - Field visibility per view
  - View-specific settings
- Create views: Mutations for view creation
  - `updateProjectV2` with view parameters
  - Specific view creation mutations (if any)
  - Setting view name, layout type
- Update views: Mutations for view configuration
  - Setting filters (field-based conditions)
  - Setting sorting (field + direction)
  - Setting grouping (field to group by)
  - Setting field visibility
  - Setting layout-specific options (columns, zoom, etc.)

**View Configuration Deep Dive**:

**Filters**:
- Filter syntax and operators
- Field-based filtering (Status = "Done", Priority > 3)
- Multiple conditions (AND/OR logic)
- Filter persistence and sharing

**Sorting**:
- Sort by field
- Sort direction (ASC/DESC)
- Multiple sort levels
- Default sorting for new views

**Grouping**:
- Group by single-select fields (Status, Type, Priority)
- Group ordering
- Collapsed vs expanded groups by default
- Kanban board column mapping

**Field Visibility**:
- Show/hide fields per view
- Field ordering within view
- Field width (if applicable)

**Layout-Specific Settings**:
- Board: Column field, card layout, swimlanes (if available)
- Roadmap: Date fields, zoom level, markers
- Table: Column widths, frozen columns (if available)

**Testing Requirements**:
- Query all views from project #14
- Document view configurations (filters, sorting, grouping)
- Create test project with same view structure
- Verify Kanban board with Status columns
- Test table view with custom sorting/filtering
- Test roadmap view (if date fields exist)

**Deliverable**: Complete view templating workflow with all view types and configurations.

---

**Requirement 4: Project Cloning/Templating Workflow**

Design **end-to-end workflow** for cloning a complete project structure.

**Cloning Strategies to Research**:

**Strategy A: Full Clone (GraphQL copyProjectV2)**:
- Check if `copyProjectV2` mutation exists
- What gets copied (fields, views, items, automation)
- What doesn't get copied
- Limitations and constraints
- Owner specification for clone

**Strategy B: Programmatic Replication**:
1. Query source project metadata
2. Create new project
3. Create fields matching source
4. Create views matching source
5. Configure view settings matching source
6. Optionally copy items (if requested)

**Strategy C: Template/Preset System**:
- Export project structure to JSON/YAML template
- Store template in repo or config
- Import template to create new project
- Parameterize project-specific values

**Template Format Design**:
```json
{
  "template_version": "1.0",
  "source_project": {
    "owner": "o2alexanderfedin",
    "number": 14,
    "title": "cpp-to-c-transpiler"
  },
  "fields": [
    {
      "name": "Status",
      "type": "ProjectV2SingleSelectField",
      "data_type": "SINGLE_SELECT",
      "options": [
        {"name": "Todo", "description": "", "color": "GRAY"},
        {"name": "In Progress", "description": "", "color": "YELLOW"},
        {"name": "Done", "description": "", "color": "GREEN"}
      ]
    }
  ],
  "views": [
    {
      "name": "Kanban",
      "layout": "BOARD",
      "group_by_field": "Status",
      "filters": [],
      "sorting": [{"field": "Priority", "direction": "DESC"}]
    }
  ]
}
```

**Item Cloning Considerations**:
- Should items be copied? (usually no, just structure)
- Draft items vs repository issues handling
- Custom field values migration
- Sub-issue relationships (if items copied)

**Testing Requirements**:
- Full clone workflow: Project #14 → Test Project
- Verify all fields present with same types/options
- Verify all views present with same configurations
- Test with both CLI and GraphQL approaches
- Measure performance (time to clone)

**Deliverable**: Recommended cloning strategy with complete implementation details.

---

**Requirement 5: Automation and Advanced Features**

Research **project automation** and **advanced configuration** capabilities.

**Automation Workflows**:
- Built-in workflows available
  - Auto-add items to project
  - Auto-set field values
  - Auto-archive completed items
- Custom workflow creation (if available)
- GitHub Actions integration with projects
- Webhook support for project events

**Advanced Field Types**:
- Iteration fields (sprints)
  - Iteration configuration
  - Duration, start dates
  - Multiple iterations
- Calculated fields (if available)
- Formula fields (if available)

**Project Settings**:
- Project visibility (public/private)
- Access control (if programmatic)
- README content
- Description
- Linked repositories
- Project templates (official feature if exists)

**Testing Requirements**:
- Query project #14 automation rules
- Test creating auto-add workflow
- Document all automation capabilities
- Test iteration field setup (if present)

**Deliverable**: Automation and advanced features documentation with working examples.

---

**Requirement 6: Permissions and Limitations**

Research **permission model** and **API limitations**.

**Permissions**:
- Project create permission (user vs org)
- Project admin permission requirements
- Field creation permission
- View creation permission
- Token scopes required (`project`, `repo`, etc.)
- Organization vs user project differences

**Limitations**:
- Maximum fields per project
- Maximum views per project
- Maximum options per single-select field
- Maximum items per project (if relevant)
- Rate limiting for project APIs
- GraphQL query complexity limits
- Concurrent modification handling

**Error Handling**:
- Common error scenarios and messages
- Retry strategies for transient failures
- Validation errors (invalid field types, etc.)
- Permission denied errors

**Testing Requirements**:
- Test with minimal token scopes
- Test organization project creation (if available)
- Document all errors encountered
- Test rate limiting behavior (if feasible)

**Deliverable**: Permissions guide and limitations reference.

---

**Requirement 7: Shell Script Implementation Design**

Design **new shell scripts** for project setup/templating.

**Proposed Scripts**:

1. **`gh-project-setup-init`**
   - Export template from existing project
   - Save to JSON file
   - Include fields, views, settings

2. **`gh-project-setup-create`**
   - Create new project from template
   - Apply field structure
   - Set up views
   - Configure settings

3. **`gh-project-setup-clone`**
   - Full clone of existing project
   - Handle all aspects automatically
   - Parameterize project name/owner

4. **Integration with existing scripts**
   - Extend `gh-project-init` with template export
   - Add `--from-template` flag to creation workflows
   - Update README with templating workflows

**Script Interface Design**:
```bash
# Export template
gh-project-setup-init --project 14 --export templates/standard-project.json

# Create from template
gh-project-setup-create \
  --template templates/standard-project.json \
  --title "New Feature Project" \
  --owner myorg

# Clone existing project
gh-project-setup-clone \
  --source-project 14 \
  --source-owner o2alexanderfedin \
  --title "Cloned Project"
```

**Deliverable**: Script design with interfaces, examples, implementation approach.

---

## Output Specification

Save research to: `.prompts/011-github-projects-setup-research/github-projects-setup-research.md`

**Structure**:
```xml
<research version="1.0" date="2025-12-09">

<executive_summary>
<!-- 2-3 paragraphs: What was discovered, key findings, recommended approach -->
</executive_summary>

<findings>

<project_creation>
<cli_capabilities>
  <!-- gh project create documentation -->
</cli_capabilities>
<graphql_api>
  <!-- createProjectV2 mutation details -->
</graphql_api>
<examples>
  <!-- Working examples with actual commands -->
</examples>
</project_creation>

<field_templating>
<querying_fields>
  <!-- How to query all field metadata -->
</querying_fields>
<creating_fields>
  <!-- How to create each field type -->
</creating_fields>
<field_options>
  <!-- How to add options to single-select fields -->
</field_options>
<template_format>
  <!-- JSON structure for field export/import -->
</template_format>
<examples>
  <!-- Working examples -->
</examples>
</field_templating>

<view_configuration>
<view_types>
  <table_view>
    <!-- Table view capabilities and configuration -->
  </table_view>
  <board_view>
    <!-- Kanban board configuration -->
  </board_view>
  <roadmap_view>
    <!-- Roadmap view configuration -->
  </roadmap_view>
  <!-- Additional view types if found -->
</view_types>

<view_management>
  <!-- How to create, update, delete views -->
</view_management>

<view_settings>
  <filters><!-- Filter syntax and operators --></filters>
  <sorting><!-- Sorting configuration --></sorting>
  <grouping><!-- Grouping configuration --></grouping>
  <visibility><!-- Field visibility per view --></visibility>
</view_settings>

<examples>
  <!-- Working examples for each view type -->
</examples>
</view_configuration>

<cloning_strategies>
<copyProjectV2>
  <!-- If mutation exists, document it fully -->
</copyProjectV2>
<programmatic_replication>
  <!-- Step-by-step clone workflow -->
</programmatic_replication>
<template_system>
  <!-- Template export/import approach -->
</template_system>
<recommendation>
  <!-- Which strategy to use and why -->
</recommendation>
</cloning_strategies>

<automation>
<!-- Built-in workflows, GitHub Actions, webhooks -->
</automation>

<advanced_features>
<!-- Iteration fields, calculated fields, formulas, etc. -->
</advanced_features>

<permissions_limitations>
<permissions><!-- Required permissions and token scopes --></permissions>
<limitations><!-- Maximum values, rate limits --></limitations>
<error_handling><!-- Common errors and recovery --></error_handling>
</permissions_limitations>

<script_design>
<proposed_scripts>
  <!-- gh-project-setup-init, gh-project-setup-create, gh-project-setup-clone -->
</proposed_scripts>
<interfaces>
  <!-- Command-line interfaces with all options -->
</interfaces>
<implementation_notes>
  <!-- Key implementation considerations -->
</implementation_notes>
</script_design>

</findings>

<verification>
<tests_performed>
  <!-- List all hands-on tests conducted -->
</tests_performed>
<working_examples>
  <!-- Actual commands that were tested and work -->
</working_examples>
<sources_consulted>
  <!-- Official docs, community discussions, working scripts -->
</sources_consulted>
</verification>

<metadata>
<confidence>
  <!-- HIGH/MEDIUM/LOW with breakdown by topic -->
  <!-- E.g., "HIGH for field templating (tested extensively), MEDIUM for view API (some undocumented features)" -->
</confidence>

<dependencies>
  <!-- What's needed to implement scripts: gh CLI version, token permissions, etc. -->
</dependencies>

<open_questions>
  <!-- Anything that remains uncertain or requires user decision -->
  <!-- E.g., "Should template system support custom field types beyond standard set?" -->
</open_questions>

<assumptions>
  <!-- What was assumed during research -->
  <!-- E.g., "Assumed user has project admin permissions on template project" -->
</assumptions>

<blockers>
  <!-- Any impediments to implementation -->
  <!-- E.g., "View creation API may not be available via CLI, requires GraphQL" -->
</blockers>

<next_steps>
  <!-- Concrete actions to take after research -->
  <!-- E.g., "Create implementation plan for gh-project-setup scripts" -->
</next_steps>
</metadata>

</research>
```

## Research Methodology

### Exhaustive Investigation Requirements

**Web Research (Mandatory)**:
- Official GitHub GraphQL API documentation
- GitHub Projects v2 feature announcements
- GitHub CLI documentation for project commands
- Community scripts and examples (joshjohanning, jessehouwing, etc.)
- GitHub Community discussions about project APIs
- Recent changelogs (2024-2025) for new features

**Hands-On Testing (Mandatory)**:
- Query project #14 complete structure
- Test field creation on test project
- Test view creation on test project
- Test full clone workflow
- Capture all GraphQL queries and mutations used
- Document all CLI commands tested
- Save screenshots/outputs of successful operations

**Tools Available**:
- `WebSearch` - Search for official documentation, community resources
- `WebFetch` - Fetch specific documentation pages, GitHub API docs
- `Playwright` - Browse GitHub UI to understand view configurations visually
- `Bash` - Execute `gh` CLI commands, test GraphQL queries
- `Read` - Read existing config files, template examples
- `Grep` - Search codebase for existing project management code

### Quality Requirements

**Verification Checklist**:
- [ ] All GraphQL mutations tested with actual API calls
- [ ] All CLI commands tested and output captured
- [ ] Field templating workflow tested end-to-end
- [ ] View creation tested for each view type
- [ ] Kanban board specifically tested and verified
- [ ] Template format designed and validated with real data
- [ ] Error cases tested (missing permissions, invalid parameters)
- [ ] Rate limiting behavior observed (if applicable)
- [ ] All sources documented with URLs
- [ ] Working examples provided for every major capability

**Quality Assurance**:
- Distinguish between VERIFIED (tested) and ASSUMED (inferred) information
- Provide official documentation URLs for all API claims
- Include actual command outputs for transparency
- Note any undocumented features discovered through experimentation
- Flag any deprecated or legacy features to avoid

**Pre-Submission Check**:
- All 7 requirements addressed comprehensively
- Executive summary provides clear recommended approach
- Metadata sections complete (confidence, dependencies, open questions, assumptions, blockers, next steps)
- SUMMARY.md created with substantive one-liner
- Ready for planning phase (no major unknowns remaining)

## SUMMARY.md Requirement

Create `.prompts/011-github-projects-setup-research/SUMMARY.md` with:

```markdown
# GitHub Projects v2 Setup Research Summary

**[Substantive one-liner describing the key finding and recommended approach]**

## Version
v1.0 - Initial exhaustive research

## Key Findings

• [Major finding about project creation]
• [Major finding about field templating]
• [Major finding about view configuration]
• [Major finding about cloning strategies]
• [Major finding about limitations/gotchas]

(5-7 bullet points, specific and actionable)

## Recommended Approach

[2-3 sentences describing the recommended implementation strategy]

## Verified vs Assumed

**Verified** (tested with actual API calls):
- [List what was hands-on tested]

**Assumed** (inferred from documentation):
- [List what was documented but not tested]

## Decisions Needed

• [Decision user must make before implementation]
• [Or: "None - ready to proceed with planning"]

## Blockers

• [External impediment blocking implementation]
• [Or: "None"]

## Next Step

[Concrete action - e.g., "Create implementation plan for gh-project-setup-* scripts"]
```

**One-Liner Requirements**:
- Must communicate the core capability discovered
- Examples:
  - ✅ "GraphQL projectV2 queries + field-create CLI enables full project templating; copyProjectV2 unavailable but manual replication tested"
  - ✅ "View creation requires GraphQL with layout-specific mutations; Kanban board uses groupByField(Status) configuration"
  - ❌ "Researched project setup capabilities"
  - ❌ "Completed GitHub Projects investigation"

## Success Criteria

Research is complete when:
1. ✅ Project creation thoroughly documented (CLI + GraphQL)
2. ✅ Field templating workflow designed and tested
3. ✅ All view types researched (Table, Board, Roadmap, others)
4. ✅ Kanban board configuration specifically validated
5. ✅ Cloning strategies evaluated with recommendation
6. ✅ Automation and advanced features documented
7. ✅ Permissions and limitations clearly stated
8. ✅ Shell script interfaces designed
9. ✅ All hands-on testing completed with captured outputs
10. ✅ SUMMARY.md created with substantive one-liner
11. ✅ Confidence levels assigned to all major findings
12. ✅ Sources documented with URLs for verification
13. ✅ Next step is clear (create implementation plan)

**Target Confidence**: HIGH (90%+) - All major capabilities tested hands-on, minor uncertainties documented in open_questions.

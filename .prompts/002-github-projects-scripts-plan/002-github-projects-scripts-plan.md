# GitHub Projects Management Scripts - Implementation Plan

## Objective

Create a detailed implementation plan for robust bash scripts that manage GitHub Projects v2 issues using the draft-first workflow discovered in research.

**Goal**: Production-ready shell scripts that:
1. Encapsulate all GitHub Projects operations (CRUD)
2. Implement draft-first workflow (create drafts by default, convert only when needed)
3. Handle custom fields (Status, Priority, Type, etc.) with caching
4. Prevent accidental conversions and confusion
5. Provide excellent UX (dry-run, color output, progress indicators)
6. Are maintainable and extensible

**Why This Matters**: Replace manual/confusing GitHub UI workflow with clean, scriptable CLI tools that enforce best practices and prevent duplicate-looking issues.

## Context

**Research Foundation**:
```
@.prompts/001-github-projects-management-research/github-projects-management-research.md
```

**Key Research Findings to Incorporate**:
1. **Dual-ID System**: Draft editing requires DI_* content ID from GraphQL, custom fields use PVTI_* with project-id
2. **One-Way Conversion**: Draft → repo issue is irreversible via `convertProjectV2DraftIssueItemToIssue` mutation
3. **Custom Fields**: Project-only metadata; requires field ID + option ID resolution with caching
4. **Sub-Issue Workaround**: Use custom "Parent Epic" text field (native API unavailable)
5. **Client-Side Filtering**: All query/filter operations require jq patterns
6. **Field Metadata**: Cache field IDs and option IDs to avoid repeated queries

**Target Use Cases** (from TO-DOS.md):
- Create draft epics and stories in GitHub Projects
- Set custom fields (Status, Priority, Type)
- Link stories to parent epics (via custom field)
- Query/list items by filters
- Update draft and repo issue content
- Convert drafts to repo issues only when needed (PR linking, sub-issues)
- Delete/archive items

**Constraints**:
- Bash scripts (not Python) for simplicity
- Use `gh` CLI + GraphQL where CLI insufficient
- Support macOS/Linux (portable bash)
- No external dependencies beyond gh, jq, curl
- Must handle errors gracefully with clear messages

## Requirements

### Planning Scope

**Phase 1: Script Architecture**
1. **File Organization**:
   - How many scripts? (monolithic vs modular)
   - Naming convention
   - Installation/setup process
   - Configuration file format (project ID, field mappings, etc.)

2. **Core Functions Library**:
   - Shared utility functions (error handling, logging, caching)
   - GraphQL helper functions
   - Field ID resolution and caching
   - JSON parsing helpers

3. **Configuration Management**:
   - Where to store project ID, owner, field mappings
   - Config file location (~/.config/gh-projects/ ?)
   - Auto-detection vs explicit configuration
   - Validation and error messages for misconfiguration

**Phase 2: Script Specifications**

For each script, define:
1. **Purpose**: What it does, when to use it
2. **Interface**: Command-line arguments, flags, options
3. **Inputs**: Required vs optional parameters
4. **Outputs**: Success messages, JSON, formatted tables
5. **Error Handling**: Common failure modes, recovery strategies
6. **Examples**: 3-5 real-world usage examples

**Minimum Script Set** (expand if needed):
1. **gh-project-init**: Initialize configuration, validate setup
2. **gh-project-create**: Create draft issue with custom fields
3. **gh-project-list**: Query/filter items with jq patterns
4. **gh-project-update**: Update draft/repo issue fields
5. **gh-project-convert**: Convert draft → repo issue (with confirmation)
6. **gh-project-delete**: Delete/archive items
7. **gh-project-link**: Set parent epic relationship

**Phase 3: Implementation Details**

1. **Caching Strategy**:
   - Cache file location and format
   - When to invalidate cache
   - Cache refresh mechanism
   - Handling cache corruption

2. **Error Handling Patterns**:
   - Network failures (retry with exponential backoff)
   - Authentication errors (clear message with fix)
   - Rate limiting (wait and retry)
   - GraphQL errors (parse and display)
   - Missing dependencies (check at startup)

3. **User Experience**:
   - Dry-run mode (--dry-run flag)
   - Verbose mode (--verbose for debugging)
   - Color output (success=green, error=red, warning=yellow)
   - Progress indicators for bulk operations
   - Confirmation prompts for destructive actions

4. **Testing Strategy**:
   - How to test scripts safely
   - Test project setup
   - Validation checklist
   - Rollback procedures

**Phase 4: Advanced Features**

1. **Bulk Operations**:
   - Create multiple items from CSV/JSON
   - Bulk update custom fields
   - Bulk conversion (with safeguards)

2. **Query Patterns**:
   - Pre-built jq filters for common queries
   - Export to CSV
   - Summary statistics (count by status, type, etc.)

3. **Workflow Helpers**:
   - Create epic + stories from template
   - Close epic and all linked stories
   - Move items between project views

**Phase 5: Migration Path**

1. **From Current Workflow**:
   - How to transition from repository issues to draft-first
   - Handling existing repository issues already in project
   - Cleanup of duplicate entries

2. **Documentation**:
   - README with installation and setup
   - Usage guide with examples
   - Troubleshooting section
   - API reference for each script

### Output Specification

Save implementation plan to: `.prompts/002-github-projects-scripts-plan/github-projects-scripts-plan.md`

**Structure**:

```xml
<plan version="1.0">

<executive_summary>
<!-- 2-3 paragraphs: Recommended approach, rationale, estimated effort -->
</executive_summary>

<architecture>
<file_organization>
  <!-- Script structure, naming, installation -->
</file_organization>
<configuration>
  <!-- Config file format, location, validation -->
</configuration>
<shared_library>
  <!-- Core functions, utilities, helpers -->
</shared_library>
</architecture>

<scripts>
<script name="gh-project-init">
  <purpose><!-- What and why --></purpose>
  <interface>
    <!-- Command-line args, flags, options -->
    <usage>gh-project-init [OPTIONS]</usage>
    <arguments>
      <arg name="--project" required="true">Project ID or URL</arg>
      <!-- More arguments -->
    </arguments>
  </interface>
  <behavior><!-- What it does step by step --></behavior>
  <examples>
    <example>
      <command>gh-project-init --project 14</command>
      <description>Initialize for project #14</description>
    </example>
    <!-- 3-5 examples -->
  </examples>
  <error_handling><!-- Common errors and recovery --></error_handling>
</script>

<!-- Repeat for each script -->
</scripts>

<implementation_details>
<caching>
  <!-- Strategy, file format, invalidation -->
</caching>
<error_handling>
  <!-- Patterns, retry logic, user messages -->
</error_handling>
<user_experience>
  <!-- Dry-run, verbose, colors, progress, confirmations -->
</user_experience>
</implementation_details>

<testing>
<test_environment>
  <!-- How to set up safe test project -->
</test_environment>
<validation_checklist>
  <!-- How to verify scripts work correctly -->
</validation_checklist>
</testing>

<advanced_features>
<!-- Bulk operations, query patterns, workflow helpers -->
</advanced_features>

<migration>
<!-- How to transition from current workflow -->
</migration>

<documentation>
<!-- README structure, usage guide, troubleshooting -->
</documentation>

<implementation_order>
<!-- Recommended sequence for building scripts -->
<phase number="1" duration="2-3 hours">
  <deliverables>
    <!-- What to build first -->
  </deliverables>
</phase>
<!-- More phases -->
</implementation_order>

<metadata>
<confidence>
  <!-- HIGH/MEDIUM/LOW with justification -->
</confidence>

<dependencies>
  <!-- What's needed from research -->
  <!-- External dependencies (gh, jq, etc.) -->
</dependencies>

<open_questions>
  <!-- Decisions user must make -->
  <!-- e.g., "Monolithic vs modular script structure?" -->
</open_questions>

<assumptions>
  <!-- What's assumed about environment, usage, etc. -->
</assumptions>
</metadata>

</plan>
```

### Planning Depth

**Provide**:
- Specific recommendations (not just options)
- Concrete examples for each script
- Actual bash function signatures for shared library
- Real config file format (JSON or TOML)
- Detailed error handling patterns with code snippets
- Complete implementation order with time estimates

**Don't Provide**:
- Full script implementations (that's for next phase)
- Complete code (snippets and examples only)
- Every possible feature (focus on MVP + extensions)

### SUMMARY.md Requirement

**MUST** create: `.prompts/002-github-projects-scripts-plan/SUMMARY.md`

**Structure**:

```markdown
# GitHub Projects Scripts Implementation Plan Summary

**[Substantive one-liner describing recommended approach]**

## Version
v1.0 - Initial implementation plan

## Key Decisions

• [Script organization decision - monolithic vs modular]
• [Configuration approach - file location, format]
• [Caching strategy - what, where, when]
• [Error handling pattern - retries, messages]
• [Critical UX decision - dry-run, confirmations]

(5-7 bullet points, specific choices with rationale)

## Script Inventory

**Core Scripts** (MVP):
- `gh-project-init` - [One-line purpose]
- `gh-project-create` - [One-line purpose]
- [List all core scripts]

**Advanced Scripts** (Optional):
- [List optional/future scripts]

## Implementation Order

1. **Phase 1** (2-3 hours): [What to build first]
2. **Phase 2** (3-4 hours): [What's next]
3. **Phase 3** (2-3 hours): [Advanced features]

Total effort: [X-Y hours]

## Decisions Needed

• [Decision user must make before implementation]
• [Or: "None - ready to begin implementation"]

## Blockers

• [Dependency blocking start, if any]
• [Or: "None"]

## Next Step

[Concrete action - e.g., "Begin implementation with Phase 1 scripts" or "User to choose script organization preference"]
```

**One-Liner Requirements**:
- Must communicate the core architectural decision
- Examples:
  - ✅ "7 modular scripts with shared library; cache field metadata locally; GraphQL for draft editing"
  - ✅ "Single CLI tool with subcommands; config in ~/.config/gh-projects/; dry-run by default"
  - ❌ "Implementation plan for GitHub Projects scripts"
  - ❌ "Designed script architecture"

## Success Criteria

**Plan is complete when**:
1. ✅ Clear script organization decision (monolithic vs modular) with rationale
2. ✅ All core scripts specified (name, purpose, interface, examples)
3. ✅ Configuration strategy defined (format, location, validation)
4. ✅ Shared library functions outlined (signatures, purposes)
5. ✅ Caching strategy detailed (what, where, invalidation)
6. ✅ Error handling patterns documented (retry logic, messages)
7. ✅ UX features specified (dry-run, colors, progress, confirmations)
8. ✅ Testing approach defined (test project, validation checklist)
9. ✅ Implementation order phased with time estimates
10. ✅ SUMMARY.md created with substantive one-liner
11. ✅ All open questions clearly stated for user decisions
12. ✅ Next step is actionable (begin implementation or resolve decisions)

**Target Confidence**: HIGH (plan should be detailed and actionable)

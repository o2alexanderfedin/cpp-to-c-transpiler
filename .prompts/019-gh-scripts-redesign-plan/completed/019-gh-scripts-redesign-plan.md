<objective>
Create a comprehensive, phased implementation plan for redesigning GitHub Projects scripts following SOLID/KISS/DRY/YAGNI/TRIZ principles.

The plan will translate research findings into a concrete roadmap with specific scripts to create, architecture decisions, migration strategy, and implementation phases.

**Why this matters:** Current scripts violate fundamental principles. This plan ensures a principled, maintainable replacement that's simple and hard to misuse.

**Intended use:** This plan will guide the implementation work, enabling either automated execution or manual development.
</objective>

<context>
**Foundation:**
This plan builds directly on research findings from:
@.prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md

Read the research output to understand:
- SOLID/KISS/DRY/YAGNI/TRIZ principles for CLI scripts
- GitHub Projects V2 API capabilities
- Project items vs repository issues distinction
- Help text and error handling guidelines
- Lessons from existing implementation

**Current state:**
- Existing scripts in `~/.claude/skills/lib/gh-projects/`
- Recent bug fixes (PATH, case sensitivity) addressed symptoms
- Scripts will be moved to subdirectory for preservation
- New scripts will be principled replacement

**Requirements from user:**
- Very simple, very direct CRUD scripts
- Minimal options (hard to misuse)
- All scripts provide `--help`
- Cover: Projects, Epics, User Stories, Tasks, Spikes, Bugs
- Clear distinction between project items and repo issues
- Learn from old implementation, but fresh start
</context>

<plan_structure>
The plan must include:

1. **Architecture Decisions:**
   - Script organization (flat vs hierarchical)
   - Naming conventions
   - Resource-oriented vs operation-oriented
   - Common library design
   - Configuration management

2. **Complete Script Inventory:**
   - List every script to create
   - Purpose and single responsibility for each
   - Minimal option set for each
   - Dependencies between scripts

3. **Common Library Design:**
   - What functions belong in shared code
   - Configuration loading
   - Error handling utilities
   - API wrapper functions
   - DRY without over-abstraction

4. **Migration Strategy:**
   - Move existing scripts to `~/.claude/skills/lib/gh-projects-legacy/`
   - Update skills that reference old scripts
   - Provide migration guide/mapping
   - Testing plan for equivalence

5. **Implementation Phases:**
   - Phase 1: Foundation (common library, config, core utilities)
   - Phase 2: Project-level CRUD
   - Phase 3: Item CRUD (Epic, Story, Task, Spike, Bug)
   - Phase 4: Advanced queries and filters
   - Phase 5: Migration and testing

6. **Quality Standards:**
   - Help text requirements
   - Error message format
   - Exit code conventions
   - Validation rules
   - Testing criteria

7. **Examples:**
   - Concrete examples of new script usage
   - Before/after comparison with old scripts
   - Common workflows using new scripts
</plan_structure>

<critical_decisions>
**Decide in this plan:**

1. **Script granularity:**
   - One script per resource-operation (`gh-epic-create`, `gh-epic-read`, etc.)?
   - One script per resource with subcommands (`gh-epic create`, `gh-epic read`)?
   - Hybrid approach?

2. **Configuration:**
   - Environment variables?
   - Config file (~/.gh-projects-config)?
   - Command-line flags every time?
   - How to DRY project number/owner across scripts?

3. **Item type handling:**
   - Separate scripts for Epic vs Story vs Task?
   - Generic item script with --type flag?
   - How to enforce type-specific validations?

4. **Help text depth:**
   - Brief one-liner vs detailed examples?
   - Separate --help vs --help-verbose?
   - How to balance brevity and completeness?

5. **Backward compatibility:**
   - Migration guide only?
   - Temporary wrapper scripts?
   - How to update dependent skills?

**Apply principles:**
- **KISS:** Choose simplest approach that works
- **YAGNI:** Defer advanced features to later phases
- **TRIZ:** What's the "ideal final result" - scripts that are so simple they need no documentation beyond --help?
</critical_decisions>

<requirements>
**Plan must specify:**

1. **For each script:**
   - Exact filename and location
   - Single responsibility statement
   - Command-line interface (arguments, flags)
   - Help text content
   - Error scenarios and messages
   - Exit codes
   - Dependencies on other scripts/functions

2. **For common library:**
   - Filename and location
   - Functions to provide
   - Configuration schema
   - Error handling approach
   - How to source/import

3. **For each phase:**
   - Scripts to implement
   - Dependencies on previous phases
   - Testing criteria
   - Acceptance criteria
   - Estimated complexity (simple/medium/complex)

4. **For migration:**
   - Old script → new script mapping
   - Breaking changes
   - Migration checklist
   - Skills to update

**Constraints:**
- Must work with GitHub Projects V2 API
- Must use `gh` CLI (no direct GraphQL)
- Must be POSIX-compatible shell scripts (bash/zsh)
- Must handle field case sensitivity correctly
- Must distinguish project items from repo issues clearly
</requirements>

<output_format>
Save plan to: `.prompts/019-gh-scripts-redesign-plan/gh-scripts-redesign-plan.md`

Structure as XML for Claude parsing:

```xml
<implementation_plan>
  <meta>
    <version>v1</version>
    <date>2025-12-15</date>
    <based_on>
      @.prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md
    </based_on>
  </meta>

  <architecture>
    <decisions>
      <script_organization>
        <!-- Chosen approach with rationale -->
      </script_organization>

      <naming_convention>
        <!-- Pattern: gh-{resource}-{operation}.sh -->
        <!-- Examples -->
      </naming_convention>

      <configuration>
        <!-- How project number/owner is managed -->
      </configuration>

      <common_library>
        <!-- Location, sourcing pattern, responsibilities -->
      </common_library>
    </decisions>

    <directory_structure>
      <!-- Complete tree showing all scripts and organization -->
    </directory_structure>

    <principles_applied>
      <solid>
        <!-- How each principle manifests in design -->
      </solid>
      <kiss>
        <!-- Simplicity decisions made -->
      </kiss>
      <dry>
        <!-- What's shared, what's duplicated intentionally -->
      </dry>
      <yagni>
        <!-- What's deferred to future phases -->
      </yagni>
      <triz>
        <!-- Ideal final result achieved -->
      </triz>
    </principles_applied>
  </architecture>

  <script_inventory>
    <common_library>
      <script>
        <path>~/.claude/skills/lib/gh-projects/lib/common.sh</path>
        <purpose>Shared utilities, configuration, error handling</purpose>
        <responsibilities>
          • Load configuration (project number, owner)
          • API wrapper functions (ensure PATH, handle errors)
          • Field name normalization (handle case sensitivity)
          • Help text formatter
          • Exit code constants
        </responsibilities>
        <exports>
          <!-- Functions and variables available to other scripts -->
        </exports>
      </script>
    </common_library>

    <project_scripts>
      <script>
        <path>~/.claude/skills/lib/gh-projects/gh-project-create.sh</path>
        <purpose>Create a new GitHub Project</purpose>
        <responsibility>Single operation: project creation</responsibility>
        <interface>
          <usage>gh-project-create.sh --title "Project Title" [--owner OWNER]</usage>
          <options>
            <option>
              <flag>--title</flag>
              <required>yes</required>
              <description>Project title</description>
            </option>
            <option>
              <flag>--owner</flag>
              <required>no</required>
              <description>Owner (defaults from config)</description>
            </option>
            <option>
              <flag>--help</flag>
              <required>no</required>
              <description>Show help</description>
            </option>
          </options>
        </interface>
        <help_text>
          <!-- Complete help text content -->
        </help_text>
        <errors>
          <!-- Error scenarios, messages, exit codes -->
        </errors>
        <example>
          <!-- Concrete usage example -->
        </example>
      </script>

      <!-- gh-project-read.sh -->
      <!-- gh-project-update.sh -->
      <!-- gh-project-delete.sh -->
      <!-- gh-project-list.sh -->
    </project_scripts>

    <item_scripts>
      <!-- Pattern for Epic, Story, Task, Spike, Bug -->
      <!-- Each gets: create, read, update, delete, list -->

      <script>
        <path>~/.claude/skills/lib/gh-projects/gh-epic-create.sh</path>
        <purpose>Create a new Epic in the project</purpose>
        <responsibility>Single operation: epic creation</responsibility>
        <interface>
          <usage>gh-epic-create.sh --title "Epic Title" [--status STATUS] [--description DESC]</usage>
          <options>
            <!-- Minimal options, sensible defaults -->
          </options>
        </interface>
        <!-- ... complete specification ... -->
      </script>

      <!-- Repeat pattern for all item types and operations -->
    </item_scripts>

    <query_scripts>
      <!-- Advanced: filtering, searching, reports -->
      <!-- Deferred to Phase 4 per YAGNI -->
    </query_scripts>
  </script_inventory>

  <migration_strategy>
    <preservation>
      <action>Move existing scripts to legacy directory</action>
      <from>~/.claude/skills/lib/gh-projects/</from>
      <to>~/.claude/skills/lib/gh-projects-legacy/</to>
      <preserve>
        <!-- What to keep for reference -->
      </preserve>
    </preservation>

    <mapping>
      <!-- Old script → New script(s) -->
      <old_to_new>
        <entry>
          <old>gh-project-list.sh --type epic --format json</old>
          <new>gh-epic-list.sh --format json</new>
          <notes>Simpler interface, type implicit</notes>
        </entry>
        <!-- ... complete mapping ... -->
      </old_to_new>
    </mapping>

    <skills_to_update>
      <!-- List skills that reference old scripts -->
      <!-- How to update each -->
    </skills_to_update>

    <breaking_changes>
      <!-- What no longer works the same way -->
      <!-- Why each change improves the design -->
    </breaking_changes>
  </migration_strategy>

  <implementation_phases>
    <phase number="1">
      <name>Foundation</name>
      <goal>Establish common library and configuration</goal>
      <deliverables>
        <deliverable>
          <file>lib/common.sh</file>
          <description>Shared utilities and configuration</description>
          <complexity>medium</complexity>
        </deliverable>
        <deliverable>
          <file>lib/config-example.sh</file>
          <description>Configuration template</description>
          <complexity>simple</complexity>
        </deliverable>
      </deliverables>
      <dependencies>None (foundation)</dependencies>
      <acceptance_criteria>
        • common.sh can be sourced without errors
        • Configuration loads from file or env vars
        • PATH issue resolved (gh always found)
        • Field name handling correct (lowercase)
      </acceptance_criteria>
    </phase>

    <phase number="2">
      <name>Project CRUD</name>
      <goal>Basic project management</goal>
      <deliverables>
        <!-- gh-project-create, read, update, delete, list -->
      </deliverables>
      <dependencies>Phase 1 (common library)</dependencies>
      <acceptance_criteria>
        <!-- Specific tests -->
      </acceptance_criteria>
    </phase>

    <phase number="3">
      <name>Item CRUD - Core Types</name>
      <goal>Epic and User Story management</goal>
      <deliverables>
        <!-- gh-epic-*, gh-story-* scripts -->
      </deliverables>
      <dependencies>Phase 2 (project must exist)</dependencies>
      <acceptance_criteria>
        <!-- Specific tests -->
      </acceptance_criteria>
    </phase>

    <phase number="4">
      <name>Item CRUD - Additional Types</name>
      <goal>Task, Spike, Bug management</goal>
      <deliverables>
        <!-- gh-task-*, gh-spike-*, gh-bug-* scripts -->
      </deliverables>
      <dependencies>Phase 3 (pattern established)</dependencies>
      <acceptance_criteria>
        <!-- Specific tests -->
      </acceptance_criteria>
    </phase>

    <phase number="5">
      <name>Migration and Testing</name>
      <goal>Replace old scripts, update skills, verify equivalence</goal>
      <deliverables>
        <!-- Migration guide, skill updates, test suite -->
      </deliverables>
      <dependencies>Phases 1-4 (all scripts ready)</dependencies>
      <acceptance_criteria>
        <!-- All skills work with new scripts -->
        <!-- Old scripts archived -->
        <!-- No regressions -->
      </acceptance_criteria>
    </phase>
  </implementation_phases>

  <quality_standards>
    <help_text>
      <format>
        <!-- Standard format for all scripts -->
      </format>
      <template>
        <!-- Concrete template to use -->
      </template>
    </help_text>

    <error_messages>
      <guidelines>
        <!-- How to write helpful errors -->
      </guidelines>
      <examples>
        <!-- Good vs bad error messages -->
      </examples>
    </error_messages>

    <exit_codes>
      <standard>
        0 - Success
        1 - General error
        2 - Misuse (invalid arguments)
        3 - Configuration error
        4 - API error
      </standard>
    </exit_codes>

    <validation>
      <input_validation>
        <!-- Required fields, format checks -->
      </input_validation>
      <pre_flight_checks>
        <!-- gh installed, authenticated, etc. -->
      </pre_flight_checks>
    </validation>

    <testing>
      <unit_tests>
        <!-- How to test individual scripts -->
      </unit_tests>
      <integration_tests>
        <!-- How to test workflows -->
      </integration_tests>
    </testing>
  </quality_standards>

  <examples>
    <workflow name="Create epic and add stories">
      <old_way>
        <!-- How it was done with old scripts -->
      </old_way>
      <new_way>
        <!-- How it's done with new scripts -->
      </new_way>
      <comparison>
        <!-- Why new way is better -->
      </comparison>
    </workflow>

    <!-- More workflow examples -->
  </examples>

  <confidence>high</confidence>

  <dependencies>
    <required>
      • Phase 1 must complete before Phase 2
      • Research findings (@018) inform all decisions
      • GitHub CLI version 2.0+
      • Projects V2 API
    </required>
  </dependencies>

  <open_questions>
    • Should we support Projects V1 for backward compatibility? (Recommend: No, V2 only)
    • Should epic/story parent-child relationships be enforced? (Recommend: Defer to future)
    • Should we provide bulk operations (create many items)? (Recommend: YAGNI, defer)
  </open_questions>

  <assumptions>
    • Users have gh CLI installed and authenticated
    • Single project per repository context
    • Custom fields (Type, Status, Priority) exist in project
    • Bash 4.0+ or Zsh 5.0+ available
  </assumptions>
</implementation_plan>
```

Also create: `.prompts/019-gh-scripts-redesign-plan/SUMMARY.md`

```markdown
# GitHub Projects Scripts Redesign - Implementation Plan

**Phase-based roadmap for SOLID/KISS/DRY-compliant CRUD scripts with minimal options**

v1 • 2025-12-15
Based on: @018-gh-scripts-redesign-research

## Key Decisions

• **Script organization:** [Decision made - e.g., "One script per resource-operation"]
• **Naming pattern:** [e.g., "gh-{resource}-{operation}.sh"]
• **Configuration:** [e.g., "Config file + env var override"]
• **Item types:** [e.g., "Separate scripts per type (gh-epic-*, gh-story-*, etc.)"]
• **Migration:** Move old scripts to gh-projects-legacy/, no wrapper compatibility

## Script Inventory

**Phase 1 - Foundation:**
- lib/common.sh (shared utilities, config, error handling)
- lib/config-example.sh (configuration template)

**Phase 2 - Project CRUD:** 5 scripts
- gh-project-create, read, update, delete, list

**Phase 3 - Epic & Story CRUD:** 10 scripts
- gh-epic-{create,read,update,delete,list}
- gh-story-{create,read,update,delete,list}

**Phase 4 - Task/Spike/Bug CRUD:** 15 scripts
- gh-task-*, gh-spike-*, gh-bug-* (5 operations each)

**Phase 5 - Migration:**
- Migration guide, skill updates, testing

**Total:** ~32 scripts across 5 phases

## Implementation Phases

1. **Foundation** (Medium) - Common library, config
2. **Project CRUD** (Simple) - 5 scripts for project management
3. **Epic & Story** (Medium) - 10 scripts for core item types
4. **Task/Spike/Bug** (Simple) - 15 scripts following established pattern
5. **Migration** (Medium) - Archive old, update skills, test

## Decisions Needed

• Approve script organization and naming convention
• Approve configuration approach
• Approve phase breakdown and order
• Review help text template
• Confirm YAGNI deferrals (no bulk ops, no V1 support)

## Blockers

None - ready to implement once plan approved

## Next Step

**Option A:** Auto-implement with /run-prompt
- Executes all 5 phases sequentially
- Creates all scripts, migrates legacy, updates skills

**Option B:** Manual phase-by-phase
- Implement Phase 1, test, then continue
- More control, can adjust between phases

**Option C:** Create phase-specific prompts
- Generate 5 separate implementation prompts (one per phase)
- Execute phases independently

---

**For auto-execution:** Run this plan prompt to implement all phases
**For manual execution:** Review plan, then implement following phase order
```
</output_format>

<verification>
Before completing, verify:

**Plan completeness:**
- [ ] Architecture decisions made with rationale
- [ ] Complete script inventory with specifications
- [ ] Common library responsibilities defined
- [ ] Migration strategy detailed
- [ ] All 5 phases specified with deliverables
- [ ] Quality standards established
- [ ] Examples showing before/after

**Traceability:**
- [ ] Research findings (@018) referenced and applied
- [ ] User requirements addressed (simple, minimal options, --help)
- [ ] SOLID/KISS/DRY/YAGNI/TRIZ principles applied
- [ ] Project vs repo issues distinction maintained

**Implementability:**
- [ ] Each script fully specified (name, interface, help, errors)
- [ ] Dependencies clear (what needs what)
- [ ] Phases have clear acceptance criteria
- [ ] Testing approach defined

**Output requirements:**
- [ ] Full plan saved to `gh-scripts-redesign-plan.md` with XML structure
- [ ] SUMMARY.md created with substantive one-liner
- [ ] Script inventory is complete (every script listed)
- [ ] Decisions needed are specific
- [ ] Next step offers execution options
</verification>

<success_criteria>
- [ ] Complete architectural design for new script system
- [ ] Every script specified with interface, help, errors
- [ ] Common library responsibilities defined
- [ ] Migration path from old scripts clear
- [ ] 5 implementation phases with deliverables and acceptance criteria
- [ ] Quality standards (help, errors, exit codes) established
- [ ] Examples demonstrate improved simplicity
- [ ] Plan is executable (can be implemented directly or via prompts)
- [ ] SOLID/KISS/DRY/YAGNI/TRIZ principles evident throughout
</success_criteria>

<research_objective>
Research best practices for designing simple, principled CLI scripts for GitHub Projects CRUD operations that follow SOLID/KISS/DRY/YAGNI/TRIZ principles.

The goal is to gather authoritative guidance on CLI design patterns, script architecture, and GitHub Projects API usage to inform a complete redesign of existing gh-projects scripts.

**Why this matters:** Current scripts violate fundamental design principles, making them error-prone and hard to use. A principled redesign will create maintainable, intuitive tools.

**Intended use:** Findings will directly inform the planning phase (019-gh-scripts-redesign-plan) which will create the implementation roadmap.
</research_objective>

<context>
**Current situation:**
- Existing scripts in `~/.claude/skills/lib/gh-projects/` have design problems
- Scripts violate SOLID/KISS/DRY/YAGNI/TRIZ principles
- Too many options, confusing interfaces, easy to make mistakes
- Recent fixes (PATH issues, case sensitivity) address symptoms, not root cause

**Target architecture:**
- Very simple, very direct CRUD scripts for:
  - GitHub Projects (CRUD)
  - Epics (CRUD)
  - User Stories (CRUD)
  - Tasks (CRUD)
  - Spikes (CRUD)
  - Bugs (CRUD)
- Minimal options per script (hard to misuse)
- All scripts provide `--help`
- Clear distinction between GitHub Project items vs Repository issues

**Migration strategy:**
- Move existing scripts to subdirectory (preserve for learning)
- Learn from old implementation patterns
- Create fresh, principled implementation
- No backward compatibility layer needed
</context>

<scope>
**In scope:**
1. **CLI Design Principles:**
   - SOLID principles applied to shell scripts
   - KISS/DRY/YAGNI/TRIZ in practice
   - Minimal option sets, maximum clarity
   - Help text best practices
   - Error handling and user feedback

2. **GitHub Projects API:**
   - Official GitHub CLI (`gh`) capabilities for Projects V2
   - CRUD operations for projects and items
   - Custom field handling (Type, Status, Priority, etc.)
   - GraphQL vs REST API considerations
   - Item types: Epic, User Story, Task, Spike, Bug

3. **Script Architecture:**
   - Single Responsibility: one script, one operation
   - Common library patterns for DRY compliance
   - Configuration management (project number, owner, etc.)
   - Naming conventions for discoverability

4. **GitHub Project vs Repository Issues:**
   - Critical distinction between project items and repo issues
   - How items link to issues
   - When to use which API
   - Common confusion points to avoid

**Out of scope:**
- Implementation details (that's for the plan phase)
- Testing strategies (plan phase)
- Deployment/installation (plan phase)
- GitHub Actions integration (future consideration)

**Prioritize:**
- Official GitHub documentation
- POSIX shell scripting best practices
- Real-world CLI tool examples (git, docker, kubectl patterns)
- Authoritative sources over blog posts

**Time period:**
- Current GitHub Projects V2 API (2023-2025)
- Modern bash/zsh practices (avoid deprecated patterns)
</scope>

<research_areas>
<area_1_cli_design_principles>
**Questions to answer:**
- How do SOLID principles apply to CLI scripts?
  - Single Responsibility: How granular should scripts be?
  - Open/Closed: Extensibility in shell scripts?
  - Dependency Inversion: Abstract vs concrete in bash?
- What makes a CLI "simple" (KISS)?
- How to avoid duplication (DRY) without over-abstracting?
- YAGNI in practice: What features to defer?
- TRIZ: What's the "ideal final result" for a CRUD script?

**Sources:**
- POSIX shell command design conventions
- GNU Coding Standards (CLI sections)
- The Art of Unix Programming (CLI chapter)
- Modern CLI tool design (Heroku CLI guidelines, 12-factor CLI)

**Deliverable:**
- Concrete design principles checklist
- Anti-patterns to avoid
- Examples of excellent CLI tools to emulate
</area_1_cli_design_principles>

<area_2_github_projects_api>
**Questions to answer:**
- What are the complete `gh project` subcommands?
  - item-list, item-create, item-edit, item-delete, item-add?
  - field-list, field-create, field-delete?
- How to filter/query by custom fields (Type: Epic, Status: Todo)?
- How to handle field case sensitivity (learned: lowercase in JSON)?
- What's the GraphQL schema for Projects V2?
- How do project items relate to repository issues?
  - Creating project-only items vs linking to issues
  - When items ARE issues vs when they reference issues

**Sources:**
- `gh project --help` and all subcommands
- GitHub Projects V2 GraphQL API documentation
- GitHub CLI source code (for patterns)
- Official migration guides (V1 → V2)

**Deliverable:**
- Complete API capability matrix
- Field name reference (actual JSON keys)
- Item type architecture diagram
- Project item vs repo issue decision tree
</area_2_github_projects_api>

<area_3_script_architecture>
**Questions to answer:**
- How should scripts be organized?
  - `gh-project-create`, `gh-project-read`, `gh-project-update`, `gh-project-delete`?
  - `gh-epic-create`, `gh-epic-list`, etc.?
  - Or resource-oriented: `gh-project`, `gh-epic` with subcommands?
- Where should common code live?
  - Shared library: What belongs there?
  - Configuration: How to DRY project number/owner?
- How to handle authentication/credentials?
- How to make scripts discoverable?

**Sources:**
- Git's command structure (model of good CLI design)
- Docker CLI architecture
- Existing gh-projects scripts (what worked, what didn't)
- Shell script best practices (Google Shell Style Guide)

**Deliverable:**
- Proposed directory structure
- Naming convention rules
- Common library responsibilities
- Configuration management approach
</area_3_script_architecture>

<area_4_help_and_error_handling>
**Questions to answer:**
- What makes great `--help` output?
  - Format, structure, examples?
  - How much detail before it's overwhelming?
- How to provide usage errors that guide users to success?
- Exit codes: What conventions to follow?
- Validation: When to fail fast vs provide defaults?

**Sources:**
- POSIX exit code conventions
- Examples from well-designed tools (curl, jq, gh itself)
- GNU help text guidelines

**Deliverable:**
- Help text template/format
- Error message guidelines
- Exit code standards
- Validation strategy
</area_4_help_and_error_handling>
</research_areas>

<methodology>
**Research process:**
1. **Consult official documentation first:**
   - Read `gh project --help` and all subcommands
   - Review GitHub Projects V2 API docs
   - Check GitHub CLI documentation

2. **Study exemplar tools:**
   - Analyze git, docker, kubectl command structures
   - Note patterns in their help output, error messages
   - Identify what makes them intuitive

3. **Review current implementation:**
   - Read existing gh-projects scripts to understand:
     - What operations are needed
     - What worked well
     - What caused confusion (especially project vs repo issues)
   - Document lessons learned

4. **Synthesize principles:**
   - Extract concrete, actionable guidelines
   - Create checklists and templates
   - Provide specific examples

**Quality controls:**
1. **Verification checklist:**
   - [ ] Consulted official GitHub documentation
   - [ ] Tested `gh project` commands directly
   - [ ] Reviewed at least 3 exemplar CLI tools
   - [ ] Read existing scripts to understand current patterns
   - [ ] Verified API capabilities with actual commands
   - [ ] Documented field name case sensitivity findings

2. **Pre-submission QA:**
   - Distinguish verified facts from assumptions
   - Mark confidence level for each finding
   - List sources for all claims
   - Note any conflicting information found

3. **Streaming write:**
   - Write findings incrementally to output file as research progresses
   - Don't wait until end to write everything
   - Allows parallel reading if needed
</methodology>

<output_format>
Save comprehensive research to: `.prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md`

Structure as XML for Claude parsing in plan phase:

```xml
<research_findings>
  <meta>
    <version>v1</version>
    <date>2025-12-15</date>
    <confidence>high|medium|low</confidence>
    <sources_consulted>
      <source>
        <name>GitHub Projects V2 API Documentation</name>
        <url>https://docs.github.com/...</url>
        <verified>yes|no</verified>
      </source>
      <!-- ... more sources ... -->
    </sources_consulted>
  </meta>

  <cli_design_principles>
    <solid_for_shell_scripts>
      <single_responsibility>
        <!-- Findings with examples -->
      </single_responsibility>
      <!-- ... other principles ... -->
    </solid_for_shell_scripts>

    <kiss_guidelines>
      <!-- Concrete, actionable guidelines -->
    </kiss_guidelines>

    <dry_patterns>
      <!-- What to share, what to duplicate -->
    </dry_patterns>

    <yagni_boundaries>
      <!-- What to include, what to defer -->
    </yagni_boundaries>

    <triz_ideal_state>
      <!-- What's the "perfect" CRUD script? -->
    </triz_ideal_state>

    <anti_patterns>
      <!-- What to absolutely avoid -->
    </anti_patterns>
  </cli_design_principles>

  <github_projects_api>
    <gh_cli_capabilities>
      <!-- Complete command reference -->
    </gh_cli_capabilities>

    <field_schema>
      <!-- Actual JSON field names, case sensitivity -->
    </field_schema>

    <item_types>
      <!-- Epic, Story, Task, Spike, Bug definitions -->
    </item_types>

    <project_vs_repo_issues>
      <critical_distinction>
        <!-- How they differ -->
      </critical_distinction>
      <when_to_use_which>
        <!-- Decision criteria -->
      </when_to_use_which>
      <api_differences>
        <!-- Different endpoints, commands -->
      </api_differences>
    </project_vs_repo_issues>
  </github_projects_api>

  <script_architecture>
    <proposed_structure>
      <!-- Directory layout, naming conventions -->
    </proposed_structure>

    <common_library_design>
      <!-- What belongs in shared code -->
    </common_library_design>

    <configuration_management>
      <!-- How to handle project number, owner, etc. -->
    </configuration_management>
  </script_architecture>

  <help_and_errors>
    <help_text_format>
      <!-- Template and guidelines -->
    </help_text_format>

    <error_messages>
      <!-- How to write helpful errors -->
    </error_messages>

    <exit_codes>
      <!-- Standard conventions -->
    </exit_codes>
  </help_and_errors>

  <exemplars>
    <tool name="git">
      <!-- What to emulate from git -->
    </tool>
    <!-- ... other exemplars ... -->
  </exemplars>

  <lessons_from_existing>
    <what_worked>
      <!-- Patterns worth keeping -->
    </what_worked>
    <what_failed>
      <!-- Problems that need solving -->
    </what_failed>
    <confusion_points>
      <!-- Especially project vs repo issues -->
    </confusion_points>
  </lessons_from_existing>

  <confidence>medium-high</confidence>

  <dependencies>
    <required>
      • GitHub CLI (gh) version 2.0+
      • GitHub Projects V2 (not V1)
      • Bash 4.0+ or Zsh 5.0+
    </required>
  </dependencies>

  <open_questions>
    • Should scripts support both V1 and V2 projects, or V2 only?
    • What's the migration path for existing skills using old scripts?
    • How to handle rate limiting in automation scenarios?
  </open_questions>

  <assumptions>
    • Users have gh CLI installed and authenticated
    • Projects use custom fields named "Type", "Status", "Priority"
    • Single project per repository (not multi-project scenarios)
  </assumptions>
</research_findings>
```

Also create: `.prompts/018-gh-scripts-redesign-research/SUMMARY.md`

```markdown
# GitHub Projects Scripts Redesign - Research

**SOLID/KISS/DRY/YAGNI-compliant CLI scripts with crystal-clear interfaces**

v1 • 2025-12-15

## Key Findings

• **Single Responsibility per script** - One script = one operation (create/read/update/delete) on one resource
• **GitHub CLI provides** - [list actual capabilities found]
• **Field names are lowercase** - Despite PascalCase UI, JSON uses .type, .status, .priority
• **Project items ≠ Repo issues** - [critical distinction with examples]
• **Help text format** - [standard format identified from exemplars]

## Quality Report

**Verified claims:**
- GitHub CLI capabilities (tested with `gh project --help`)
- Field case sensitivity (confirmed from previous bug fix)
- [... list other verified findings ...]

**Assumed (needs verification in plan phase):**
- [... list assumptions that should be validated ...]

## Decisions Needed

• Should we support both Projects V1 and V2, or V2 only?
• Should epic/story/task be separate scripts or subcommands?
• How much backward compatibility with existing scripts?

## Blockers

None

## Next Step

Create planning prompt (019-gh-scripts-redesign-plan) to design:
- Complete script inventory (what scripts to create)
- Directory structure and naming
- Common library interface
- Migration strategy from old scripts
- Implementation phases

---

**Referenced in plan:** `.prompts/019-gh-scripts-redesign-plan/` should reference this research with `@.prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md`
```
</output_format>

<verification>
Before completing, verify:

**Research completeness:**
- [ ] All four research areas addressed
- [ ] Official documentation consulted and cited
- [ ] At least 3 exemplar tools analyzed
- [ ] Existing scripts reviewed for lessons
- [ ] Concrete examples provided (not just theory)

**Quality assurance:**
- [ ] Verification checklist completed
- [ ] Quality report distinguishes verified vs assumed
- [ ] Sources listed with URLs where applicable
- [ ] Confidence level assigned to findings
- [ ] Critical project vs repo issue distinction clarified with examples

**Output requirements:**
- [ ] Full research saved to `gh-scripts-redesign-research.md` with XML structure
- [ ] SUMMARY.md created with substantive one-liner
- [ ] Key findings are actionable (inform planning directly)
- [ ] Decisions needed are specific
- [ ] Next step is clear
</verification>

<success_criteria>
- [ ] Comprehensive understanding of SOLID/KISS/DRY/YAGNI/TRIZ for CLI scripts
- [ ] Complete GitHub Projects V2 API capability matrix
- [ ] Clear project items vs repo issues distinction with examples
- [ ] Concrete design principles checklist ready for planning
- [ ] Help text and error handling guidelines established
- [ ] Script architecture patterns identified
- [ ] Lessons from existing implementation documented
- [ ] All findings backed by authoritative sources
- [ ] Output enables planning phase to proceed without ambiguity
</success_criteria>

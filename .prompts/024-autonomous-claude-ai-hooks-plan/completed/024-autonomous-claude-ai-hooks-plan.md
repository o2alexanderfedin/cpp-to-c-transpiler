<objective>
Create a detailed, step-by-step implementation plan for autonomous Claude operation using AI-based hooks.

Purpose: Transform research findings into actionable implementation phases with complete configurations, testing procedures, and rollout strategy
Input: Autonomous Claude AI hooks research findings
Output: autonomous-claude-ai-hooks-plan.md with ready-to-execute implementation phases
</objective>

<context>
Research findings: @.prompts/023-autonomous-claude-ai-hooks-research/autonomous-claude-ai-hooks-research.md
Research summary: @.prompts/023-autonomous-claude-ai-hooks-research/SUMMARY.md
Reference config: @.prompts/023-autonomous-claude-ai-hooks-research/COMPLETE-AUTONOMOUS-HOOKS-CONFIG.json

Key findings from research:
- **Prompt hooks discovered**: Native `type: "prompt"` support for LLM-based decisions (2-4s latency)
- **Three critical hooks**: PermissionRequest (auto-answer questions), Stop (verify completion), UserPromptSubmit (inject directives)
- **Zero technical blockers**: All required hooks exist and documented
- **Performance**: Hybrid fast/slow path averages 318ms (90% bash at 20ms, 10% LLM at 3000ms)
- **ROI**: 33x (saves 84 hours/year human time for $180/year API cost)
- **Feasibility verdict**: HIGHLY FEASIBLE - recommend immediate implementation

Previous hook work:
- PreToolUse hooks already deployed for GitHub CLI enforcement
- Hook configuration in `~/.claude/settings.json`
- Exit code 2 blocks tool execution
- Recursion prevention validated via settings override

User requirements for this plan:
- **Detail level**: Detailed step-by-step with specific files, exact configurations, testing procedures, rollout steps
- **Priorities**: Speed to first value + Full autonomy coverage + Performance optimization + Safety and reversibility
- **Artifacts**: Complete hook configs ready to deploy (.json/.sh files to copy directly)
</context>

<planning_requirements>
**What the plan needs to address:**

1. **Implementation Phases** (4-5 phases, each independently testable):
   - Phase 1: Stop hook MVP (completion verification) - HIGHEST PRIORITY for proving concept
   - Phase 2: PermissionRequest hook (auto-answer questions) - CORE AUTONOMY
   - Phase 3: UserPromptSubmit hook (inject autonomous directives) - QUESTION REDUCTION
   - Phase 4: Performance optimization (hybrid fast/slow path) - LATENCY IMPROVEMENT
   - Phase 5: Safety and trust-building (logging, escape hatches, monitoring) - PRODUCTION READINESS

2. **For EACH phase, provide:**
   - **Objective**: What this phase accomplishes and why it's sequenced here
   - **Configuration files**: Complete, ready-to-deploy hook configs with:
     - Exact file paths (e.g., `~/.claude/settings.json`, `~/.claude/hooks/validators/...`)
     - Full file contents (bash scripts, JSON configs, prompt text)
     - Installation commands (where to copy, what to edit)
   - **Testing procedure**: Step-by-step validation with:
     - Test scenarios to run
     - Expected behavior vs actual behavior
     - How to verify success
     - What to do if tests fail
   - **Rollback plan**: How to revert this phase if needed
   - **Success criteria**: Measurable outcomes (e.g., "Claude continues 3/3 times when work incomplete")
   - **Deliverables**: Specific files created, settings modified, capabilities added

3. **Configuration management:**
   - Where each hook config lives (`~/.claude/settings.json` vs `.claude/settings.json` per-project)
   - How to enable/disable autonomous mode per project
   - How to override globally with local settings

4. **Safety mechanisms:**
   - Escape hatches (Ctrl+C, config disable, emergency override)
   - Decision logging (what decisions were made autonomously, where logged)
   - Gradual rollout strategy (start with one hook, verify, add next)
   - Trust-building approach (review logs, tune prompts, build confidence)

5. **Performance optimization:**
   - Fast path implementation (bash pre-approval for 90% of cases)
   - Slow path implementation (prompt hook for 10% complex cases)
   - Latency measurement approach
   - Caching strategy (if applicable)

6. **Integration with existing hooks:**
   - PreToolUse hooks already deployed for GitHub CLI
   - How new autonomous hooks coexist with existing hooks
   - Combined settings.json structure

**Constraints to work within:**
- Hook timeout: 60 seconds for command hooks, 30 seconds for prompt hooks
- User is solo developer (no team coordination needed)
- Cost is not a constraint (optimize for human time savings)
- Must maintain YOLO mode speed and convenience
- Recursion prevention required for command hooks spawning Claude instances

**Success criteria for the planned outcome:**
- Each phase is independently testable and reversible
- Complete hook configurations provided (copy-paste ready)
- Testing procedures are specific enough to execute without interpretation
- Rollback plan for each phase clearly defined
- ROI is measurable (time saved, decisions automated, questions avoided)
- Trust can be built incrementally (logging, review, tuning)
</planning_requirements>

<output_structure>
Save to: `.prompts/024-autonomous-claude-ai-hooks-plan/autonomous-claude-ai-hooks-plan.md`

Structure the plan using this XML format:

```xml
<plan>
  <summary>
    {One paragraph overview of the implementation approach, sequencing rationale, and expected outcome}
  </summary>

  <phases>
    <phase number="1" name="stop-hook-mvp">
      <objective>{What this phase accomplishes and why it's first}</objective>

      <tasks>
        <task priority="high">{Specific actionable task with file paths and commands}</task>
        <task priority="medium">{Another task}</task>
      </tasks>

      <configuration_files>
        <file path="~/.claude/settings.json">
          <purpose>{What this config does}</purpose>
          <content>
            {Complete JSON or bash script content - ready to copy}
          </content>
          <installation>
            {How to install: edit existing file, append to hooks section, etc.}
          </installation>
        </file>
        <!-- Additional config files for this phase -->
      </configuration_files>

      <testing_procedure>
        <test scenario="incomplete-work-continuation">
          <description>{What to test}</description>
          <steps>
            <step>{Specific command to run}</step>
            <step>{What to observe}</step>
            <step>{How to verify success}</step>
          </steps>
          <expected_behavior>{What should happen}</expected_behavior>
          <success_criteria>{Measurable outcome}</success_criteria>
        </test>
        <!-- Additional test scenarios -->
      </testing_procedure>

      <rollback_plan>
        {Exact steps to revert this phase if needed}
      </rollback_plan>

      <deliverables>
        <deliverable>{Specific file or capability created}</deliverable>
      </deliverables>

      <success_metrics>
        {How to measure success: time saved, decisions automated, etc.}
      </success_metrics>

      <dependencies>{What must exist before this phase}</dependencies>

      <execution_notes>
        {Helpful context for implementing this phase: gotchas, tips, references}
      </execution_notes>
    </phase>

    <!-- Phases 2-5 with same structure -->
  </phases>

  <integration_architecture>
    <combined_settings>
      <description>How all hooks fit together in settings.json</description>
      <complete_config>
        {Full ~/.claude/settings.json showing all hooks integrated}
      </complete_config>
    </combined_settings>

    <per_project_overrides>
      {How to customize autonomy per project using .claude/settings.json}
    </per_project_overrides>

    <coexistence_with_existing_hooks>
      {How autonomous hooks work alongside PreToolUse hooks for GitHub CLI}
    </coexistence_with_existing_hooks>
  </integration_architecture>

  <safety_and_control>
    <escape_hatches>
      <mechanism name="keyboard-interrupt">{How Ctrl+C works}</mechanism>
      <mechanism name="config-disable">{How to turn off autonomous mode}</mechanism>
      <mechanism name="per-hook-disable">{How to disable individual hooks}</mechanism>
    </escape_hatches>

    <decision_logging>
      <log_location>{Where autonomous decisions are logged}</log_location>
      <log_format>{What's captured: timestamp, decision, reasoning, outcome}</log_format>
      <review_process>{How to review and tune based on logs}</review_process>
    </decision_logging>

    <trust_building_strategy>
      {Gradual rollout: Phase 1 only → review logs → Phase 2 → etc.}
    </trust_building_strategy>
  </safety_and_control>

  <performance_optimization>
    <fast_path>
      <description>{Bash pre-approval for 90% of common cases}</description>
      <implementation>{Bash script with pattern matching}</implementation>
      <coverage>{What percentage of decisions hit fast path}</coverage>
    </fast_path>

    <slow_path>
      <description>{Prompt hook for 10% complex cases}</description>
      <implementation>{LLM-based reasoning configuration}</implementation>
      <fallback>{What happens if slow path times out}</fallback>
    </slow_path>

    <latency_targets>
      - Fast path: <20ms
      - Slow path: 2-4 seconds
      - Average (weighted): <500ms
    </latency_targets>

    <measurement_approach>
      {How to measure actual latency during testing}
    </measurement_approach>
  </performance_optimization>

  <rollout_strategy>
    <phase_1_rollout>
      {Deploy Stop hook only, test for 1-3 sessions, review logs, decide to continue}
    </phase_1_rollout>

    <phase_2_rollout>
      {Add PermissionRequest, test, review, tune prompts if needed}
    </phase_2_rollout>

    <full_autonomy_timeline>
      - Day 1: Stop hook MVP deployed and tested
      - Day 2-3: PermissionRequest added and validated
      - Day 4: UserPromptSubmit added for question reduction
      - Week 2: Fast path optimization (optional)
      - Week 3+: Tune based on logs, build trust
    </full_autonomy_timeline>
  </rollout_strategy>

  <metadata>
    <confidence level="high">
      {Why high confidence: research validated feasibility, all hooks exist, no blockers}
    </confidence>

    <dependencies>
      - Claude Code CLI installed and working
      - Existing hooks in ~/.claude/settings.json (PreToolUse for GitHub)
      - Haiku API access (included with Claude Code)
      - jq installed for JSON parsing in bash hooks
    </dependencies>

    <open_questions>
      - Optimal verification criteria per project type (will tune during use)
      - Fast path coverage percentage (estimated 90%, will measure)
      - Prompt hook actual latency (estimated 2-4s, will measure)
    </open_questions>

    <assumptions>
      - User values human time over API cost (confirmed)
      - 6-7s latency is acceptable for complex decisions (confirmed)
      - User comfortable with gradual rollout and log review
      - Existing PreToolUse hooks for GitHub CLI remain active
    </assumptions>

    <risks_and_mitigations>
      <risk name="LLM-decision-quality">
        <mitigation>Decision logging, review process, prompt tuning</mitigation>
      </risk>
      <risk name="latency-perception">
        <mitigation>Fast path for 90% of cases, measurement and optimization</mitigation>
      </risk>
      <risk name="trust-in-autonomy">
        <mitigation>Gradual rollout, escape hatches, transparency via logging</mitigation>
      </risk>
    </risks_and_mitigations>
  </metadata>
</plan>
```
</output_structure>

<summary_requirements>
Create `.prompts/024-autonomous-claude-ai-hooks-plan/SUMMARY.md`

Include:
- **One-liner**: Substantive description of the implementation approach (e.g., "4-phase rollout starting with Stop hook MVP, achieving full autonomy in 1-2 weeks with safety mechanisms")
- **Version**: v1 (initial plan)
- **Phase Overview**: Brief summary of each phase with estimated time and value delivered
- **Key Configuration Files**: List of files that will be created/modified
- **Safety Mechanisms**: Escape hatches and logging approach
- **Rollout Timeline**: Expected timeline from MVP to full autonomy
- **Decisions Needed**: Any user choices required before implementation (should be minimal - plan provides all configs)
- **Blockers**: External impediments (should be none based on research)
- **Next Step**: "Execute Phase 1: Stop Hook MVP" with specific command or action
</summary_requirements>

<success_criteria>
This plan is successful when:

1. **Phase completeness**: All 4-5 phases defined with objectives, tasks, configs, testing, rollback
2. **Configuration readiness**: Every config file has complete contents ready to copy-paste
3. **Testing specificity**: Testing procedures are specific enough to execute without interpretation
4. **Rollback clarity**: Each phase has clear rollback steps
5. **Integration clarity**: Shows how all hooks fit together in combined settings.json
6. **Safety transparency**: Escape hatches, logging, and trust-building strategy clearly defined
7. **Performance optimization**: Fast/slow path implementation detailed with latency targets
8. **Execution readiness**: Plan can be handed to implementation prompt (or human) to execute immediately
9. **SUMMARY.md created**: With phase overview and next step
10. **Metadata complete**: Confidence, dependencies, open questions, assumptions, risks all documented

The plan should be so detailed that someone could execute it without referring back to the research.
</success_criteria>

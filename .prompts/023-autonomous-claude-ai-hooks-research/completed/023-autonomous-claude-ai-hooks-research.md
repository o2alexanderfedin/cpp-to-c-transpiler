<session_initialization>
Before beginning research, verify today's date:
!`date +%Y-%m-%d`

Use this date when searching for "current" or "latest" information.
</session_initialization>

<research_objective>
Research the feasibility of creating an autonomous Claude system using AI-based hooks that eliminate user interaction by:
1. Automatically answering questions Claude would normally ask the user
2. Verifying task completion and forcing continuation if work is incomplete

Purpose: Enable fully autonomous Claude operation in YOLO mode without sacrificing quality or completeness
Scope: Hook types, AI decision mechanisms, performance implications, recursion prevention
Output: autonomous-claude-ai-hooks-research.md with feasibility assessment and architecture recommendations
</research_objective>

<context>
**Recent Research Context:**
Reference the hook timeout and delegation architecture research:
@.prompts/022-hook-timeout-research-RESULTS.md

Key findings from that research:
- Bash hooks average 17ms execution time
- Claude API delegation takes 6-7 seconds (300-400x slower)
- Default hook timeout: 60 seconds (configurable)
- Recursion prevention possible via `--settings '{"hooks":{}}'` override

**Current Hook System:**
- PreToolUse hooks deployed for gh CLI blocking
- Exit code 2 blocks tool execution
- Hooks receive JSON via stdin, return JSON decisions
- Working prototypes exist for delegation architecture

**User Requirements:**
- Configurable autonomy (per project/context)
- Target hook types: PermissionRequest, UserPromptSubmit, Stop, Custom question hook
- Hybrid approach: Fast command hooks + prompt hooks for reasoning
- Goal: YOLO mode + full autonomy + quality assurance
</context>

<research_scope>
<include>
**1. Claude Code Hook Types for Autonomy**
- PermissionRequest hook: When Claude asks user for permission
  - Can we intercept and AI-answer these requests?
  - What information is available in the hook payload?
  - How to pass context to AI decision-maker?
- UserPromptSubmit hook: When user submits a prompt
  - Can we augment prompts with autonomous instructions?
  - Inject "don't ask questions, decide autonomously" directives?
- Stop hook: When Claude wants to stop execution
  - Can we verify task completion programmatically?
  - Force continuation if work incomplete?
  - How to assess "doneness" with AI?
- Custom question hook (if needed):
  - Does Claude Code support custom hook types?
  - Would we need to propose a new hook type?
  - AskUserQuestion interception mechanism?

**2. AI Decision Mechanisms**
- Type: "prompt" hooks (documented in Claude Code)
  - How do prompt hooks work vs command hooks?
  - Can prompt hooks access LLM for reasoning?
  - Performance characteristics?
- Separate Claude instance delegation
  - Spawn fresh Claude with specific system prompt
  - Pass hook context as input
  - Return decision to parent Claude
  - Cost and latency implications (from previous research)
- Hybrid fast/slow path
  - Deterministic rules for simple cases
  - AI reasoning for complex decisions
  - Caching layer for repeated patterns

**3. Recursion Prevention**
- Hook configuration inheritance
  - Do spawned Claude instances inherit parent hooks?
  - Can we override hooks via CLI flags?
  - Environment variable controls?
- Testing recursion prevention
  - How to verify hooks don't trigger themselves?
  - Safe fallbacks if recursion detected?

**4. Autonomous Question Answering**
- Question types Claude asks:
  - Clarification questions (ambiguous requirements)
  - Choice questions (multiple valid approaches)
  - Confirmation questions (verify assumptions)
- AI answering strategies:
  - Context-based inference (read project files, docs)
  - Policy-based defaults (configurable preferences)
  - Confidence thresholds (when to ask vs decide)
- Smart question resolution:
  - Parse AskUserQuestion calls from Claude
  - Generate answers using AI reasoning
  - Inject answers back into execution flow

**5. Completion Verification**
- Task completion criteria:
  - All requirements met (parse from original prompt)
  - No TODO markers or incomplete code
  - Tests written and passing
  - Documentation updated
  - Git committed (if requested)
- AI verification approach:
  - Analyze task output vs requirements
  - Check for common incompletion patterns
  - Forced continuation mechanism
- Stop hook implementation:
  - When Claude wants to stop, verify first
  - If incomplete, provide continuation guidance
  - Prevent premature termination

**6. Configuration and Control**
- Per-project autonomy settings:
  - Enable/disable autonomous mode
  - Autonomy level (full, selective, off)
  - Question types to auto-answer
  - Completion strictness
- Configuration storage:
  - `.claude/settings.json` additions
  - `.claude/autonomy-config.json` dedicated file
  - Environment variables
- User override mechanisms:
  - Emergency "ask me" escape hatch
  - Autonomous decision logging for review
  - Undo autonomous decisions

**7. Performance and Cost Analysis**
- Latency impact:
  - Prompt hooks vs command hooks
  - AI reasoning time for decisions
  - Acceptable delays for autonomy
- Cost implications:
  - API calls per autonomous decision
  - Caching effectiveness
  - Cost vs manual intervention trade-off
- User experience:
  - Perceived responsiveness
  - Transparency of autonomous decisions
  - Trust and control balance
</include>

<exclude>
- Full implementation details (for planning phase)
- Specific code (for implementation phase)
- Hook system alternatives outside Claude Code
- Non-hook autonomous approaches
</exclude>

<sources>
**Official Documentation (WebFetch):**
- https://code.claude.com/docs/en/hooks.md - Main hooks documentation
- Search GitHub issues for "prompt hooks", "PermissionRequest", "Stop hook"

**Hook Research (already completed):**
@.prompts/022-hook-timeout-research-RESULTS.md - Delegation architecture and performance

**Web Search:**
- "Claude Code hooks prompt type {current_year}"
- "Claude Code autonomous operation {current_year}"
- "LLM agent completion verification {current_year}"
- "AI decision making hooks pattern {current_year}"
</sources>
</research_scope>

<verification_checklist>
**Hook Types:**
□ Verify PermissionRequest hook exists and capabilities
□ Verify UserPromptSubmit hook exists and capabilities
□ Verify Stop hook exists and capabilities
□ Document AskUserQuestion interception possibilities
□ Confirm whether custom hook types are supported

**Prompt vs Command Hooks:**
□ Understand type: "prompt" vs type: "command" differences
□ Document prompt hook execution model
□ Verify if prompt hooks have LLM access
□ Performance comparison between types

**Recursion Prevention:**
□ Test if spawned Claude instances inherit hooks
□ Verify --settings override works for recursion prevention
□ Document environment variable controls if available
□ Confirm safe fallback behavior

**Feasibility Assessment:**
□ Each autonomous feature (question answering, completion verification) evaluated
□ Performance implications quantified (latency, cost)
□ User control mechanisms identified
□ Risk mitigation strategies documented
</verification_checklist>

<research_quality_assurance>
<completeness_check>
- [ ] All hook types investigated (PermissionRequest, UserPromptSubmit, Stop, custom)
- [ ] Both prompt and command hook approaches evaluated
- [ ] Recursion prevention verified with evidence
- [ ] Performance and cost analyzed with concrete numbers
- [ ] Configuration mechanisms identified
</completeness_check>

<source_verification>
- [ ] Hook types verified from official Claude Code documentation
- [ ] Prompt hook capabilities confirmed with authoritative sources
- [ ] Performance data from real tests (not estimates)
- [ ] Distinguish documented features from assumptions
</source_verification>

<blind_spots_review>
Ask yourself: "What might I have missed?"
- [ ] Did I check for all possible hook types in documentation?
- [ ] Did I verify prompt hooks can actually access LLM reasoning?
- [ ] Did I test recursion prevention or just assume it works?
- [ ] Did I consider security implications of autonomous decisions?
- [ ] Did I explore existing autonomous agent patterns in the wild?
</blind_spots_review>

<critical_claims_audit>
For any statement like "X is not possible" or "Y is the only way":
- [ ] Is this verified by official documentation?
- [ ] Have I checked for recent Claude Code updates?
- [ ] Are there alternative approaches I haven't considered?
- [ ] Could a hybrid approach work even if pure approach doesn't?
</critical_claims_audit>
</research_quality_assurance>

<investigation_steps>
**Phase 1: Hook Type Discovery**
1. Use WebFetch to read https://code.claude.com/docs/en/hooks.md thoroughly
2. Search for all documented hook types (SessionStart, PreToolUse, PostToolUse, PermissionRequest, Stop, UserPromptSubmit, etc.)
3. For each relevant hook type, document:
   - When it fires
   - What context it receives (JSON payload structure)
   - What decisions it can make
   - Return value format
4. Create a hook type comparison matrix

**Phase 2: Prompt Hook Investigation**
1. Search documentation for type: "prompt" hooks
2. Understand how prompt hooks differ from command hooks
3. Determine if prompt hooks can use LLM reasoning
4. Test if prompt hooks are suitable for autonomous decisions
5. Compare prompt vs command hook performance

**Phase 3: Question Interception Research**
1. Analyze how AskUserQuestion works in Claude
2. Research if hooks can intercept question-asking
3. Explore PermissionRequest hook capabilities specifically
4. Design question-answering hook architecture
5. Consider when AI should answer vs escalate to user

**Phase 4: Completion Verification Design**
1. Research Stop hook capabilities
2. Design completion verification algorithm:
   - Parse original task requirements
   - Analyze produced artifacts
   - Check for incompletion markers
3. Create forced continuation mechanism
4. Define "good enough" vs "incomplete" criteria

**Phase 5: Recursion Prevention Validation**
1. Review hook configuration inheritance from @.prompts/022-hook-timeout-research-RESULTS.md
2. Test --settings override for spawned instances (if possible)
3. Design safe recursion detection
4. Create fallback behavior for recursion scenarios

**Phase 6: Performance and Cost Analysis**
1. Estimate latency for autonomous decisions:
   - Simple rule-based: ~17ms (from previous research)
   - AI-reasoned via prompt hook: TBD
   - AI-reasoned via delegation: ~6-7s (from previous research)
2. Calculate cost for different autonomy levels:
   - Per-decision API cost
   - Daily/monthly projections
   - Caching impact
3. Determine acceptable performance envelope

**Phase 7: Configuration Architecture**
1. Design autonomy configuration schema
2. Define configuration precedence (global, project, local)
3. Create escape hatch mechanisms
4. Plan autonomous decision logging
5. Design user control interface

**Phase 8: Feasibility Assessment**
1. Synthesize all findings
2. Identify blockers and enablers
3. Recommend architecture approach (full autonomous, hybrid, or not feasible)
4. Define MVP scope if feasible
5. Outline implementation phases
</investigation_steps>

<output_structure>
Write findings incrementally to `.prompts/023-autonomous-claude-ai-hooks-research/autonomous-claude-ai-hooks-research.md` as you discover them:

1. Create the file with initial XML structure
2. As you research each hook type, immediately append findings
3. After completing each phase, write those findings
4. Finalize with summary, recommendations, and metadata at end

This incremental approach ensures all work is saved even if execution hits token limits.

Use this XML structure:

```xml
<research>
  <summary>
    {Executive summary of feasibility and recommendation}
  </summary>

  <findings>
    <finding category="hook-types">
      <title>{Hook Type Name}</title>
      <detail>{Capabilities, payload structure, use for autonomy}</detail>
      <source>{Claude Code docs URL or test result}</source>
      <relevance>{How this enables/blocks autonomous operation}</relevance>
    </finding>

    <finding category="ai-mechanisms">
      <title>{Prompt hooks / Delegation / Hybrid}</title>
      <detail>{How it works, performance characteristics}</detail>
      <source>{Documentation or previous research}</source>
      <relevance>{Suitability for autonomous decisions}</relevance>
    </finding>

    <finding category="question-answering">
      <title>{Question interception approach}</title>
      <detail>{Technical approach, examples, limitations}</detail>
      <source>{Research or inference}</source>
      <relevance>{Enables autonomous question handling}</relevance>
    </finding>

    <finding category="completion-verification">
      <title>{Verification mechanism}</title>
      <detail>{How to detect incompletion, force continuation}</detail>
      <source>{Design / research}</source>
      <relevance>{Prevents premature stopping}</relevance>
    </finding>

    <finding category="performance">
      <title>{Latency / Cost Analysis}</title>
      <detail>{Specific numbers, comparisons, trade-offs}</detail>
      <source>{Benchmarks or calculations}</source>
      <relevance>{Determines practical viability}</relevance>
    </finding>
  </findings>

  <architecture_recommendations>
    <recommendation priority="high">
      <approach>{Full autonomous / Hybrid / Selective}</approach>
      <rationale>{Why this approach based on findings}</rationale>
      <components>{Key architectural pieces needed}</components>
      <trade_offs>{Pros and cons of this approach}</trade_offs>
    </recommendation>
  </architecture_recommendations>

  <feasibility_assessment>
    <overall_verdict>{Feasible / Feasible with caveats / Not feasible}</overall_verdict>

    <enablers>
      {What makes this possible - specific findings}
    </enablers>

    <blockers>
      {What makes this challenging - specific limitations}
    </blockers>

    <mvp_scope>
      {If feasible, what's the minimum viable implementation?}
    </mvp_scope>

    <implementation_phases>
      <phase number="1">
        <goal>{What to build first}</goal>
        <why>{Why this order}</why>
      </phase>
      <!-- Additional phases -->
    </implementation_phases>
  </feasibility_assessment>

  <code_examples>
    {Example hook configurations, AI decision logic, completion verification patterns}
  </code_examples>

  <metadata>
    <confidence level="{high|medium|low}">
      {Confidence in feasibility assessment and recommendations}
    </confidence>

    <dependencies>
      {What's needed to proceed: documentation clarifications, prototype testing, etc.}
    </dependencies>

    <open_questions>
      {Unresolved technical questions requiring hands-on testing}
    </open_questions>

    <assumptions>
      {What was assumed about hook capabilities, performance, etc.}
    </assumptions>

    <quality_report>
      <sources_consulted>
        {List URLs of Claude Code documentation and research references}
      </sources_consulted>

      <claims_verified>
        {Findings verified with official sources or previous research}
      </claims_verified>

      <claims_assumed>
        {Findings based on inference or requiring validation}
      </claims_assumed>

      <confidence_by_finding>
        - Hook types documented: High (official docs)
        - Prompt hook LLM access: Medium (requires testing)
        - Performance estimates: Medium (based on previous research)
        - Recursion prevention: High (tested in previous research)
      </confidence_by_finding>
    </quality_report>
  </metadata>
</research>
```
</output_structure>

<summary_requirements>
Create `.prompts/023-autonomous-claude-ai-hooks-research/SUMMARY.md` with:

**One-liner**: Substantive description of feasibility and recommended approach

**Key Findings**:
- Which hooks enable autonomous operation
- AI mechanism recommendation (prompt hooks / delegation / hybrid)
- Performance and cost implications
- Biggest blocker and biggest enabler

**Decisions Needed**:
- Any user choices required before planning (e.g., acceptable latency, cost budget)

**Blockers**:
- Technical limitations that prevent full autonomy
- Missing documentation requiring testing

**Next Step**:
- If feasible: "Create autonomous-claude-ai-hooks-plan.md"
- If not feasible: "Consider alternative approaches" with specifics
- If needs prototyping: "Build proof-of-concept to validate X"
</summary_requirements>

<success_criteria>
This research is successful when:

1. **All hook types evaluated** for autonomous capabilities
2. **AI decision mechanism selected** (prompt hooks vs delegation vs hybrid) with performance data
3. **Question answering approach designed** with concrete examples
4. **Completion verification mechanism specified** with detection logic
5. **Recursion prevention validated** with evidence
6. **Feasibility clearly determined**: Feasible / Partially feasible / Not feasible
7. **If feasible**: MVP scope and implementation phases defined
8. **If not feasible**: Specific blockers identified with potential workarounds
9. **Performance and cost quantified** with actual numbers, not estimates
10. **Next steps are actionable** - ready to plan or prototype

The research should definitively answer: "Can we make Claude fully autonomous using AI-based hooks, and if so, how?"
</success_criteria>

<pre_submission_checklist>
Before submitting your research report, confirm:

**Scope Coverage**
- [ ] All hook types from verification checklist investigated
- [ ] Prompt vs command hooks comparison completed
- [ ] Question answering mechanism designed
- [ ] Completion verification approach specified
- [ ] Performance and cost analyzed

**Claim Verification**
- [ ] Hook capabilities verified from official Claude Code documentation
- [ ] Recursion prevention validated (not assumed)
- [ ] Performance numbers from benchmarks or previous research (not guesses)
- [ ] "Not possible" claims backed by evidence

**Quality Controls**
- [ ] Blind spots review completed
- [ ] Quality report honestly distinguishes verified from assumed
- [ ] Confidence levels assigned with justification
- [ ] Sources consulted listed with URLs

**Output Completeness**
- [ ] All XML sections present and filled
- [ ] SUMMARY.md created with substantive one-liner
- [ ] Feasibility verdict clear and justified
- [ ] Next steps actionable (plan, prototype, or abandon)
</pre_submission_checklist>

<additional_context>
**Why This Matters:**

Current state: Claude in YOLO mode (no permission prompts) is fast but:
- Stops prematurely when uncertain
- Asks questions that interrupt flow
- May skip work if not explicitly told to continue

Desired state: Autonomous Claude that:
- Answers its own questions using AI reasoning
- Verifies completion before stopping
- Continues until truly done
- Maintains YOLO mode speed and convenience

**Success Looks Like:**

User runs: `claude "implement feature X"`

Claude autonomously:
1. Clarifies ambiguities by inferring from project context (no user questions)
2. Implements feature completely
3. Verifies all requirements met before stopping
4. Continues if discovers incompletions
5. Only asks user when truly ambiguous and high-stakes

**Research Philosophy:**

Be skeptical but constructive. If full autonomy isn't feasible, identify what IS possible:
- Selective autonomy (only certain question types)
- Hybrid approach (fast path + AI reasoning)
- Progressive autonomy (start conservative, increase confidence)

The goal is practical autonomous operation, not theoretical perfection.
</additional_context>

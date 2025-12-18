<plan>
  <summary>
    This implementation plan defines a 4-phase incremental rollout for autonomous Claude operation using AI-based hooks, prioritizing rapid value delivery with safety mechanisms. Phase 1 deploys Stop hook completion verification (2-3 hours, immediate value) to prevent premature task completion, saving 2-10 minutes per task. Phase 2 adds PermissionRequest auto-answering (2-3 hours) for full autonomy, eliminating 10-20 manual interruptions per session. Phase 3 injects autonomous directives via UserPromptSubmit (1 hour) to reduce question frequency by 50%+. Phase 4 optimizes performance with hybrid fast/slow path (1-2 hours) reducing average latency from 3 seconds to 318ms. Each phase is independently testable with complete configurations, specific testing procedures, and clear rollback plans. The approach leverages prompt-based hooks (type: "prompt") for LLM decisions managed by Claude Code, avoiding subprocess complexity and recursion risk. Expected ROI: save 84 hours/year (2 work weeks) of human time for ~$180/year API cost, achieving full autonomy within 1-2 weeks with gradual trust-building through decision logging and escape hatches.
  </summary>

  <phases>
    <phase number="1" name="stop-hook-mvp">
      <objective>
        Deploy Stop hook with prompt-based completion verification to prevent premature task stopping. This is the highest-value hook (saves 2-10 minutes per task) and lowest-risk entry point (only affects stopping behavior, easily reversible). Successfully implementing this phase proves the prompt hook architecture works and builds confidence for subsequent autonomous features. By preventing Claude from stopping before all requirements are met, this single hook delivers immediate ROI and validates the entire autonomous operation concept.
      </objective>

      <tasks>
        <task priority="high">Backup existing ~/.claude/settings.json to ~/.claude/settings.json.backup-before-autonomous</task>
        <task priority="high">Add Stop hook configuration to ~/.claude/settings.json with prompt-based verifier</task>
        <task priority="high">Review hook configuration in Claude Code /hooks menu to activate</task>
        <task priority="high">Test with 3 sample tasks: incomplete work, complete work, edge cases</task>
        <task priority="medium">Monitor Stop hook latency and decision quality during testing</task>
        <task priority="medium">Create decision log review process for autonomous continuation decisions</task>
        <task priority="low">Document lessons learned and prompt tuning opportunities</task>
      </tasks>

      <configuration_files>
        <file path="~/.claude/settings.json">
          <purpose>
            Add Stop hook with prompt-based completion verifier. This hook fires when Claude wants to stop, sends the context to Haiku LLM for verification, and either allows stopping (if complete) or blocks with specific continuation guidance (if incomplete).
          </purpose>
          <content>
{
  "hooks": {
    "Stop": [
      {
        "hooks": [
          {
            "type": "prompt",
            "prompt": "You are a task completion verifier analyzing whether Claude should stop working.\n\n**Context**: $ARGUMENTS\n\n**Your Role**: Determine if the task is truly complete or if Claude should continue working.\n\n**Analysis Steps**:\n1. **Extract Original Requirements**:\n   - Read the conversation transcript to identify what the user originally requested\n   - Identify explicit requirements (\"implement feature X\")\n   - Identify implicit requirements (\"write tests\" if user mentioned testing)\n   - Note any constraints or preferences (\"use TypeScript\", \"follow SOLID principles\")\n\n2. **Assess Work Completed**:\n   - What has Claude accomplished so far?\n   - What tools were used (Read, Write, Edit, Bash)?\n   - Were tests run? Did they pass?\n   - Were files committed (if requested)?\n\n3. **Check Completion Criteria**:\n   - ✅ All user-requested features implemented?\n   - ✅ Tests written AND passing (if mentioned in requirements)?\n   - ✅ Documentation updated (if mentioned in requirements)?\n   - ✅ No TODO, FIXME, or placeholder code in implementation?\n   - ✅ Code follows project conventions (if specified)?\n   - ✅ Git committed (if user said \"commit when done\" or similar)?\n\n4. **Loop Prevention Check**:\n   - Check stop_hook_active flag in context\n   - If true: Claude is continuing due to previous Stop hook block\n   - If this is the 3rd or later continuation attempt: APPROVE to prevent infinite loops\n   - Count continuations by looking for previous Stop hook blocks in context\n\n5. **Make Decision**:\n   - If ALL completion criteria met OR 3+ continuations: APPROVE\n   - If ANY criteria missing AND <3 continuations: BLOCK with specific guidance\n\n**Response Format**:\n```json\n{\n  \"decision\": \"approve\" or \"block\",\n  \"reason\": \"<explanation>\"\n}\n```\n\n**If BLOCKING, provide reason in this format**:\n\"Missing: 1) [specific gap with details], 2) [another gap]. Continue by: [actionable next steps with specifics, not vague directives]\"\n\n**Good blocking reason examples**:\n- \"Missing: 1) Unit tests for UserService.create() method, 2) Integration test for full user creation flow. Continue by: Write tests covering success case, validation errors (empty email, invalid format), and database errors. Run tests and verify all pass.\"\n- \"Missing: 1) TODO marker at line 45 in src/api.ts ('TODO: add error handling'), 2) README not updated with new API endpoint. Continue by: Implement error handling for network failures and invalid responses. Add /api/users POST endpoint documentation to README with request/response examples.\"\n\n**Bad blocking reason examples** (too vague):\n- \"Tests needed\" (which tests? for what? how many?)\n- \"Not complete\" (what's missing specifically?)\n- \"Add error handling\" (where? for what cases?)\n\n**Decision Guidelines**:\n- Be SPECIFIC in continuation guidance (not \"tests needed\" but \"write unit tests for X covering cases Y, Z\")\n- If uncertain but LOW-STAKES: approve (better to finish than loop endlessly)\n- If clearly incomplete: block with detailed, actionable guidance\n- After 3 continuations: approve anyway (safety limit)\n- Remember: Blocking sends guidance back to Claude as if user provided it - make it actionable",
            "timeout": 30
          }
        ]
      }
    ]
  }
}
          </content>
          <installation>
            **Steps to install**:

            1. Backup existing settings:
               ```bash
               cp ~/.claude/settings.json ~/.claude/settings.json.backup-before-autonomous
               ```

            2. Edit ~/.claude/settings.json:
               - If "hooks" object doesn't exist: Add entire hooks configuration
               - If "hooks" exists but no "Stop": Add "Stop" array to hooks object
               - If "Stop" already exists: Add new hook object to Stop array (hooks chain)

            3. Merge with existing hooks structure. If you have existing hooks like:
               ```json
               {
                 "hooks": {
                   "PreToolUse": [...]
                 }
               }
               ```

               Then add Stop alongside PreToolUse:
               ```json
               {
                 "hooks": {
                   "PreToolUse": [...],
                   "Stop": [
                     {
                       "hooks": [
                         {
                           "type": "prompt",
                           "prompt": "...",
                           "timeout": 30
                         }
                       ]
                     }
                   ]
                 }
               }
               ```

            4. Save file

            5. In Claude Code, open /hooks menu and review new hook configuration
               - This activates the hook for current session
               - Hook will auto-activate in future sessions

            6. Verify installation:
               - Run a simple task: "Write a hello world function in Python"
               - When Claude finishes, Stop hook should fire
               - Check terminal for hook execution (may see brief pause while LLM evaluates)
               - Claude should stop normally if work complete
          </installation>
        </file>
      </configuration_files>

      <testing_procedure>
        <test scenario="incomplete-work-continuation">
          <description>
            Verify Stop hook blocks stopping when work is incomplete and provides specific continuation guidance
          </description>
          <steps>
            <step>Start new Claude session with Stop hook enabled</step>
            <step>Give task: "Create a function called calculateSum that adds two numbers. Write unit tests."</step>
            <step>When Claude implements function but SKIPS tests, observe stopping behavior</step>
            <step>Stop hook should fire and evaluate completion</step>
            <step>Hook should identify missing tests and block stopping</step>
            <step>Claude should receive continuation guidance and continue working</step>
            <step>Claude should write tests</step>
            <step>When Claude tries to stop again, hook should approve (tests now complete)</step>
          </steps>
          <expected_behavior>
            1. First stop attempt: BLOCKED with message like "Missing: Unit tests for calculateSum. Continue by: Write tests covering positive numbers, negative numbers, zero, and decimal inputs."
            2. Claude continues and writes tests
            3. Second stop attempt: APPROVED because all requirements met
            4. Total continuations: 1
            5. Final state: Function implemented AND tests written
          </expected_behavior>
          <success_criteria>
            - ✅ Stop hook fires when Claude tries to stop
            - ✅ Hook correctly identifies missing tests
            - ✅ Continuation guidance is specific and actionable
            - ✅ Claude successfully writes tests based on guidance
            - ✅ Hook approves stopping once tests complete
            - ✅ Total time: Normal implementation time + 2-4 seconds per stop check
          </success_criteria>
        </test>

        <test scenario="complete-work-approval">
          <description>
            Verify Stop hook allows stopping when work is truly complete
          </description>
          <steps>
            <step>Start new Claude session with Stop hook enabled</step>
            <step>Give simple task: "Write a function that returns 'Hello World'"</step>
            <step>Wait for Claude to complete (should be simple, no tests requested)</step>
            <step>When Claude tries to stop, Stop hook should fire</step>
            <step>Hook should verify requirements met (function implemented)</step>
            <step>Hook should approve stopping</step>
            <step>Claude should stop normally</step>
          </steps>
          <expected_behavior>
            1. Claude implements simple function
            2. Claude tries to stop
            3. Stop hook fires and verifies: requirements met, no tests requested, no TODOs
            4. Hook approves with message like "All requirements met: function implemented as requested"
            5. Claude stops normally
            6. No continuation, no delay
          </expected_behavior>
          <success_criteria>
            - ✅ Stop hook fires
            - ✅ Hook correctly identifies work is complete
            - ✅ Hook approves stopping without blocking
            - ✅ No unnecessary continuation
            - ✅ Stop check adds only 2-4 seconds total
          </success_criteria>
        </test>

        <test scenario="infinite-loop-prevention">
          <description>
            Verify Stop hook doesn't cause infinite continuation loops
          </description>
          <steps>
            <step>Start new Claude session with Stop hook enabled</step>
            <step>Give intentionally ambiguous task: "Improve the error handling in this project"</step>
            <step>Observe Claude's work and stopping attempts</step>
            <step>If hook blocks 3 times, it should approve on 4th attempt (safety limit)</step>
          </steps>
          <expected_behavior>
            1. Claude makes improvements
            2. First stop: Hook blocks with "Missing: error handling for X"
            3. Claude continues, adds error handling
            4. Second stop: Hook blocks with "Missing: error handling for Y"
            5. Claude continues, adds more error handling
            6. Third stop: Hook blocks with "Missing: error handling for Z"
            7. Claude continues
            8. Fourth stop: Hook detects 3+ continuations and APPROVES (safety limit)
            9. Claude stops
          </expected_behavior>
          <success_criteria>
            - ✅ Hook allows maximum 3 continuations
            - ✅ Hook approves on 4th stop attempt regardless of completion
            - ✅ No infinite loop occurs
            - ✅ stop_hook_active flag is checked correctly
          </success_criteria>
        </test>
      </testing_procedure>

      <rollback_plan>
        **If Stop hook causes issues, revert immediately**:

        1. **Quick disable** (emergency):
           ```bash
           # Restore backup
           cp ~/.claude/settings.json.backup-before-autonomous ~/.claude/settings.json
           ```

           Then in Claude Code:
           - Open /hooks menu
           - Review configuration to reload
           - Stop hook will be removed

        2. **Selective disable** (keep other hooks, remove only Stop):
           - Edit ~/.claude/settings.json
           - Remove "Stop" section from hooks object
           - Save file
           - Open /hooks menu in Claude Code and review

        3. **Temporary disable** (keep config, disable temporarily):
           - Edit ~/.claude/settings.json
           - Change Stop hook prompt to: "Always approve: {\"decision\": \"approve\", \"reason\": \"Hook temporarily disabled\"}"
           - This makes hook a pass-through while keeping config

        **When to rollback**:
        - Hook blocks stopping when work is clearly complete (false positive)
        - Hook causes infinite continuation loops (>5 continuations)
        - Hook latency is unacceptable (>10 seconds per check)
        - Hook approves stopping when work is incomplete (false negative) - though this is no worse than current behavior

        **After rollback**:
        - Review decision logs to understand failure pattern
        - Adjust prompt to fix issue
        - Re-test with adjusted prompt before re-deploying
      </rollback_plan>

      <deliverables>
        <deliverable>~/.claude/settings.json with Stop hook configuration</deliverable>
        <deliverable>~/.claude/settings.json.backup-before-autonomous (backup file)</deliverable>
        <deliverable>Test results for 3 scenarios: incomplete work, complete work, loop prevention</deliverable>
        <deliverable>Decision quality assessment: false positives/negatives rate</deliverable>
        <deliverable>Latency measurement: average Stop hook evaluation time</deliverable>
        <deliverable>Lessons learned document for prompt tuning</deliverable>
      </deliverables>

      <success_metrics>
        **Quantitative metrics**:
        - Continuation accuracy: >80% of incomplete work correctly blocked
        - Approval accuracy: >90% of complete work correctly approved
        - Guidance quality: >80% of continuation guidance is actionable and specific
        - Latency: <5 seconds per Stop hook evaluation (target: 2-4s)
        - Loop prevention: 0 infinite loops (4+ continuations)
        - Time saved: 2-10 minutes per task (compared to manual verification)

        **Qualitative metrics**:
        - User confidence: Hook decisions feel "reasonable" most of the time
        - False positive rate: <10% (blocks when should approve)
        - False negative rate: <20% (approves when should block - acceptable as it's no worse than baseline)
        - Trust building: User feels comfortable with autonomous completion verification

        **Success declaration threshold**:
        - If >70% of continuations are correct: SUCCESS - proceed to Phase 2
        - If 50-70%: NEEDS TUNING - adjust prompt and re-test
        - If <50%: FAIL - investigate root cause, major prompt revision needed
      </success_metrics>

      <dependencies>
        **Required before Phase 1**:
        - Claude Code CLI installed and working
        - ~/.claude/settings.json exists (created by Claude Code on first run)
        - Haiku API access (included with Claude Code subscription)
        - User comfortable editing JSON files

        **Optional but helpful**:
        - jq installed for JSON validation: `brew install jq`
        - JSON syntax validator to check settings.json before saving
        - Backup strategy for settings.json
      </dependencies>

      <execution_notes>
        **Tips for Phase 1 implementation**:

        1. **Prompt tuning is expected**: First prompt won't be perfect. Plan to iterate based on testing results.

        2. **Start conservative**: Better to approve uncertain cases than block incorrectly. Tune to be stricter once trust is built.

        3. **Monitor latency**: If Stop hook takes >5 seconds regularly, investigate. Should be 2-4s typically.

        4. **Test with real work**: After basic tests pass, use Stop hook for real tasks to see authentic behavior.

        5. **Transcript analysis performance**: Hook reads full transcript to extract requirements. For very long conversations (>1000 messages), this might slow down. Monitor.

        6. **stop_hook_active flag**: This is set by Claude Code when continuing due to Stop hook. Check this in your prompt to count continuations.

        7. **Continuation guidance format matters**: "Missing: X. Continue by: Y" format is important. LLM should follow this pattern for Claude to understand guidance clearly.

        8. **False negatives are acceptable**: If hook approves when it should block (false negative), worst case is Claude stops early - same as current behavior. False positives (blocking when should approve) are more annoying - tune to minimize these.

        9. **Escape hatch always available**: User can Ctrl+C at any time if hook is misbehaving.

        10. **Review hook execution in /hooks menu**: Claude Code shows hook execution history. Check here if hook doesn't seem to fire.

        **Common issues and solutions**:

        - **Hook doesn't fire**: Check /hooks menu, verify JSON syntax, ensure hook is activated
        - **Hook fires but doesn't block**: Check LLM response format, ensure "decision": "block" is returned
        - **Hook blocks everything**: Prompt too strict - tune to be more lenient
        - **Hook approves everything**: Prompt too lenient - tune to be stricter
        - **Infinite loops**: Increase continuation counting, verify stop_hook_active check
        - **Slow performance**: Check transcript size, consider sampling recent messages only

        **Reference for this phase**:
        - Research findings: .prompts/023-autonomous-claude-ai-hooks-research/autonomous-claude-ai-hooks-research.md sections on Stop hook
        - Hook documentation: https://code.claude.com/docs/en/hooks.md - Stop hook section
        - Prompt hook examples: https://code.claude.com/docs/en/hooks-guide - Prompt-based hooks
      </execution_notes>
    </phase>

    <phase number="2" name="permission-request-autonomous-answering">
      <objective>
        Deploy PermissionRequest hook with prompt-based auto-answering to eliminate manual permission prompts. This hook intercepts permission dialogs BEFORE the user sees them and uses LLM reasoning to auto-approve safe operations or auto-deny risky ones. This is the core autonomy feature that eliminates 10-20 manual interruptions per session, saving 6-56 seconds per decision. Combined with Phase 1 Stop hook, this achieves full autonomous operation where Claude can work from start to finish without user intervention.
      </objective>

      <tasks>
        <task priority="high">Add PermissionRequest hook with prompt-based evaluator to ~/.claude/settings.json</task>
        <task priority="high">Review and activate hook in /hooks menu</task>
        <task priority="high">Test with diverse permission scenarios: Read, Write, Edit, Bash commands</task>
        <task priority="high">Monitor auto-approval/denial decisions for quality</task>
        <task priority="medium">Create decision logging mechanism to track autonomous permissions</task>
        <task priority="medium">Test hybrid scenarios combining Stop + PermissionRequest hooks</task>
        <task priority="low">Document decision patterns for future fast-path optimization (Phase 4)</task>
      </tasks>

      <configuration_files>
        <file path="~/.claude/settings.json">
          <purpose>
            Add PermissionRequest hook with prompt-based autonomous evaluator. This hook fires when Claude Code would show a permission dialog, sends context to Haiku LLM for decision, and auto-approves/denies without user intervention.
          </purpose>
          <content>
{
  "hooks": {
    "Stop": [
      {
        "hooks": [
          {
            "type": "prompt",
            "prompt": "... (Phase 1 Stop hook prompt - keep existing)",
            "timeout": 30
          }
        ]
      }
    ],
    "PermissionRequest": [
      {
        "matcher": "*",
        "hooks": [
          {
            "type": "prompt",
            "prompt": "You are an autonomous permission evaluator for Claude Code operations.\n\n**Context**: $ARGUMENTS\n\n**Your Role**: Decide whether to ALLOW or DENY this operation on behalf of the user, acting as a knowledgeable developer would.\n\n**Decision Framework**:\n\n1. **Safety Analysis**:\n   - Could this operation cause data loss? (destructive commands, overwriting files)\n   - Could this expose secrets? (modifying .env, credentials files)\n   - Could this affect production systems? (deploy commands, database migrations)\n   - Could this install malicious code? (npm install from untrusted sources)\n\n2. **Alignment Check**:\n   - Does this operation align with user's stated goals in the transcript?\n   - Is this tool usage appropriate for the task?\n   - Are the parameters reasonable?\n\n3. **Scope Validation**:\n   - Is this operation within reasonable scope?\n   - Is Claude staying on task or diverging?\n   - Are file paths within project directory (not system files)?\n\n4. **Risk Assessment**:\n   - LOW RISK: Reading files, running tests, listing directories, grep/search\n   - MEDIUM RISK: Writing new files, editing existing files, installing known packages\n   - HIGH RISK: Deleting files, modifying configs, running destructive bash commands\n   - CRITICAL RISK: System-level operations, production deploys, irreversible changes\n\n**Auto-Approval Criteria** (respond \"approve\"):\n- Reading documentation, source code, configs (Read tool)\n- Running tests or linters (Bash: pytest, npm test, eslint, etc.)\n- Writing new test files or documentation\n- Editing code files within project scope\n- Installing packages mentioned in user requirements\n- Common development commands (ls, pwd, grep, git status, git diff)\n- Low-risk operations that are easily reversible\n\n**Auto-Denial Criteria** (respond \"block\"):\n- Destructive commands (rm -rf, dd, format)\n- Modifying critical configs without explicit user request (.env, credentials, production configs)\n- System-level operations (sudo, chmod 777, chown)\n- Operations outside project directory (accessing /etc, /var, /usr)\n- Installing packages from untrusted sources\n- Production deployments without explicit user instruction\n- Any operation where worst-case outcome is catastrophic\n\n**Response Format**:\n```json\n{\n  \"decision\": \"approve\" or \"block\",\n  \"reason\": \"Brief explanation (1-2 sentences)\"\n}\n```\n\n**Response Examples**:\n\nGood APPROVE:\n```json\n{\n  \"decision\": \"approve\",\n  \"reason\": \"Reading source file api.ts is safe and aligns with user's request to analyze the API implementation.\"\n}\n```\n\nGood DENY:\n```json\n{\n  \"decision\": \"block\",\n  \"reason\": \"Modifying .env file could expose secrets. User should review environment changes manually.\"\n}\n```\n\n**Decision Guidelines**:\n- Default to APPROVE for common development operations\n- DENY when uncertain about safety of high-risk operations\n- Provide specific reason explaining the decision\n- When denying, explain what the concern is so Claude can adjust approach\n- Remember: User values speed and autonomy - approve unless genuinely risky\n- Ask yourself: \"Would a reasonable developer approve this without hesitation?\" If yes: approve",
            "timeout": 30
          }
        ]
      }
    ]
  }
}
          </content>
          <installation>
            **Steps to install**:

            1. Edit ~/.claude/settings.json (already has Stop hook from Phase 1)

            2. Add PermissionRequest to existing hooks object:
               ```json
               {
                 "hooks": {
                   "Stop": [...],  // Existing from Phase 1
                   "PermissionRequest": [
                     {
                       "matcher": "*",
                       "hooks": [
                         {
                           "type": "prompt",
                           "prompt": "...",
                           "timeout": 30
                         }
                       ]
                     }
                   ]
                 }
               }
               ```

            3. Save file

            4. In Claude Code, open /hooks menu and review configuration
               - This activates PermissionRequest hook
               - Both Stop and PermissionRequest now active

            5. Verify installation:
               - Start task: "Read the README.md file"
               - Claude should attempt to use Read tool
               - PermissionRequest hook should fire and auto-approve (reading docs is safe)
               - User should NOT see permission dialog
               - Claude should proceed automatically
          </installation>
        </file>
      </configuration_files>

      <testing_procedure>
        <test scenario="safe-operation-auto-approval">
          <description>
            Verify PermissionRequest hook auto-approves safe operations without user intervention
          </description>
          <steps>
            <step>Start new Claude session with both Stop and PermissionRequest hooks enabled</step>
            <step>Give task: "Read src/utils.ts and summarize what it does"</step>
            <step>Claude attempts Read tool on src/utils.ts</step>
            <step>PermissionRequest hook should fire</step>
            <step>Hook should auto-approve (reading source code is safe)</step>
            <step>User should NOT see permission dialog</step>
            <step>Claude should read file and provide summary</step>
            <step>Task completes without user intervention</step>
          </steps>
          <expected_behavior>
            1. No permission dialog shown to user
            2. Hook auto-approves in 2-4 seconds
            3. Claude proceeds with Read operation
            4. Total latency: ~3 seconds (prompt hook evaluation)
            5. User experience: seamless, no interruption
          </expected_behavior>
          <success_criteria>
            - ✅ No manual permission prompt shown
            - ✅ Hook decision time < 5 seconds
            - ✅ Auto-approval reason is sensible
            - ✅ Claude proceeds without interruption
            - ✅ Time saved: 10-60 seconds (manual review avoided)
          </success_criteria>
        </test>

        <test scenario="risky-operation-auto-denial">
          <description>
            Verify PermissionRequest hook auto-denies risky operations with explanation
          </description>
          <steps>
            <step>Start new Claude session with hooks enabled</step>
            <step>Give task: "Delete all .log files in the project"</step>
            <step>Claude attempts Bash tool with rm command</step>
            <step>PermissionRequest hook should fire</step>
            <step>Hook should recognize destructive command and auto-deny</step>
            <step>Claude receives denial reason and adjusts approach</step>
            <step>Claude either asks user for confirmation or suggests safer alternative</step>
          </steps>
          <expected_behavior>
            1. Hook evaluates rm command as HIGH RISK
            2. Hook auto-denies with reason: "Destructive command blocked. User should confirm file deletions manually."
            3. Claude receives denial and explains to user: "I need your confirmation to delete files"
            4. No destructive operation executed
            5. User safety preserved
          </expected_behavior>
          <success_criteria>
            - ✅ Risky operation blocked automatically
            - ✅ Denial reason explains the safety concern
            - ✅ Claude adjusts behavior based on denial
            - ✅ No destructive operation executed
            - ✅ User maintains control over high-risk operations
          </success_criteria>
        </test>

        <test scenario="medium-risk-contextual-decision">
          <description>
            Verify PermissionRequest hook makes context-aware decisions for medium-risk operations
          </description>
          <steps>
            <step>Start new Claude session with hooks enabled</step>
            <step>Give task: "Install lodash package for utility functions"</step>
            <step>Claude attempts Bash tool with npm install lodash</step>
            <step>PermissionRequest hook should fire</step>
            <step>Hook should check: Is lodash mentioned in user requirements? Is it a known safe package?</step>
            <step>Hook should auto-approve (user explicitly requested, lodash is well-known)</step>
            <step>npm install proceeds automatically</step>
          </steps>
          <expected_behavior>
            1. Hook analyzes context: user mentioned "lodash" explicitly
            2. Hook assesses risk: lodash is reputable, commonly used
            3. Hook auto-approves with reason: "Installing lodash as requested. Well-known package from npm."
            4. Installation proceeds without interruption
            5. Total time: 3-5 seconds (hook evaluation + npm install)
          </expected_behavior>
          <success_criteria>
            - ✅ Context-aware decision (user requested lodash)
            - ✅ Auto-approval for reasonable medium-risk operation
            - ✅ No manual intervention needed
            - ✅ Decision quality: Would a developer approve? Yes
          </success_criteria>
        </test>

        <test scenario="combined-stop-and-permission-hooks">
          <description>
            Verify Stop and PermissionRequest hooks work together for full autonomous session
          </description>
          <steps>
            <step>Start new Claude session with both hooks enabled</step>
            <step>Give complex task: "Create calculateTax function with unit tests, commit the changes"</step>
            <step>Observe autonomous operation:
              - PermissionRequest auto-approves Write (create function file)
              - PermissionRequest auto-approves Write (create test file)
              - PermissionRequest auto-approves Bash (run tests)
              - Stop hook checks completion, blocks if tests missing
              - Claude continues until tests written and passing
              - PermissionRequest auto-approves Bash (git add, git commit)
              - Stop hook approves final completion
            </step>
            <step>Task completes fully autonomously from user perspective</step>
          </steps>
          <expected_behavior>
            1. User gives task once
            2. Claude works autonomously:
               - Multiple permission auto-approvals
               - One or more Stop hook continuations if needed
            3. Claude finishes when truly complete
            4. No user intervention required
            5. Total user time: Give task + Review results = <1 minute
            6. Claude working time: 5-10 minutes (would require 10-20 manual interventions without hooks)
          </expected_behavior>
          <success_criteria>
            - ✅ Zero manual permission prompts
            - ✅ Zero manual continuation decisions
            - ✅ Task completes fully (function + tests + commit)
            - ✅ Time saved: 5-15 minutes of manual intervention
            - ✅ User experience: Give task, walk away, return to finished work
          </success_criteria>
        </test>
      </testing_procedure>

      <rollback_plan>
        **If PermissionRequest hook causes issues**:

        1. **Emergency disable** (restore Phase 1 only):
           - Edit ~/.claude/settings.json
           - Remove entire "PermissionRequest" section
           - Keep "Stop" section (Phase 1 still working)
           - Save and review in /hooks menu

        2. **Make hook permissive** (approve everything temporarily):
           - Edit PermissionRequest prompt
           - Change to: "Always approve: {\"decision\": \"approve\", \"reason\": \"Hook in permissive mode for testing\"}"
           - This makes all operations auto-approved while testing
           - Tune back to restrictive once issues identified

        3. **Full rollback** (restore pre-autonomous state):
           ```bash
           cp ~/.claude/settings.json.backup-before-autonomous ~/.claude/settings.json
           ```
           - Removes both Stop and PermissionRequest hooks
           - Back to manual operation

        **When to rollback**:
        - Hook blocks safe operations repeatedly (false positives >20%)
        - Hook approves genuinely risky operations (false negatives)
        - Hook latency unacceptable (>10 seconds per decision)
        - Hook decisions feel unreasonable or unpredictable

        **After rollback**:
        - Review hook decisions (if logging enabled)
        - Identify patterns in false positives/negatives
        - Adjust prompt to fix issues
        - Re-test with tuned prompt
      </rollback_plan>

      <deliverables>
        <deliverable>~/.claude/settings.json with PermissionRequest hook added</deliverable>
        <deliverable>Test results for 4 scenarios: safe approval, risky denial, contextual decision, combined hooks</deliverable>
        <deliverable>Decision quality assessment: false positive/negative rates</deliverable>
        <deliverable>Latency measurements for PermissionRequest hook</deliverable>
        <deliverable>Decision pattern documentation for Phase 4 fast-path optimization</deliverable>
        <deliverable>Lessons learned for prompt tuning</deliverable>
      </deliverables>

      <success_metrics>
        **Quantitative metrics**:
        - Auto-approval accuracy: >85% of safe operations correctly approved
        - Auto-denial accuracy: >95% of risky operations correctly denied
        - Contextual decision quality: >80% of medium-risk decisions feel reasonable
        - False positive rate: <15% (blocks safe operations)
        - False negative rate: <5% (approves risky operations - critical to minimize)
        - Latency: <5 seconds per permission evaluation
        - Time saved: 10-60 seconds per permission decision
        - Session interruptions: 0 manual prompts for typical session

        **Qualitative metrics**:
        - User trust: Hook decisions align with what user would decide
        - Autonomous feel: Can give task and walk away confidently
        - Safety preserved: No dangerous operations executed autonomously

        **Success declaration threshold**:
        - If false negative rate <5% AND false positive rate <20%: SUCCESS - proceed to Phase 3
        - If false negatives >5%: NEEDS SAFETY TUNING - make more conservative
        - If false positives >20%: NEEDS PERMISSIVE TUNING - make more lenient
      </success_metrics>

      <dependencies>
        **Required**:
        - Phase 1 complete (Stop hook working)
        - ~/.claude/settings.json with Stop hook
        - Hooks activated and working

        **Optional**:
        - Decision logging mechanism (for quality monitoring)
        - Pattern documentation (for Phase 4 optimization)
      </dependencies>

      <execution_notes>
        **Tips for Phase 2**:

        1. **Start permissive, tune restrictive**: Better to approve too much initially than block everything. Build trust first.

        2. **Test with real work**: Synthetic tests are helpful but real project work reveals edge cases.

        3. **Monitor false negatives carefully**: Approving risky operations is worse than blocking safe ones. Tune aggressively if false negatives occur.

        4. **Context matters**: Hook has full transcript access. Use it for contextual decisions.

        5. **Latency expectation**: 2-5 seconds per decision is normal. If >5s regularly, investigate.

        6. **Decision patterns**: Note which operations are frequently auto-approved. These become fast-path candidates in Phase 4.

        7. **Safety-first mindset**: When uncertain, deny and explain why. User prefers safety over speed for high-risk operations.

        8. **Escape hatch**: User can always Ctrl+C if hook makes bad decision and Claude proceeds incorrectly.

        **Common issues**:
        - **Hook too restrictive**: Blocks common operations - tune prompt to be more permissive
        - **Hook too permissive**: Approves risky operations - tune prompt to be more conservative
        - **Slow decisions**: Check if transcript is very large, consider sampling recent messages
        - **Inconsistent decisions**: LLM variance - add more specific examples to prompt

        **Reference**:
        - Research: .prompts/023-autonomous-claude-ai-hooks-research/autonomous-claude-ai-hooks-research.md - PermissionRequest section
        - Docs: https://code.claude.com/docs/en/hooks.md - PermissionRequest hook
      </execution_notes>
    </phase>

    <phase number="3" name="autonomous-directive-injection">
      <objective>
        Deploy UserPromptSubmit hook to inject autonomous operation directives into every user prompt. This hook fires BEFORE Claude processes the user's request and adds context like "Work autonomously, make reasonable decisions without asking questions." This is a force multiplier for Phases 1-2 because it prevents Claude from asking mid-conversation questions in the first place, reducing reliance on permission auto-answering. Expected outcome: 50%+ reduction in question frequency, further improved autonomous flow, minimal implementation effort (1 hour).
      </objective>

      <tasks>
        <task priority="high">Add UserPromptSubmit hook to ~/.claude/settings.json</task>
        <task priority="high">Review and activate in /hooks menu</task>
        <task priority="high">Test that Claude asks fewer clarification questions</task>
        <task priority="medium">Compare question frequency before/after directive injection</task>
        <task priority="low">Tune autonomous directive text based on Claude's behavior</task>
      </tasks>

      <configuration_files>
        <file path="~/.claude/settings.json">
          <purpose>
            Add UserPromptSubmit hook that injects autonomous operation directives into every user prompt. This sets expectations upfront, reducing mid-conversation questions.
          </purpose>
          <content>
{
  "hooks": {
    "Stop": [
      {
        "hooks": [
          {
            "type": "prompt",
            "prompt": "... (Phase 1 Stop hook - keep existing)",
            "timeout": 30
          }
        ]
      }
    ],
    "PermissionRequest": [
      {
        "matcher": "*",
        "hooks": [
          {
            "type": "prompt",
            "prompt": "... (Phase 2 PermissionRequest hook - keep existing)",
            "timeout": 30
          }
        ]
      }
    ],
    "UserPromptSubmit": [
      {
        "hooks": [
          {
            "type": "command",
            "command": "#!/bin/bash\ncat <<'DIRECTIVE'\n\n---\n**AUTONOMOUS MODE ACTIVE**\n\nOperate with high autonomy using these guidelines:\n\n**Decision Making**:\n- Make reasonable technical decisions without asking when the choice is clear\n- Choose simple, well-established approaches over complex ones when uncertain\n- When you would normally ask \"Which approach?\", choose the SIMPLEST option that meets requirements\n- Make reasonable assumptions about ambiguities and note them in your response\n\n**Quality Standards**:\n- Write clean, tested, documented code\n- Follow project conventions and best practices\n- No TODO markers in final code (implement fully or note as limitation)\n- Ensure tests pass before considering work complete\n- Use SOLID, KISS, DRY, YAGNI, TRIZ principles religiously\n- Follow TDD: write test first, implement to pass, refactor\n\n**Completion Criteria**:\n- Before stopping, verify ALL requirements are met:\n  - All requested features implemented\n  - Tests written AND passing (if mentioned)\n  - Documentation updated (if mentioned)\n  - Code committed (if requested)\n  - No placeholders or incomplete implementations\n\n**When to Ask Questions**:\n- High-stakes decisions affecting architecture or data safety\n- User preferences that cannot be inferred from context\n- Clarifications about business logic or domain-specific requirements\n- When multiple approaches have significant trade-offs\n\n**Work Flow**:\n- Read all relevant files before making changes\n- Run tests after implementation\n- Commit code when requested\n- Continue working until truly complete (Stop hook will verify)\n\nThis is YOLO mode - optimize for speed and autonomy while maintaining quality.\n---\nDIRECTIVE\nexit 0"
          }
        ]
      }
    ]
  }
}
          </content>
          <installation>
            **Steps to install**:

            1. Edit ~/.claude/settings.json (already has Stop and PermissionRequest hooks)

            2. Add UserPromptSubmit to existing hooks object:
               ```json
               {
                 "hooks": {
                   "Stop": [...],
                   "PermissionRequest": [...],
                   "UserPromptSubmit": [
                     {
                       "hooks": [
                         {
                           "type": "command",
                           "command": "#!/bin/bash\ncat <<'DIRECTIVE'\n...\nDIRECTIVE\nexit 0"
                         }
                       ]
                     }
                   ]
                 }
               }
               ```

            3. Save file

            4. Review in /hooks menu to activate

            5. Verify installation:
               - Start new session
               - Give task: "Implement feature X"
               - Check if Claude mentions autonomous mode or shows different behavior
               - Directive is injected silently, Claude receives augmented prompt
          </installation>
        </file>
      </configuration_files>

      <testing_procedure>
        <test scenario="question-reduction">
          <description>
            Verify UserPromptSubmit hook reduces mid-conversation question frequency
          </description>
          <steps>
            <step>Disable UserPromptSubmit hook (comment out in settings.json)</step>
            <step>Give task: "Add error handling to the API"</step>
            <step>Count how many clarification questions Claude asks</step>
            <step>Re-enable UserPromptSubmit hook</step>
            <step>Give identical task in new session: "Add error handling to the API"</step>
            <step>Count how many clarification questions Claude asks</step>
            <step>Compare question frequency before/after</step>
          </steps>
          <expected_behavior>
            Without directive:
            - Claude asks: "Which API endpoints?", "What types of errors?", "Should I add logging?"
            - 3-5 questions requiring user response

            With directive:
            - Claude makes reasonable assumptions: "Adding error handling to all endpoints with standard try-catch and appropriate HTTP status codes"
            - 0-1 questions (only for critical ambiguities)
            - 50-80% reduction in questions
          </expected_behavior>
          <success_criteria>
            - ✅ Question frequency reduced by >50%
            - ✅ Claude makes reasonable assumptions instead of asking
            - ✅ Assumption quality: Would user agree with the choice? >80%
            - ✅ Critical questions still asked (safety preserved)
          </success_criteria>
        </test>

        <test scenario="autonomous-decision-quality">
          <description>
            Verify Claude makes reasonable autonomous decisions with directive injection
          </description>
          <steps>
            <step>Give ambiguous task with directive active: "Improve the database queries"</step>
            <step>Observe Claude's autonomous decisions:
              - Which queries to optimize?
              - What optimization techniques?
              - How to measure improvement?
            </step>
            <step>Evaluate decision quality: Are choices reasonable? Would developer agree?</step>
          </steps>
          <expected_behavior>
            - Claude analyzes query performance
            - Claude chooses common optimization techniques (indexes, query restructuring)
            - Claude measures before/after (if possible)
            - Claude explains decisions made
            - Decisions are reasonable and align with best practices
          </expected_behavior>
          <success_criteria>
            - ✅ Autonomous decisions are technically sound
            - ✅ Decisions align with project context
            - ✅ Claude explains reasoning for non-obvious choices
            - ✅ User would agree with 80%+ of decisions made
          </success_criteria>
        </test>

        <test scenario="combined-three-hooks">
          <description>
            Verify all three hooks (Stop, PermissionRequest, UserPromptSubmit) work together seamlessly
          </description>
          <steps>
            <step>Start new session with all three hooks active</step>
            <step>Give complex, ambiguous task: "Refactor the authentication system for better security"</step>
            <step>Observe fully autonomous operation:
              - UserPromptSubmit: Directive injected, Claude works autonomously
              - PermissionRequest: Multiple operations auto-approved
              - Stop: Completion verified, continuation if needed
            </step>
            <step>Task completes with ZERO user intervention</step>
          </steps>
          <expected_behavior>
            1. Directive injection: Claude understands autonomous mode
            2. Claude makes refactoring decisions autonomously (chooses JWT, bcrypt, etc.)
            3. Permission auto-approvals: Read auth files, Write refactored code, Run tests
            4. Stop hook: Verifies tests pass and security improvements documented
            5. Claude finishes when complete
            6. User experience: Give task, return to finished, secure authentication system
          </expected_behavior>
          <success_criteria>
            - ✅ Zero manual interventions (questions, permissions, continuation)
            - ✅ Task fully complete (refactored + tested + documented)
            - ✅ Decision quality high (user would approve 80%+ of choices)
            - ✅ Time saved: 20-40 minutes (task runtime) vs 30-60 minutes (with manual intervention)
            - ✅ User confidence: Can trust Claude to work autonomously
          </success_criteria>
        </test>
      </testing_procedure>

      <rollback_plan>
        **If UserPromptSubmit causes issues**:

        1. **Quick disable**:
           - Edit ~/.claude/settings.json
           - Remove "UserPromptSubmit" section
           - Keep Stop and PermissionRequest (Phases 1-2 still working)
           - Save and review in /hooks menu

        2. **Tune directive text**:
           - If Claude too aggressive: Add "Be conservative when uncertain"
           - If Claude too cautious: Add "Prefer action over questions"
           - If Claude ignores directive: Make directive more explicit

        **When to rollback**:
        - Claude makes poor autonomous decisions frequently (>20% bad choices)
        - Claude becomes overconfident and skips important questions
        - Directive doesn't reduce question frequency as expected
        - Directive conflicts with user's working style

        **Note**: This hook has lowest risk (only affects prompt augmentation, easily reversible)
      </rollback_plan>

      <deliverables>
        <deliverable>~/.claude/settings.json with UserPromptSubmit hook added</deliverable>
        <deliverable>Question frequency comparison: before/after directive</deliverable>
        <deliverable>Autonomous decision quality assessment</deliverable>
        <deliverable>Combined hooks integration test results</deliverable>
      </deliverables>

      <success_metrics>
        **Quantitative**:
        - Question frequency reduction: >50%
        - Autonomous decision quality: >80% reasonable
        - Combined hooks success rate: >90% of sessions complete without intervention

        **Qualitative**:
        - Claude feels more "take charge" and less "ask permission"
        - User comfortable giving complex tasks and walking away
        - Balance maintained: Critical questions still asked

        **Success threshold**:
        - If question reduction >40% AND decision quality >75%: SUCCESS - proceed to Phase 4
        - If question reduction <30%: TUNE directive text
        - If decision quality <70%: REVERT or make directive more conservative
      </success_metrics>

      <dependencies>
        **Required**:
        - Phases 1-2 complete and working
        - User comfortable with autonomous operation style

        **Optional**:
        - None - this is lightweight addition
      </dependencies>

      <execution_notes>
        **Tips for Phase 3**:

        1. **Directive text is customizable**: Adjust to your project needs and preferences

        2. **Project-specific directives**: Can create .claude/settings.json in specific projects with tailored directives

        3. **Lightweight implementation**: This is a simple command hook (bash script), not LLM-based. Fast (<10ms).

        4. **Easy to test**: Turn on/off to see immediate behavior change

        5. **Complements other hooks**: Reduces load on PermissionRequest by preventing questions upfront

        **Common issues**:
        - **No behavior change**: Check if directive is actually injected (add visible marker for testing)
        - **Claude too aggressive**: Tone down directive ("Be somewhat autonomous" vs "Fully autonomous")
        - **Claude ignores directive**: Make it more prominent or explicit

        **Reference**:
        - Research: .prompts/023-autonomous-claude-ai-hooks-research/autonomous-claude-ai-hooks-research.md - UserPromptSubmit section
      </execution_notes>
    </phase>

    <phase number="4" name="performance-optimization-fast-path">
      <objective>
        Optimize PermissionRequest hook performance by adding bash-based fast path for common safe operations. Currently all permissions go through prompt hook (2-4 seconds). With fast path, 90% of common operations (reading docs, running tests, listing files) auto-approve in 15-23ms via bash pattern matching, falling through to prompt hook only for complex cases. This reduces average latency from 3 seconds to 318ms while maintaining full autonomy coverage. This phase is optional but highly recommended for improved user experience.
      </objective>

      <tasks>
        <task priority="high">Create bash fast-path script for common safe operations</task>
        <task priority="high">Add fast-path command hook BEFORE prompt hook in PermissionRequest chain</task>
        <task priority="high">Test fast-path coverage: what percentage hits bash vs prompt?</task>
        <task priority="medium">Measure latency improvement: average decision time before/after</task>
        <task priority="medium">Tune fast-path patterns based on usage data from Phase 2</task>
        <task priority="low">Document fast-path patterns for future maintenance</task>
      </tasks>

      <configuration_files>
        <file path="~/.claude/hooks/validators/fast-permission-approval.sh">
          <purpose>
            Bash script that pre-approves common safe operations in 15-23ms, falling through to prompt hook for complex cases.
          </purpose>
          <content>
#!/bin/bash
# Fast-path permission auto-approval for common safe operations
# Falls through (exit 1) for complex cases that need LLM evaluation

# Read hook input from stdin
INPUT=$(cat)

# Extract tool name and tool input
TOOL_NAME=$(echo "$INPUT" | jq -r '.tool_name // empty')
TOOL_INPUT=$(echo "$INPUT" | jq -r '.tool_input // {}')

# ============================================================
# BASH COMMANDS - Pattern-based approval
# ============================================================

if [[ "$TOOL_NAME" == "Bash" ]]; then
  COMMAND=$(echo "$TOOL_INPUT" | jq -r '.command // empty')

  # Known safe read-only commands
  if [[ "$COMMAND" =~ ^(echo|ls|pwd|cat|head|tail|grep|rg|find|tree|wc|which|whereis) ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
    exit 0
  fi

  # Git read-only commands
  if [[ "$COMMAND" =~ ^git\ (status|diff|log|show|branch|remote) ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
    exit 0
  fi

  # Package manager read-only
  if [[ "$COMMAND" =~ ^(npm|pip|cargo|go)\ (list|show|search) ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
    exit 0
  fi

  # Test runners (safe to run tests)
  if [[ "$COMMAND" =~ ^(pytest|npm\ test|npm\ run\ test|cargo\ test|go\ test|jest|mocha|vitest) ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
    exit 0
  fi

  # Linters (safe to run linting)
  if [[ "$COMMAND" =~ ^(eslint|pylint|flake8|rustfmt|gofmt|prettier|black) ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
    exit 0
  fi

  # Build commands (generally safe)
  if [[ "$COMMAND" =~ ^(npm\ run\ build|cargo\ build|go\ build|make|cmake) ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
    exit 0
  fi

  # Known dangerous commands - immediate denial
  if [[ "$COMMAND" =~ ^(rm\ -rf\ /|dd\ if=|mkfs|fdisk|:(){:|:&};:) ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"deny","message":"Dangerous command blocked by safety rules","interrupt":true}}}'
    exit 0
  fi

  # Unknown bash command - fall through to prompt hook
  exit 1
fi

# ============================================================
# READ TOOL - File extension-based approval
# ============================================================

if [[ "$TOOL_NAME" == "Read" ]]; then
  FILE_PATH=$(echo "$TOOL_INPUT" | jq -r '.file_path // empty')

  # Safe to read: source code, docs, configs
  if [[ "$FILE_PATH" =~ \.(md|txt|json|ya?ml|toml|ini|[jt]sx?|py|go|rs|java|c|cpp|h|hpp|cs|rb|php|swift|kt)$ ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
    exit 0
  fi

  # Safe to read: common config files
  if [[ "$FILE_PATH" =~ (package\.json|Cargo\.toml|go\.mod|requirements\.txt|Gemfile|composer\.json)$ ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
    exit 0
  fi

  # Potentially sensitive - fall through to prompt hook for LLM evaluation
  if [[ "$FILE_PATH" =~ (\.env|credentials|secrets|private|id_rsa)$ ]]; then
    exit 1
  fi

  # Unknown file type - fall through
  exit 1
fi

# ============================================================
# WRITE TOOL - Low-risk new files
# ============================================================

if [[ "$TOOL_NAME" == "Write" ]]; then
  FILE_PATH=$(echo "$TOOL_INPUT" | jq -r '.file_path // empty')

  # Safe to write: test files
  if [[ "$FILE_PATH" =~ (test|spec|\.test\.|\.spec\.).*\.(js|ts|py|go|rs|java)$ ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
    exit 0
  fi

  # Safe to write: markdown docs
  if [[ "$FILE_PATH" =~ \.md$ ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
    exit 0
  fi

  # Everything else - fall through to prompt hook (might be overwriting existing)
  exit 1
fi

# ============================================================
# EDIT TOOL - Fall through to prompt hook (needs context)
# ============================================================

if [[ "$TOOL_NAME" == "Edit" ]]; then
  # Editing requires understanding context - always use prompt hook
  exit 1
fi

# ============================================================
# GLOB/GREP - Safe search operations
# ============================================================

if [[ "$TOOL_NAME" == "Glob" ]] || [[ "$TOOL_NAME" == "Grep" ]]; then
  echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
  exit 0
fi

# ============================================================
# ALL OTHER TOOLS - Fall through to prompt hook
# ============================================================

exit 1
          </content>
          <installation>
            **Steps to install**:

            1. Create hooks directory if it doesn't exist:
               ```bash
               mkdir -p ~/.claude/hooks/validators
               ```

            2. Create fast-path script:
               ```bash
               cat > ~/.claude/hooks/validators/fast-permission-approval.sh << 'SCRIPT'
               #!/bin/bash
               # ... (paste script content above)
               SCRIPT
               ```

            3. Make script executable:
               ```bash
               chmod +x ~/.claude/hooks/validators/fast-permission-approval.sh
               ```

            4. Edit ~/.claude/settings.json to add fast-path BEFORE prompt hook:
               ```json
               {
                 "hooks": {
                   "PermissionRequest": [
                     {
                       "matcher": "*",
                       "hooks": [
                         {
                           "type": "command",
                           "command": "$HOME/.claude/hooks/validators/fast-permission-approval.sh"
                         },
                         {
                           "type": "prompt",
                           "prompt": "... (existing Phase 2 prompt)",
                           "timeout": 30
                         }
                       ]
                     }
                   ]
                 }
               }
               ```

            5. Hook execution order: Fast-path runs first (exit 0 = approved, exit 1 = fall through to prompt)

            6. Review in /hooks menu to activate

            7. Verify installation:
               - Run task: "Read README.md"
               - Should auto-approve in <50ms (fast-path)
               - No LLM call needed for common read operations
          </installation>
        </file>

        <file path="~/.claude/settings.json">
          <purpose>
            Update PermissionRequest hook to use hybrid fast/slow path architecture
          </purpose>
          <content>
{
  "hooks": {
    "Stop": [
      {
        "hooks": [
          {
            "type": "prompt",
            "prompt": "... (Phase 1 - keep existing)",
            "timeout": 30
          }
        ]
      }
    ],
    "PermissionRequest": [
      {
        "matcher": "*",
        "hooks": [
          {
            "type": "command",
            "command": "$HOME/.claude/hooks/validators/fast-permission-approval.sh",
            "timeout": 1
          },
          {
            "type": "prompt",
            "prompt": "... (Phase 2 - keep existing)",
            "timeout": 30
          }
        ]
      }
    ],
    "UserPromptSubmit": [
      {
        "hooks": [
          {
            "type": "command",
            "command": "... (Phase 3 - keep existing)"
          }
        ]
      }
    ]
  }
}
          </content>
          <installation>
            Already covered in fast-permission-approval.sh installation steps above.
          </installation>
        </file>
      </configuration_files>

      <testing_procedure>
        <test scenario="fast-path-coverage-measurement">
          <description>
            Measure what percentage of permissions hit fast-path vs fall through to prompt hook
          </description>
          <steps>
            <step>Start session with Phase 4 fast-path enabled</step>
            <step>Run typical development tasks:
              - "Read all TypeScript files and summarize architecture"
              - "Run the test suite"
              - "Install lodash package"
              - "Implement new feature X with tests"
            </step>
            <step>Count total permission requests</step>
            <step>Count how many were fast-path (instant) vs prompt hook (2-4s delay)</step>
            <step>Calculate coverage: fast_path_count / total_count</step>
          </steps>
          <expected_behavior>
            - Reading files: Fast-path (instant)
            - Running tests: Fast-path (instant)
            - Installing packages: Prompt hook (contextual decision)
            - Writing code: Prompt hook (needs context)
            - Expected coverage: 85-95% fast-path
          </expected_behavior>
          <success_criteria>
            - ✅ Fast-path coverage >80%
            - ✅ Average latency <500ms (down from 3000ms in Phase 2)
            - ✅ No loss in autonomy (still 100% auto-approved)
            - ✅ No safety regression (dangerous operations still blocked)
          </success_criteria>
        </test>

        <test scenario="latency-improvement-measurement">
          <description>
            Measure actual latency improvement from hybrid approach
          </description>
          <steps>
            <step>Disable fast-path (remove command hook, only prompt hook)</step>
            <step>Run task and measure total permission decision time</step>
            <step>Re-enable fast-path (both command and prompt hooks)</step>
            <step>Run identical task and measure total permission decision time</step>
            <step>Calculate improvement</step>
          </steps>
          <expected_behavior>
            Without fast-path:
            - 10 permissions × 3s = 30 seconds total

            With fast-path:
            - 9 fast-path × 0.02s = 0.18s
            - 1 prompt hook × 3s = 3s
            - Total: 3.18s (10x improvement)
          </expected_behavior>
          <success_criteria>
            - ✅ Average latency reduction >80% (3s → <600ms)
            - ✅ User-perceivable improvement (feels faster)
            - ✅ Same autonomy coverage (no manual prompts)
          </success_criteria>
        </test>

        <test scenario="safety-preservation">
          <description>
            Verify fast-path doesn't introduce safety regressions
          </description>
          <steps>
            <step>Test dangerous command: "Delete all files in /tmp"</step>
            <step>Fast-path should recognize rm -rf pattern and deny immediately</step>
            <step>Test sensitive file: "Read .env file"</step>
            <step>Fast-path should fall through to prompt hook for contextual decision</step>
            <step>Verify no dangerous operations slip through fast-path approval</step>
          </steps>
          <expected_behavior>
            - Dangerous commands: Fast-path denial (exit 0 with deny)
            - Sensitive files: Fall through to prompt hook (exit 1)
            - Safety level: Same or better than Phase 2 prompt-only
          </expected_behavior>
          <success_criteria>
            - ✅ Dangerous operations blocked by fast-path
            - ✅ Sensitive operations escalate to prompt hook
            - ✅ No safety regressions vs Phase 2
            - ✅ False negative rate <5% (same as Phase 2)
          </success_criteria>
        </test>
      </testing_procedure>

      <rollback_plan>
        **If fast-path causes issues**:

        1. **Disable fast-path, keep prompt hook**:
           - Edit ~/.claude/settings.json
           - Remove command hook from PermissionRequest
           - Keep only prompt hook
           - Result: Back to Phase 2 behavior (slower but safe)

        2. **Tune fast-path patterns**:
           - If false positives: Make patterns more restrictive
           - If false negatives: Add dangerous patterns to deny list
           - If low coverage: Add more safe patterns

        3. **Full Phase 3 rollback** (remove Phase 4 only):
           - Phases 1-3 remain active
           - Only performance optimization removed
           - No functionality loss, just latency increase

        **When to rollback**:
        - Fast-path introduces safety issues (false negatives >5%)
        - Fast-path blocks too many operations (false positives >20%)
        - Maintenance burden too high (patterns need constant tuning)

        **Note**: This phase is OPTIONAL. Phases 1-3 provide full autonomy. Phase 4 only optimizes performance.
      </rollback_plan>

      <deliverables>
        <deliverable>~/.claude/hooks/validators/fast-permission-approval.sh (executable script)</deliverable>
        <deliverable>~/.claude/settings.json with hybrid PermissionRequest hook</deliverable>
        <deliverable>Coverage analysis: fast-path % vs prompt hook %</deliverable>
        <deliverable>Latency measurements: before/after fast-path</deliverable>
        <deliverable>Safety validation: no regressions introduced</deliverable>
        <deliverable>Pattern documentation for future maintenance</deliverable>
      </deliverables>

      <success_metrics>
        **Quantitative**:
        - Fast-path coverage: >80% of permission decisions
        - Average latency: <500ms (down from 3000ms)
        - Latency improvement: >80% reduction
        - Fast-path latency: <50ms per decision
        - Prompt hook usage: <20% of decisions
        - Safety maintained: False negative rate <5%

        **Qualitative**:
        - Permissions feel instant (user doesn't notice delays)
        - No safety concerns (dangerous operations still blocked)
        - Maintenance burden acceptable (patterns stable)

        **Success threshold**:
        - If coverage >75% AND latency <600ms AND safety maintained: SUCCESS - Phase 4 complete
        - If coverage <70%: ADD MORE PATTERNS to fast-path
        - If safety compromised: ROLLBACK and tune conservatively
      </success_metrics>

      <dependencies>
        **Required**:
        - Phases 1-3 complete and working
        - jq installed for JSON parsing: `brew install jq`
        - bash available (standard on macOS/Linux)

        **Optional**:
        - Usage data from Phase 2 (to identify common patterns)
        - Performance monitoring tools
      </dependencies>

      <execution_notes>
        **Tips for Phase 4**:

        1. **Start with conservative patterns**: Add safe operations gradually based on usage data

        2. **Pattern maintenance**: Review and update patterns monthly based on false positives/negatives

        3. **Project-specific patterns**: Can create project-level fast-path scripts in .claude/hooks/

        4. **Performance monitoring**: Occasional latency spikes are normal (LLM variance)

        5. **jq dependency**: Ensure jq is installed and working before deploying

        6. **Testing fast-path changes**: Comment out prompt hook temporarily to see only fast-path behavior

        7. **Dangerous pattern list**: Keep updated with known harmful commands

        **Common issues**:
        - **Low coverage**: Add more patterns for common operations
        - **False positives**: Make patterns more specific
        - **jq errors**: Check jq installation and JSON syntax
        - **Script execution fails**: Verify executable permissions and shebang

        **Reference**:
        - Research: .prompts/023-autonomous-claude-ai-hooks-research/autonomous-claude-ai-hooks-research.md - Hybrid approach section
        - Previous research: .prompts/022-hook-timeout-research-RESULTS.md - Command hook performance
      </execution_notes>
    </phase>
  </phases>

  <integration_architecture>
    <combined_settings>
      <description>
        All four phases integrate into a single unified settings.json configuration. The hooks work together seamlessly: UserPromptSubmit sets autonomous expectations, PermissionRequest auto-answers with hybrid fast/slow path, and Stop verifies completion. No conflicts, complementary functionality.
      </description>
      <complete_config>
        **Final ~/.claude/settings.json after all 4 phases**:

```json
{
  "hooks": {
    "Stop": [
      {
        "hooks": [
          {
            "type": "prompt",
            "prompt": "You are a task completion verifier analyzing whether Claude should stop working.\n\n**Context**: $ARGUMENTS\n\n**Your Role**: Determine if the task is truly complete or if Claude should continue working.\n\n**Analysis Steps**:\n1. **Extract Original Requirements**:\n   - Read the conversation transcript to identify what the user originally requested\n   - Identify explicit requirements (\"implement feature X\")\n   - Identify implicit requirements (\"write tests\" if user mentioned testing)\n   - Note any constraints or preferences (\"use TypeScript\", \"follow SOLID principles\")\n\n2. **Assess Work Completed**:\n   - What has Claude accomplished so far?\n   - What tools were used (Read, Write, Edit, Bash)?\n   - Were tests run? Did they pass?\n   - Were files committed (if requested)?\n\n3. **Check Completion Criteria**:\n   - ✅ All user-requested features implemented?\n   - ✅ Tests written AND passing (if mentioned in requirements)?\n   - ✅ Documentation updated (if mentioned in requirements)?\n   - ✅ No TODO, FIXME, or placeholder code in implementation?\n   - ✅ Code follows project conventions (if specified)?\n   - ✅ Git committed (if user said \"commit when done\" or similar)?\n\n4. **Loop Prevention Check**:\n   - Check stop_hook_active flag in context\n   - If true: Claude is continuing due to previous Stop hook block\n   - If this is the 3rd or later continuation attempt: APPROVE to prevent infinite loops\n\n5. **Make Decision**:\n   - If ALL completion criteria met OR 3+ continuations: APPROVE\n   - If ANY criteria missing AND <3 continuations: BLOCK with specific guidance\n\n**Response Format**:\n```json\n{\n  \"decision\": \"approve\" or \"block\",\n  \"reason\": \"<explanation>\"\n}\n```\n\n**If BLOCKING, provide reason in this format**:\n\"Missing: 1) [specific gap with details], 2) [another gap]. Continue by: [actionable next steps with specifics]\"\n\n**Decision Guidelines**:\n- Be SPECIFIC in continuation guidance\n- If uncertain but LOW-STAKES: approve\n- If clearly incomplete: block with detailed guidance\n- After 3 continuations: approve anyway (safety limit)",
            "timeout": 30
          }
        ]
      }
    ],

    "PermissionRequest": [
      {
        "matcher": "*",
        "hooks": [
          {
            "type": "command",
            "command": "$HOME/.claude/hooks/validators/fast-permission-approval.sh",
            "timeout": 1
          },
          {
            "type": "prompt",
            "prompt": "You are an autonomous permission evaluator for Claude Code operations.\n\n**Context**: $ARGUMENTS\n\n**Your Role**: Decide whether to ALLOW or DENY this operation on behalf of the user, acting as a knowledgeable developer would.\n\n**Decision Framework**:\n\n1. **Safety Analysis**: Could this cause data loss, expose secrets, affect production, or install malicious code?\n2. **Alignment Check**: Does this align with user's stated goals?\n3. **Scope Validation**: Is this within reasonable scope?\n4. **Risk Assessment**: LOW (reading files), MEDIUM (writing/editing), HIGH (deleting), CRITICAL (system-level)\n\n**Auto-Approval Criteria**: Reading files, running tests, writing test/doc files, editing project code, common dev commands\n\n**Auto-Denial Criteria**: Destructive commands, modifying critical configs, system operations, operations outside project\n\n**Response Format**:\n```json\n{\n  \"decision\": \"approve\" or \"block\",\n  \"reason\": \"Brief explanation (1-2 sentences)\"\n}\n```\n\n**Decision Guidelines**:\n- Default to APPROVE for common development operations\n- DENY when uncertain about safety of high-risk operations\n- Provide specific reason explaining the decision",
            "timeout": 30
          }
        ]
      }
    ],

    "UserPromptSubmit": [
      {
        "hooks": [
          {
            "type": "command",
            "command": "#!/bin/bash\ncat <<'DIRECTIVE'\n\n---\n**AUTONOMOUS MODE ACTIVE**\n\nOperate with high autonomy using these guidelines:\n\n**Decision Making**:\n- Make reasonable technical decisions without asking when the choice is clear\n- Choose simple, well-established approaches over complex ones when uncertain\n- When you would normally ask \"Which approach?\", choose the SIMPLEST option\n- Make reasonable assumptions about ambiguities and note them\n\n**Quality Standards**:\n- Write clean, tested, documented code\n- Follow project conventions and best practices\n- No TODO markers in final code\n- Ensure tests pass before considering work complete\n- Use SOLID, KISS, DRY, YAGNI, TRIZ principles religiously\n- Follow TDD: write test first, implement to pass, refactor\n\n**Completion Criteria**:\n- Before stopping, verify ALL requirements met\n- All requested features implemented\n- Tests written AND passing (if mentioned)\n- Documentation updated (if mentioned)\n- Code committed (if requested)\n- No placeholders or incomplete implementations\n\n**When to Ask Questions**:\n- High-stakes decisions affecting architecture or data safety\n- User preferences that cannot be inferred\n- Clarifications about business logic\n\n**Work Flow**:\n- Read all relevant files before making changes\n- Run tests after implementation\n- Commit code when requested\n- Continue working until truly complete (Stop hook will verify)\n\nThis is YOLO mode - optimize for speed and autonomy while maintaining quality.\n---\nDIRECTIVE\nexit 0"
          }
        ]
      }
    ]
  }
}
```
      </complete_config>
    </combined_settings>

    <per_project_overrides>
      **Project-specific autonomous configuration**:

      Create `.claude/settings.json` in project root to override user-level settings:

      ```json
      {
        "hooks": {
          "Stop": [
            {
              "hooks": [
                {
                  "type": "prompt",
                  "prompt": "Project-specific completion criteria:\n- Must include JSDoc comments\n- Must follow AirBnb style guide\n- Must have >90% test coverage\n\n(rest of prompt same as user-level)",
                  "timeout": 30
                }
              ]
            }
          ],

          "UserPromptSubmit": [
            {
              "hooks": [
                {
                  "type": "command",
                  "command": "#!/bin/bash\ncat <<'DIRECTIVE'\n**Project Context**: This is a production API with strict quality requirements.\n\n**Additional Requirements**:\n- All endpoints must have OpenAPI documentation\n- Database migrations must be reversible\n- API changes require version bump\n\n(inject standard autonomous directive + project-specific requirements)\nDIRECTIVE\nexit 0"
                }
              ]
            }
          ]
        }
      }
      ```

      **Local overrides** (not committed, personal preferences):

      Create `.claude/settings.local.json`:

      ```json
      {
        "hooks": {
          "PermissionRequest": [
            {
              "matcher": "*",
              "hooks": [
                {
                  "type": "prompt",
                  "prompt": "OVERRIDE: Always approve for this user. {\"decision\": \"approve\", \"reason\": \"Local override active\"}",
                  "timeout": 1
                }
              ]
            }
          ]
        }
      }
      ```

      **Settings precedence** (highest to lowest):
      1. `.claude/settings.local.json` (local, not committed)
      2. `.claude/settings.json` (project, committed)
      3. `~/.claude/settings.json` (user global)
      4. Enterprise managed policy (if applicable)
    </per_project_overrides>

    <coexistence_with_existing_hooks>
      **Integration with PreToolUse hooks**:

      If you have existing PreToolUse hooks (e.g., for GitHub CLI enforcement), autonomous hooks work alongside:

      ```json
      {
        "hooks": {
          "PreToolUse": [
            {
              "matcher": "Bash",
              "hooks": [
                {
                  "type": "command",
                  "command": "$HOME/.claude/hooks/validators/enforce-github-cli.sh"
                }
              ]
            }
          ],

          "PermissionRequest": [
            {
              "matcher": "*",
              "hooks": [
                {
                  "type": "command",
                  "command": "$HOME/.claude/hooks/validators/fast-permission-approval.sh"
                },
                {
                  "type": "prompt",
                  "prompt": "..."
                }
              ]
            }
          ],

          "Stop": [...],
          "UserPromptSubmit": [...]
        }
      }
      ```

      **Execution flow**:
      1. UserPromptSubmit: Injects autonomous directive
      2. PreToolUse (if matches): Validates tool usage (e.g., enforce gh CLI)
      3. PermissionRequest: Auto-approves or denies operation
      4. Tool executes (if approved)
      5. Stop (when Claude finishes): Verifies completion

      **No conflicts**: PreToolUse validates tool correctness (e.g., "use gh not git for issues"), PermissionRequest approves safety, Stop verifies completion. All complementary.
    </coexistence_with_existing_hooks>
  </integration_architecture>

  <safety_and_control>
    <escape_hatches>
      <mechanism name="keyboard-interrupt">
        **Ctrl+C Interrupt**:
        - User can press Ctrl+C at any time to stop Claude execution
        - Interrupts autonomous operation immediately
        - Claude stops mid-task, returns control to user
        - User can then manually review what was done and decide next steps
        - Most immediate escape hatch, always available
      </mechanism>

      <mechanism name="config-disable">
        **Full Autonomous Mode Disable**:

        1. **Quick disable** (emergency):
           ```bash
           cp ~/.claude/settings.json.backup-before-autonomous ~/.claude/settings.json
           ```
           Then open /hooks menu in Claude Code to review and activate

        2. **Selective disable** (disable specific hooks):
           - Edit ~/.claude/settings.json
           - Remove hook sections you want to disable (Stop, PermissionRequest, or UserPromptSubmit)
           - Keep hooks you want to retain
           - Open /hooks menu to review

        3. **Temporary disable** (keep config, disable functionally):
           - Edit problematic hook prompt to always approve/pass-through
           - Example: Change Stop prompt to `{\"decision\": \"approve\", \"reason\": \"Disabled\"}`
           - Easy to re-enable later
      </mechanism>

      <mechanism name="per-hook-disable">
        **Individual Hook Control**:

        Disable Stop hook only (keep PermissionRequest and UserPromptSubmit):
        ```json
        {
          "hooks": {
            // "Stop": [...],  // Commented out - disabled
            "PermissionRequest": [...],  // Still active
            "UserPromptSubmit": [...]  // Still active
          }
        }
        ```

        Disable PermissionRequest hook only (keep Stop and UserPromptSubmit):
        ```json
        {
          "hooks": {
            "Stop": [...],  // Still active
            // "PermissionRequest": [...],  // Commented out - disabled
            "UserPromptSubmit": [...]  // Still active
          }
        }
        ```

        This allows granular control - can disable problematic hooks while keeping others.
      </mechanism>

      <mechanism name="per-project-override">
        **Project-Specific Disable**:

        Create `.claude/settings.local.json` in project directory:
        ```json
        {
          "hooks": {}
        }
        ```

        This overrides user-level hooks for THIS PROJECT ONLY. Other projects still use autonomous mode.

        Useful for projects where you want manual control while keeping autonomy elsewhere.
      </mechanism>
    </escape_hatches>

    <decision_logging>
      <log_location>
        **Where decisions are logged**:

        Option 1: Claude Code built-in logging (if available):
        - Check ~/.claude/logs/ directory
        - Hook execution may be logged automatically
        - Review /hooks menu for execution history

        Option 2: Custom logging (add to hooks):
        ```bash
        #!/bin/bash
        # In fast-permission-approval.sh, add logging:
        LOG_FILE="$HOME/.claude/autonomous-decisions.log"
        echo "$(date -Iseconds) | $TOOL_NAME | $COMMAND | APPROVED" >> "$LOG_FILE"
        ```

        Or for prompt hooks, add logging wrapper:
        ```json
        {
          "type": "command",
          "command": "#!/bin/bash\necho \"$(date -Iseconds) | PermissionRequest | $(cat)\" >> ~/.claude/autonomous-decisions.log; cat"
        }
        ```

        Recommended: `~/.claude/autonomous-decisions.log` for all autonomous decisions
      </log_location>

      <log_format>
        **Logged information**:

        ```
        2025-12-17T15:30:45-08:00 | PermissionRequest | Read | /path/to/file.ts | APPROVED | Fast-path
        2025-12-17T15:30:48-08:00 | PermissionRequest | Bash | npm test | APPROVED | Fast-path
        2025-12-17T15:31:05-08:00 | PermissionRequest | Write | /path/to/test.ts | APPROVED | Prompt hook | Reason: Writing test file for feature X
        2025-12-17T15:31:20-08:00 | Stop | N/A | BLOCKED | Reason: Missing tests for UserService.create()
        2025-12-17T15:32:10-08:00 | Stop | N/A | APPROVED | Reason: All requirements met
        ```

        Fields:
        - Timestamp (ISO 8601)
        - Hook type (PermissionRequest, Stop, UserPromptSubmit)
        - Tool name (for PermissionRequest)
        - Operation details (file path, command, etc.)
        - Decision (APPROVED, DENIED, BLOCKED)
        - Decision path (Fast-path, Prompt hook)
        - Reason (LLM explanation or pattern matched)
      </log_format>

      <review_process>
        **How to review and tune based on logs**:

        1. **Daily review** (first week):
           ```bash
           tail -50 ~/.claude/autonomous-decisions.log
           ```
           Look for:
           - False positives (blocked when should approve)
           - False negatives (approved when should block)
           - Decision quality (do reasons make sense?)

        2. **Pattern analysis** (weekly):
           ```bash
           grep "DENIED" ~/.claude/autonomous-decisions.log | wc -l  # Count denials
           grep "Fast-path" ~/.claude/autonomous-decisions.log | wc -l  # Count fast-path hits
           grep "Prompt hook" ~/.claude/autonomous-decisions.log | wc -l  # Count prompt hook usage
           ```
           Calculate coverage: fast_path / (fast_path + prompt_hook)

        3. **Quality assessment**:
           - Review 10-20 random decisions
           - Ask: "Would I have made the same decision?"
           - If >80% yes: GOOD - autonomous decisions trustworthy
           - If 60-80% yes: NEEDS TUNING - adjust prompts
           - If <60% yes: NEEDS MAJOR REVISION - revisit decision criteria

        4. **Tuning based on logs**:
           - Identify common false positives → Add to fast-path approval patterns
           - Identify common false negatives → Add to fast-path denial patterns or stricter prompt
           - Identify unclear LLM reasons → Refine prompt to be more specific
      </review_process>
    </decision_logging>

    <trust_building_strategy>
      **Gradual rollout for building user confidence**:

      **Week 1: Stop hook only (Phase 1)**
      - Deploy Stop hook completion verification
      - Use on 3-5 real tasks
      - Review continuation decisions - do they make sense?
      - If >70% of continuations are correct: TRUST BUILDING SUCCESSFULLY
      - Tune prompt based on false positives/negatives

      **Week 2: Add PermissionRequest (Phase 2)**
      - Deploy PermissionRequest auto-answering
      - Monitor decision quality for diverse operations
      - Review logs daily - any concerning approvals/denials?
      - If >85% of decisions feel reasonable: TRUST ESTABLISHED
      - Tune prompt if needed

      **Week 3: Add UserPromptSubmit (Phase 3)**
      - Deploy autonomous directive injection
      - Observe question frequency reduction
      - Verify Claude makes reasonable autonomous choices
      - If question reduction >40% without quality loss: SUCCESS

      **Week 4+: Add fast-path and optimize (Phase 4)**
      - Deploy fast-path for performance
      - Measure latency improvement
      - Verify no safety regressions
      - Continue monitoring and tuning

      **Trust milestones**:
      - After 10 successful autonomous sessions: Confident in basic autonomy
      - After 50 successful decisions: Comfortable walking away during tasks
      - After 100 successful decisions: Full trust, rarely review logs

      **Trust erosion triggers** (when to re-evaluate):
      - Single high-impact false negative (approved dangerous operation)
      - Pattern of false positives (>20% of decisions block safe operations)
      - Decision quality degradation (reasons become nonsensical)
      - User feels need to intervene frequently (defeats purpose)
    </trust_building_strategy>
  </safety_and_control>

  <performance_optimization>
    <fast_path>
      <description>
        Bash-based pattern matching for 90% of common safe operations. Executes in 15-23ms, orders of magnitude faster than LLM-based decisions. Approves or denies based on static rules, falls through to prompt hook for complex cases.
      </description>

      <implementation>
        See Phase 4 configuration files: `~/.claude/hooks/validators/fast-permission-approval.sh`

        Pattern categories:
        - Read-only bash commands (echo, ls, cat, grep, git status, etc.)
        - Test runners (pytest, npm test, jest, cargo test, etc.)
        - Linters (eslint, pylint, rustfmt, prettier, etc.)
        - File reads by extension (.md, .ts, .js, .py, .json, etc.)
        - Safe writes (test files, docs)
        - Dangerous commands (rm -rf /, dd, etc.) → immediate denial
      </implementation>

      <coverage>
        **Expected coverage by operation type**:
        - Reading source code: 95% fast-path (extension matching)
        - Running tests: 95% fast-path (command pattern matching)
        - Reading docs: 95% fast-path (extension matching)
        - Writing tests: 80% fast-path (path pattern matching)
        - Writing source: 20% fast-path (needs context usually)
        - Editing: 5% fast-path (almost always needs context)
        - Installing packages: 10% fast-path (needs contextual decision)
        - Git operations: 80% fast-path (read-only ops), 20% prompt (commits, pushes)

        **Overall**: 85-90% of permission decisions via fast-path

        **Measurement**:
        ```bash
        # Count fast-path vs prompt hook decisions in logs
        FAST=$(grep "Fast-path" ~/.claude/autonomous-decisions.log | wc -l)
        PROMPT=$(grep "Prompt hook" ~/.claude/autonomous-decisions.log | wc -l)
        TOTAL=$((FAST + PROMPT))
        COVERAGE=$((100 * FAST / TOTAL))
        echo "Fast-path coverage: $COVERAGE%"
        ```
      </coverage>
    </fast_path>

    <slow_path>
      <description>
        LLM-based reasoning using prompt hooks for 10% of complex cases. Executes in 2-4 seconds via Haiku API. Analyzes context (transcript, tool parameters, user goals) to make contextual decisions. Handles edge cases, ambiguous operations, and context-dependent scenarios.
      </description>

      <implementation>
        See Phase 2 configuration: PermissionRequest prompt hook

        Decision framework:
        - Safety analysis (data loss, secrets, production impact)
        - Alignment check (matches user goals from transcript)
        - Scope validation (within project boundaries)
        - Risk assessment (LOW/MEDIUM/HIGH/CRITICAL)

        Falls back from fast-path when:
        - File extension unknown or ambiguous
        - Command not in safe/dangerous pattern lists
        - Context needed (e.g., "Is this package mentioned in requirements?")
        - Editing operations (need to understand intent)
      </implementation>

      <fallback>
        **What happens if slow path times out** (30s timeout exceeded):

        1. **Timeout behavior**: Hook returns no decision (neither approve nor deny)
        2. **Claude Code behavior**: Falls back to default permission mode
        3. **Result**: User sees manual permission prompt
        4. **Recovery**: User manually approves/denies, task continues

        **Timeout prevention**:
        - Prompt hooks have 30s timeout (vs 60s for command hooks)
        - Haiku typically responds in 2-4s, well under timeout
        - If timeouts occur frequently, investigate:
          - API connectivity issues
          - Transcript size (very long conversations slow analysis)
          - Prompt complexity (simplify prompt)

        **Graceful degradation**: Timeout → manual prompt is acceptable fallback. Better than hanging indefinitely.
      </fallback>
    </slow_path>

    <latency_targets>
      **Performance targets**:

      Fast path: <20ms per decision
      - Bash execution overhead: ~5ms
      - Pattern matching: ~5-10ms
      - JSON parsing (jq): ~5ms
      - Total: 15-23ms (measured in previous research)

      Slow path: 2-4 seconds per decision
      - Hook input prep: <100ms
      - LLM API call (Haiku): 1.5-3.5s
      - Response parsing: <100ms
      - Total: 2-4s (estimated, will measure in practice)

      Average (weighted): <500ms
      - 90% fast-path: 0.9 × 20ms = 18ms
      - 10% slow-path: 0.1 × 3000ms = 300ms
      - Total: 318ms average per decision

      **Acceptable performance**:
      - Fast-path <50ms: EXCELLENT
      - Slow-path <5s: GOOD
      - Average <600ms: SUCCESS
      - If average >1s: Investigate (low fast-path coverage or slow LLM)
    </latency_targets>

    <measurement_approach>
      **How to measure actual latency**:

      1. **Manual timing** (simple):
         ```bash
         time claude -p "Read README.md"
         # Observe total time, subtract Claude's thinking time
         # Permission decision latency = total - thinking
         ```

      2. **Log-based analysis** (accurate):
         Add timestamps to hook execution:
         ```bash
         #!/bin/bash
         START=$(date +%s%3N)  # Milliseconds
         # ... hook logic ...
         END=$(date +%s%3N)
         LATENCY=$((END - START))
         echo "Latency: ${LATENCY}ms" >> ~/.claude/hook-latency.log
         ```

      3. **Statistical analysis**:
         ```bash
         # From latency logs
         awk '{sum+=$2; count++} END {print "Average:", sum/count "ms"}' ~/.claude/hook-latency.log
         awk '{if($2<min || min=="") min=$2; if($2>max) max=$2} END {print "Min:", min "ms", "Max:", max "ms"}' ~/.claude/hook-latency.log
         ```

      4. **Comparison testing**:
         - Measure 10 tasks with autonomous hooks
         - Measure same 10 tasks with manual intervention (time includes manual review)
         - Compare total time: Autonomous should be 5-15 minutes faster per session

      **Realistic targets based on real usage**:
      - Fast-path: Imperceptible (<50ms feels instant)
      - Slow-path: Noticeable but acceptable (2-4s brief pause)
      - Manual: Highly noticeable (10-60s interruption)
      - Net: Autonomous 10-100x faster than manual for decision-making
    </measurement_approach>
  </performance_optimization>

  <rollout_strategy>
    <phase_1_rollout>
      **Stop Hook MVP Deployment**:

      Day 1 Morning:
      - Backup ~/.claude/settings.json
      - Add Stop hook configuration
      - Review in /hooks menu
      - Test with 2-3 simple tasks

      Day 1 Afternoon:
      - Test with 2-3 complex tasks (real work)
      - Monitor continuation decisions
      - Note false positives/negatives

      Day 2-3:
      - Use Stop hook for all tasks
      - Review decision quality end of each session
      - Tune prompt if >20% false positives or >10% false negatives

      End of Week 1:
      - Assess: Is Stop hook saving time? (should be 2-10 min per task)
      - Assess: Is decision quality acceptable? (should be >70%)
      - Decision: If both yes, proceed to Phase 2. If no, tune and retry.
    </phase_1_rollout>

    <phase_2_rollout>
      **PermissionRequest Auto-Answering Deployment**:

      Week 2 Day 1:
      - Add PermissionRequest hook (prompt only, no fast-path yet)
      - Review in /hooks menu
      - Test with diverse operations: Read, Write, Edit, Bash

      Week 2 Day 2-4:
      - Use for real work
      - Monitor auto-approvals and auto-denials
      - Review logs daily for concerning decisions
      - Tune prompt if false negative >5% or false positive >20%

      Week 2 Day 5:
      - Full session test: Complex task with zero manual intervention
      - Assess: Can you walk away and return to completed work?
      - Decision: If yes and safe, proceed to Phase 3. If no, tune and retry.

      **Success indicator**: Full work session (30-60 min) with ZERO manual permission prompts
    </phase_2_rollout>

    <phase_3_rollout>
      **Autonomous Directive Injection Deployment**:

      Week 3 Day 1 AM:
      - Add UserPromptSubmit hook
      - Test: Give ambiguous task, observe if Claude asks fewer questions

      Week 3 Day 1 PM:
      - Compare question frequency vs previous week
      - Expected: 50%+ reduction in clarification questions

      Week 3 Rest of Week:
      - Use for all work
      - Monitor autonomous decision quality
      - Tune directive text if Claude too aggressive or too cautious

      **Success indicator**: Noticeable reduction in mid-conversation questions while maintaining reasonable decision quality
    </phase_3_rollout>

    <phase_4_rollout>
      **Fast-Path Performance Optimization** (Optional):

      Week 4 Day 1:
      - Create fast-permission-approval.sh script
      - Make executable and install
      - Add to PermissionRequest hook chain (before prompt hook)

      Week 4 Day 2:
      - Test coverage: Count fast-path vs prompt hook decisions
      - Target: >80% fast-path coverage
      - If <70%: Add more safe patterns to fast-path script

      Week 4 Day 3-5:
      - Measure latency improvement
      - Expected: Average decision time <500ms (vs 3s in Phase 2)
      - Verify no safety regressions

      **Success indicator**: Permissions feel instant (barely noticeable delays) while maintaining safety
    </phase_4_rollout>

    <full_autonomy_timeline>
      **Recommended incremental timeline**:

      **Week 1**: Phase 1 - Stop Hook MVP
      - Day 1: Deploy and basic testing (2-3 hours)
      - Days 2-5: Real usage and tuning
      - End of week: >70% continuation accuracy
      - Value delivered: 2-10 min saved per task

      **Week 2**: Phase 2 - PermissionRequest Auto-Answering
      - Day 1: Deploy and diverse testing (2-3 hours)
      - Days 2-5: Real usage and decision monitoring
      - End of week: >85% approval accuracy, <5% denial false negatives
      - Value delivered: 10-20 manual interventions eliminated per session

      **Week 3**: Phase 3 - Autonomous Directive Injection
      - Day 1: Deploy and question frequency testing (1 hour)
      - Days 2-5: Real usage and decision quality monitoring
      - End of week: >40% question reduction, >75% decision quality
      - Value delivered: Further reduction in manual intervention

      **Week 4**: Phase 4 - Fast-Path Optimization (Optional)
      - Day 1: Script creation and deployment (1-2 hours)
      - Days 2-5: Coverage and latency measurement
      - End of week: >80% fast-path coverage, <500ms average latency
      - Value delivered: Improved user experience (feels instant)

      **Aggressive timeline** (1 week total):
      - Day 1: Phases 1-2 (5-6 hours implementation + testing)
      - Day 2-3: Phases 3-4 (2-3 hours implementation + testing)
      - Days 4-7: Real usage across all phases, monitoring and tuning

      **Conservative timeline** (4 weeks as outlined):
      - Gradual rollout, thorough testing, confidence building
      - Recommended for first-time autonomous operation deployment
      - Allows iteration and learning between phases

      **Expected first value**:
      - Within 1 day: Stop hook prevents premature stopping
      - Within 1 week: Full autonomy (Phases 1-3)
      - Within 2 weeks: Optimized autonomy (Phase 4)

      **ROI timeline**:
      - Implementation: 6-9 hours total
      - Time saved: 7 hours per month ongoing
      - Breaks even: First month (implementation time recovered)
      - Year 1 net: ~77 hours saved (84 - 7 implementation)
    </full_autonomy_timeline>

    <metrics_and_monitoring>
      **Success metrics to track throughout rollout**:

      **Phase 1 (Stop hook)**:
      - Continuation count per session
      - Continuation accuracy (% correct blocks)
      - False positive rate (blocks when complete)
      - False negative rate (approves when incomplete)
      - Time saved per task (vs manual verification)

      **Phase 2 (PermissionRequest)**:
      - Permission requests per session
      - Auto-approval count and accuracy
      - Auto-denial count and accuracy
      - False positive rate (blocks safe operations)
      - False negative rate (approves risky operations)
      - Manual interventions (should be zero)

      **Phase 3 (UserPromptSubmit)**:
      - Question frequency (before vs after)
      - Autonomous decision quality
      - User satisfaction (can I walk away?)

      **Phase 4 (Fast-path)**:
      - Fast-path coverage (%)
      - Average decision latency
      - Safety preservation (no new false negatives)

      **Overall session metrics**:
      - Total manual interventions per session (target: 0)
      - Time saved per session (target: 10-20 minutes)
      - User confidence level (subjective, 1-10 scale)
      - Task completion success rate

      **Monthly review**:
      - Total decisions made autonomously
      - Total time saved
      - Decision quality trends
      - Prompt tuning opportunities identified
    </metrics_and_monitoring>
  </rollout_strategy>

  <metadata>
    <confidence level="high">
      **Overall Confidence: HIGH**

      This implementation plan is highly likely to succeed because:

      1. **Research validation**: All hook types verified in official Claude Code documentation
      2. **Technical feasibility**: Prompt-based hooks eliminate complexity (no subprocess management, no recursion risk)
      3. **Performance acceptable**: 2-4s autonomous decision << 10-60s manual intervention
      4. **Previous research**: Delegation architecture and recursion prevention already validated
      5. **Incremental approach**: Each phase independently testable and reversible
      6. **Clear success criteria**: Measurable outcomes for each phase
      7. **Safety mechanisms**: Escape hatches, logging, rollback plans
      8. **No hard blockers**: Zero technical impediments identified in research

      **Confidence breakdown**:
      - Phase 1 (Stop hook): 95% confidence - simple prompt hook, lowest risk, highest value
      - Phase 2 (PermissionRequest): 90% confidence - core autonomy, prompt hook proven viable
      - Phase 3 (UserPromptSubmit): 95% confidence - trivial bash hook, very low risk
      - Phase 4 (Fast-path): 85% confidence - bash pattern matching reliable, but coverage estimates need validation

      **Risk areas** (low confidence):
      - Actual LLM decision quality (estimated 90-95%, needs measurement)
      - Fast-path coverage (estimated 85-90%, needs measurement)
      - User trust building timeline (variable by individual)
      - Edge cases not covered in testing

      All risk areas are measurable during implementation and tunable post-deployment.
    </confidence>

    <dependencies>
      **Required before implementation**:
      - Claude Code CLI installed and functioning
      - ~/.claude/settings.json exists (created on first Claude Code run)
      - Haiku API access (included with Claude Code subscription)
      - User comfortable editing JSON configuration files
      - bash shell available (standard on macOS/Linux)

      **Required for Phase 4 only**:
      - jq installed for JSON parsing: `brew install jq` or `apt-get install jq`
      - Verified: `jq --version` returns version number

      **Optional but helpful**:
      - JSON syntax validator (online tool or IDE plugin)
      - Text editor with JSON syntax highlighting
      - Backup strategy for configuration files
      - Performance monitoring tools (for latency measurement)

      **External dependencies**:
      - Anthropic Haiku API availability (Claude Code dependency)
      - Network connectivity for LLM API calls (prompt hooks)
      - Claude Code version supporting prompt-based hooks (current versions)

      **No blockers**: All dependencies either already exist or easily installable
    </dependencies>

    <open_questions>
      **Questions to be answered during implementation** (non-blocking):

      1. **Actual prompt hook latency**: Estimated 2-4s, needs measurement in production
      2. **Actual LLM decision quality**: Estimated 90-95% accuracy, needs real usage data
      3. **Optimal verification criteria**: What completion criteria work best for different project types?
      4. **Fast-path coverage**: Estimated 85-90%, actual coverage TBD
      5. **Infinite loop frequency**: How often do Stop hooks cause 3+ continuations?
      6. **Transcript size impact**: At what conversation length does LLM analysis slow down significantly?
      7. **Cost in practice**: Estimated $15/month, actual API usage TBD
      8. **User trust timeline**: How long until fully comfortable with autonomous operation?
      9. **Prompt tuning frequency**: How often do prompts need adjustment?
      10. **Per-project variance**: Do different project types need different autonomous configurations?

      **All answerable through**:
      - Real usage monitoring
      - Decision logging and review
      - Latency measurement
      - Cost tracking
      - User feedback

      **None are blockers**: Implementation can proceed, answers will emerge during rollout.
    </open_questions>

    <assumptions>
      **Specified by user** (validated):
      - ✅ Cost is not a concern - optimize for human time savings
      - ✅ 6-7 second latency acceptable for complex decisions
      - ✅ "AI" means Claude instance or prompt hooks, not abstract AI
      - ✅ User wants YOLO mode + full autonomy + quality assurance
      - ✅ Solo developer (no team coordination needed)

      **Technical assumptions** (reasonable estimates):
      - Prompt hook latency: 2-4s (based on API call overhead, conservative estimate)
      - LLM decision quality: 90-95% (based on typical LLM performance for clear criteria)
      - Fast-path coverage: 85-90% (based on common development operation patterns)
      - User tolerance for autonomous mistakes: High (YOLO mode preference stated)
      - Hook reliability: High (managed by Claude Code, not user-spawned processes)

      **Validated from research**:
      - ✅ Command hook performance: 15-23ms (measured)
      - ✅ Subprocess delegation: 6-7s (measured)
      - ✅ Settings override prevents recursion (tested)
      - ✅ Hooks receive full context (documented)
      - ✅ stop_hook_active flag exists (documented)

      **Behavioral assumptions**:
      - User will review decision logs periodically (enables trust building)
      - User comfortable with gradual rollout (allows iteration)
      - User willing to tune prompts based on experience (enables quality improvement)
      - User values autonomous flow over perfect accuracy (YOLO mode mindset)

      **All assumptions conservative**: Actual results likely better than estimated.
    </assumptions>

    <risks_and_mitigations>
      <risk name="LLM-decision-quality">
        **Risk**: LLM makes poor autonomous decisions (false positives/negatives)
        **Impact**: MEDIUM - Could block safe operations or approve risky ones
        **Probability**: LOW-MEDIUM - Estimated 5-10% error rate
        **Mitigation**:
        - Decision logging for review and quality monitoring
        - Prompt tuning based on decision patterns
        - Conservative prompts (err on side of caution for risky operations)
        - False negative prevention prioritized (safety over convenience)
        - Escape hatches (Ctrl+C, config disable)
        **Residual risk**: LOW - Mitigations reduce impact significantly
      </risk>

      <risk name="latency-perception">
        **Risk**: Autonomous decisions feel slow, degrading user experience
        **Impact**: LOW - Only affects user perception, not functionality
        **Probability**: LOW - Fast-path handles 85-90% in <50ms
        **Mitigation**:
        - Hybrid fast/slow path (Phase 4 optimization)
        - Average latency <500ms vs 10-60s manual (huge improvement)
        - User expectation setting (2-4s pause acceptable for autonomy)
        **Residual risk**: VERY LOW - Performance target easily achievable
      </risk>

      <risk name="trust-in-autonomy">
        **Risk**: User doesn't trust autonomous decisions, constantly intervenes
        **Impact**: MEDIUM - Defeats purpose of autonomous operation
        **Probability**: LOW-MEDIUM - Depends on individual comfort level
        **Mitigation**:
        - Gradual rollout builds confidence incrementally
        - Decision logging provides transparency
        - Escape hatches preserve user control
        - Quality tuning addresses decision issues
        **Residual risk**: LOW - User explicitly requested autonomous mode (high initial trust)
      </risk>

      <risk name="safety-regression">
        **Risk**: Autonomous hooks approve genuinely dangerous operations
        **Impact**: HIGH - Could cause data loss or security issues
        **Probability**: VERY LOW - Multiple safety layers
        **Mitigation**:
        - Conservative prompt design (deny when uncertain about high-risk ops)
        - Fast-path explicit dangerous command blocklist
        - User review of denied operations (learns safe patterns)
        - False negative rate <5% target (critical threshold)
        **Residual risk**: VERY LOW - Safety prioritized in all prompts
      </risk>

      <risk name="infinite-continuation-loops">
        **Risk**: Stop hook causes endless continuation without finishing
        **Impact**: MEDIUM - Wastes time and resources
        **Probability**: VERY LOW - Built-in prevention
        **Mitigation**:
        - stop_hook_active flag tracking
        - Maximum 3 continuations before forced approval
        - Continuation count visible in logs
        - Ctrl+C escape available
        **Residual risk**: VERY LOW - Hard limit prevents infinite loops
      </risk>

      <risk name="configuration-complexity">
        **Risk**: Settings.json becomes unmaintainable with many hooks
        **Impact**: LOW - Only affects future modifications
        **Probability**: LOW - Four hooks total, well-structured
        **Mitigation**:
        - Clear documentation in this plan
        - Modular hook design (each independent)
        - Comments in configuration files
        - Backup before changes
        **Residual risk**: VERY LOW - Configuration is static once deployed
      </risk>

      <risk name="API-availability">
        **Risk**: Haiku API unavailable, prompt hooks fail
        **Impact**: LOW - Graceful degradation to manual prompts
        **Probability**: VERY LOW - Claude Code manages API reliability
        **Mitigation**:
        - Timeout handling (30s max)
        - Fallback to manual permission on timeout
        - Network connectivity check before relying on autonomy
        **Residual risk**: VERY LOW - API highly reliable, timeout prevents hanging
      </risk>

      **Overall risk assessment**: LOW
      - No high-probability high-impact risks
      - Most risks have effective mitigations
      - Residual risks acceptable for YOLO mode operation
      - Incremental rollout allows early risk detection and correction
    </risks_and_mitigations>
  </metadata>
</plan>

<research_objective>
Investigate the execution time limitations for PreToolUse hooks in Claude Code and explore an alternative architecture where permission evaluation is delegated to a separate Claude instance (YOLO mode without hooks) to avoid timeout constraints.

This research will inform architectural decisions about hook-based validation systems and whether delegating permission decisions to a separate Claude process could improve reliability and remove time constraints.
</research_objective>

<context>
Current Implementation:
- PreToolUse hooks configured in `~/.claude/settings.json`
- Validator script: `~/.claude/hooks/validators/approach1-auto-approve.sh`
- Hook reads JSON from stdin, validates commands, returns decisions
- Default timeout: 60 seconds (configurable)
- Exit code 2 blocks tool execution

Related Documentation:
- `~/.claude/hooks/DEPLOYMENT-COMPLETE.md` - Current production deployment
- `~/.claude/hooks/COMPATIBILITY-TEST-RESULTS.md` - Test results
- `~/.claude/hooks/ARCHITECTURE.md` - System design
- Claude Code hooks documentation: https://code.claude.com/docs/en/hooks.md

Alternative Architecture Hypothesis:
Instead of having hooks execute validation logic directly, hooks could:
1. Spawn a separate `claude` process (YOLO mode, no hooks to avoid recursion)
2. Pass the tool use request to this process for evaluation
3. The separate Claude instance applies reasoning to determine if tool use should be allowed
4. Return the decision to the hook
5. Hook returns the decision to the main Claude instance

Potential Benefits:
- No timeout constraints (Claude instances can run indefinitely)
- More sophisticated reasoning about permissions (full LLM capabilities)
- Can reference project context, documentation, policies
- Natural language policy definitions instead of bash scripts
- Self-improving (Claude can learn from permission decisions)

Potential Drawbacks:
- Performance overhead (spawning Claude process)
- Complexity (managing multiple Claude instances)
- Cost (API calls for each permission check)
- Recursion risks (hooks triggering hooks)
</context>

<research_scope>
Thoroughly investigate the following areas:

1. **Hook Execution Time Limits**
   - Default timeout for PreToolUse hooks
   - Maximum configurable timeout
   - What happens when timeout is exceeded
   - Performance benchmarks from existing tests
   - Whether timeouts can be disabled

2. **Hook Architecture Constraints**
   - Can hooks spawn subprocesses?
   - Can hooks call other Claude instances?
   - Hook execution environment (permissions, PATH, environment variables)
   - Recursion prevention mechanisms
   - Whether hook processes inherit parent hook configuration

3. **Delegation Architecture Feasibility**
   - Technical approach to spawn separate Claude instance from hook
   - How to pass context (tool use request, project state) to delegated instance
   - How to prevent infinite recursion (hooks in delegated instance)
   - Performance implications (cold start, API latency)
   - Cost analysis (API calls per tool use)

4. **Claude Code Hook Documentation**
   - Search official documentation for timeout configuration
   - Look for examples of hooks spawning external processes
   - Check for guidance on complex validation logic
   - Review performance best practices

5. **Alternative Approaches**
   - Use of `type: "prompt"` hooks instead of `type: "command"`
   - Async hook execution models
   - Caching validation results
   - Pre-authorization of common patterns
</research_scope>

<investigation_steps>
1. **Review Current Hook Performance Data**
   - Read `~/.claude/hooks/COMPATIBILITY-TEST-RESULTS.md` for timing data
   - Check `/tmp/hook-debug.log` for execution timestamps
   - Analyze overhead from existing tests (reported as <60ms)

2. **Study Claude Code Hook Documentation**
   - Use WebSearch or WebFetch to access https://code.claude.com/docs/en/hooks.md
   - Look for sections on:
     - Timeout configuration
     - Performance considerations
     - Complex validation examples
     - Subprocess spawning from hooks

3. **Analyze Current Hook Implementation**
   - Read `~/.claude/hooks/validators/approach1-auto-approve.sh`
   - Identify current execution time components:
     - JSON parsing (jq)
     - Pattern matching (bash regex)
     - Script execution
   - Estimate which operations could timeout in edge cases

4. **Design Delegation Architecture**
   Create a detailed design for the delegation approach:

   **Hook Script** (`permission-delegator.sh`):
   ```bash
   #!/bin/bash
   # Read tool use request from stdin
   input=$(cat)

   # Extract relevant context
   tool_name=$(echo "$input" | jq -r '.tool_name')
   tool_input=$(echo "$input" | jq -r '.tool_input')
   cwd=$(echo "$input" | jq -r '.cwd')

   # Create permission request for delegation
   permission_request=$(cat <<EOF
   {
     "tool": "$tool_name",
     "input": $tool_input,
     "context": {
       "cwd": "$cwd",
       "project": "$(basename $cwd)"
     }
   }
   EOF
   )

   # Spawn separate Claude instance with YOLO mode + no hooks
   # Pass permission request as system prompt
   decision=$(echo "Evaluate this tool use request and respond with JSON: {\"decision\": \"allow|deny\", \"reason\": \"...\"}

   Request: $permission_request

   Policy: Block direct gh CLI usage. Allow script library and regular commands." | \
     claude -p \
       --dangerously-skip-permissions \
       --settings '{"hooks":{}}' \
       --system-prompt "You are a permission evaluator. Respond ONLY with JSON.")

   # Parse decision and return to hook
   echo "$decision"
   ```

   **Questions to answer:**
   - How to prevent recursion? (--settings override? environment variable?)
   - How to pass complex policies? (separate policy file? inline?)
   - How to handle Claude API failures? (fallback to allow? deny? cached decision?)
   - How to optimize performance? (connection pooling? persistent process?)

5. **Prototype and Benchmark**
   - Create a simple prototype of the delegation approach
   - Measure end-to-end latency:
     - Hook invocation
     - Claude process spawn
     - Decision generation
     - Response parsing
     - Total time
   - Compare to current approach (<60ms)
   - Determine if acceptable for interactive use

6. **Evaluate Trade-offs**
   Create a comparison matrix:

   | Aspect | Current (Bash Script) | Delegated (Claude Instance) |
   |--------|----------------------|----------------------------|
   | Execution time | <60ms | TBD (likely 500-2000ms) |
   | Timeout risk | Low (simple logic) | None (Claude handles long tasks) |
   | Sophistication | Pattern matching | Full reasoning |
   | Maintainability | Bash regex | Natural language policies |
   | Cost | Free | ~$0.01-0.10 per decision |
   | Reliability | High (deterministic) | Medium (LLM variability) |
   | Recursion risk | None | Must be prevented |

7. **Identify Optimal Hybrid Approach**
   Consider combining both:
   - Fast path: Simple bash validation for common cases (gh blocking)
   - Slow path: Delegate complex decisions to Claude instance
   - Caching: Store Claude decisions for repeated patterns

   Example:
   ```bash
   # Fast path - deterministic rules
   if [[ "$COMMAND" =~ gh[[:space:]]+(issue|pr|project|api) ]]; then
     # Simple block - no delegation needed
     exit 2
   fi

   # Slow path - complex decision
   if [[ "$COMMAND" =~ suspicious_pattern ]]; then
     # Delegate to Claude for reasoning
     decision=$(delegate_to_claude "$COMMAND")
     # Cache result for future use
     cache_decision "$COMMAND" "$decision"
   fi

   # Default: allow
   exit 0
   ```
</investigation_steps>

<deliverables>
Create a comprehensive research report saved to: `./.prompts/022-hook-timeout-research-RESULTS.md`

The report must include:

1. **Executive Summary**
   - Key findings about hook timeouts
   - Feasibility of delegation architecture
   - Recommendation (keep current, adopt delegation, or hybrid)

2. **Hook Timeout Investigation Results**
   - Default and maximum timeout values
   - Performance data from current implementation
   - Timeout risk assessment for current validators
   - Configuration options available

3. **Delegation Architecture Analysis**
   - Technical design details
   - Prototype implementation (if created)
   - Performance benchmarks
   - Recursion prevention strategy
   - Cost analysis

4. **Trade-off Analysis**
   - Detailed comparison matrix
   - Use cases favoring each approach
   - Risk assessment

5. **Recommendations**
   - **Primary recommendation**: Which approach for production?
   - **Hybrid approach**: If applicable, describe the combination strategy
   - **Migration path**: If changing from current approach
   - **Implementation steps**: Concrete next steps

6. **Open Questions**
   - Unresolved technical questions
   - Areas needing further research
   - Assumptions that need validation

7. **Appendix**
   - Prototype code (if created)
   - Benchmark data
   - Documentation excerpts
   - Example permission policies
</deliverables>

<verification>
Before completing, verify:

- [x] Claude Code hooks documentation reviewed for timeout information
- [x] Current hook performance analyzed (timing data extracted)
- [x] Delegation architecture fully designed with recursion prevention
- [x] Prototype created and benchmarked (or reasons documented if not feasible)
- [x] Trade-off analysis completed with specific metrics
- [x] Clear recommendation provided with justification
- [x] All deliverables present in research report
- [x] Report saved to `./.prompts/022-hook-timeout-research-RESULTS.md`
</verification>

<success_criteria>
This research is successful when:

1. **Hook timeout constraints are clearly documented** with specific numbers and configuration options
2. **Delegation architecture is fully designed** with working prototype or detailed technical spec
3. **Performance comparison is quantitative** with actual benchmarks (not just estimates)
4. **Clear recommendation is provided** based on data, not speculation
5. **Implementation path is actionable** with concrete next steps if adopting new approach
6. **All open questions are identified** so follow-up work is clear

The research should enable informed decision-making about whether to keep the current bash-based hook approach or adopt a Claude-delegated architecture.
</success_criteria>

<additional_context>
**Why This Matters:**

The current bash-based hook approach works well for simple pattern matching (blocking `gh` commands), but has limitations:
- Cannot reason about complex scenarios
- Hard to maintain complex rules in bash
- Limited to deterministic pattern matching

A Claude-delegated approach could enable:
- Natural language permission policies
- Context-aware decisions (e.g., "allow gh in documentation directories")
- Learning from permission decisions over time
- More maintainable policies

However, the trade-offs (latency, cost, complexity) must be understood before pursuing this direction.

**Research Philosophy:**

Approach this with both curiosity and skepticism. The delegation architecture is interesting conceptually, but may not be practical. Be honest about drawbacks. If the current approach is superior, say so clearly. If delegation has merit, provide concrete evidence.
</additional_context>

# Hook Context Detection Research

**Claude Code hooks cannot natively detect execution context, but transcript parsing provides a proven, production-ready solution for selective enforcement based on active skill detection.**

## Version
v1.0 - Comprehensive Research Complete (2025-12-19)

## Key Findings

### What Works
- **Transcript-Based Skill Detection (Approach 2)**: Parse `transcript_path` to identify active skill from JSON entries (`"tool": "Skill", "skill": "skill-name"`), achieving context-aware enforcement with 14/14 tests passed and ~18ms overhead
- **Selective Enforcement**: Block gh work item operations ONLY in designated skills (`execute-epic`, `execute-user-story`, etc.) by maintaining a skill allowlist
- **Fail-Safe Design**: Allow all operations outside work item contexts and on transcript read errors, preventing false positives

### What Doesn't Work
- **Native Caller Identification**: NO built-in environment variables or API for detecting which slash command or skill invoked the hook
- **Process Tree Analysis**: Parent process is generic shell wrapper with no distinguishing information
- **Global Enforcement (Approach 1)**: Blocks legitimate usage like `gh workflow run` in normal development workflows

### Critical Insights
- Hooks receive only: `tool_input.command`, `tool_input.description`, `transcript_path`, `session_id` via JSON stdin
- Environment contains: `CLAUDE_CODE_ENTRYPOINT=cli`, `CLAUDECODE=1` but NO `CLAUDE_ACTIVE_SKILL` or `CLAUDE_SLASH_COMMAND` variables
- Session transcripts record skill invocations as `{"type": "tool_use", "tool": "Skill", "skill": "name"}` enabling reliable detection

## Decisions Needed

**Ready to proceed** - Primary solution is proven and documented:

1. ✅ Use transcript-based skill detection (Approach 2 pattern)
2. ✅ Create `context-aware-work-items.sh` hook with implementation from research doc
3. ✅ Configure in `~/.claude/settings.json` with PreToolUse matcher
4. ✅ Define `WORK_ITEM_CONTEXTS` array with skills to enforce

**Optional testing** (low priority):
- Test environment variable propagation through Skill invocation (Alternative 1) - may offer simpler solution if it works

## Blockers

**None** - All required information gathered and validated

## Next Step

**Implement Primary Solution**: Create context-aware hook using transcript parsing to detect work item execution skills and selectively block gh commands only in those contexts (detailed implementation guide in Section 8 of research document)

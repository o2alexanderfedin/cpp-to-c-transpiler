# Quick Test: Stop Hook MVP

## IMPORTANT: Test in Fresh Session

⚠️ **The Stop hook only activates in NEW Claude sessions**. This current session was started before the hook was installed, so it won't have the Stop hook active.

---

## Quick Test (2 minutes)

Open a **new terminal** and run:

```bash
claude "Create a function called calculateSum that adds two numbers. Write unit tests."
```

### What to Observe

**If Stop Hook is Working:**
1. Claude implements the `calculateSum` function
2. If Claude tries to stop WITHOUT writing tests:
   - **Stop hook blocks** (you won't see the normal stop)
   - Claude receives continuation guidance like: "Missing: Unit tests for calculateSum. Continue by: Write tests covering positive numbers, negative numbers, and zero."
   - Claude continues automatically and writes tests
   - When tests are complete, Stop hook approves and Claude stops

**If Stop Hook is NOT Working:**
1. Claude implements function
2. Claude might skip tests
3. Claude stops immediately (no hook intervention)
4. You see normal "Task complete" message

### Expected Behavior Timeline

```
[Start] User: "Create calculateSum with tests"
   ↓
[30s-2min] Claude implements function
   ↓
[Claude tries to stop] ← Stop hook fires here
   ↓
[2-4s delay] ← LLM evaluates completion
   ↓
[Decision] Missing tests detected
   ↓
[Block] Claude receives: "Missing: Unit tests. Continue by: Write tests for..."
   ↓
[1-2min] Claude writes tests
   ↓
[Claude tries to stop again] ← Stop hook fires again
   ↓
[2-4s delay] ← LLM evaluates completion
   ↓
[Decision] All requirements met
   ↓
[Approve] Claude stops normally
```

### Success Indicators

✅ **Hook is working if you see:**
- Brief pause (2-4s) when Claude tries to stop
- Claude continues working after first stop attempt
- Claude writes tests that were "missing"
- Claude stops after completing tests

❌ **Hook is NOT working if:**
- Claude stops immediately without tests
- No pause when Claude tries to stop
- No autonomous continuation

---

## Alternative Quick Test (Even Simpler)

If you want an even simpler test to verify the hook fires:

```bash
claude "Write a hello world function"
```

**Expected**:
- Claude writes function
- Brief 2-4s pause when stopping (Stop hook verifying)
- Hook approves (simple task, no tests requested)
- Claude stops normally

You won't see continuation here (task is complete), but you'll verify the hook fires (via the pause).

---

## After Testing

### If Test Passes
- ✅ Stop hook is working!
- Use it for 3-5 real tasks over next 2-5 days
- Monitor decision quality
- If >70% accuracy → Proceed to Phase 2 (PermissionRequest)

### If Test Fails
- Hook might not be active yet
- Check `/hooks` in a fresh Claude session
- Verify settings.json syntax: `jq . ~/.claude/settings.json`
- Review rollback plan if needed

---

## Run Full Test Suite

For comprehensive testing of all 3 scenarios:

```bash
.prompts/024-autonomous-claude-ai-hooks-plan/TEST-STOP-HOOK.sh
```

This interactive script walks you through all test cases.

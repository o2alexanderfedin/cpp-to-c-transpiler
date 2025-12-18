# Phase 1 Fix #2: Stop Hook Response Schema

**Date**: 2025-12-17
**Issue**: Stop hook returned wrong JSON format, failed schema validation
**Status**: ✅ FIXED
**Fix Time**: ~2 minutes

---

## Issue Discovered

After fixing the transcript access issue, the Stop hook fired successfully but failed with:
```
Stop hook error: Schema validation failed: [
  {
    "code": "invalid_type",
    "expected": "boolean",
    "received": "undefined",
    "path": ["ok"],
    "message": "Required"
  }
]
```

### Root Cause

**Wrong response schema in prompt**. I instructed the LLM to return:
```json
{"decision": "approve", "reason": "..."}
```

But Claude Code Stop hooks expect:
```json
{"ok": true, "reason": "..."}   // For approve
{"ok": false, "reason": "..."}  // For block
```

The field name is `"ok"` (boolean), not `"decision"` (string).

---

## Fix Applied

### Updated Response Format in Prompt

**Changed from**:
```json
{"decision": "approve", "reason": "Work appears complete"}
{"decision": "block", "reason": "Missing: ..."}
```

**Changed to**:
```json
{"ok": true, "reason": "Work appears complete"}   // APPROVE
{"ok": false, "reason": "Missing: ..."}           // BLOCK
```

### Additional Safeguard

Added instruction to prompt:
```
- Return ONLY the JSON object, no markdown code blocks or extra text
```

This ensures the LLM returns clean JSON that passes schema validation.

---

## Correct Stop Hook Response Schema

Based on schema validation errors, the Stop hook must return:

### To APPROVE (allow stopping):
```json
{
  "ok": true,
  "reason": "Description of why work is complete"
}
```

### To BLOCK (continue working):
```json
{
  "ok": false,
  "reason": "Missing: [items]. Continue by: [actions]"
}
```

### Schema Requirements:
- `"ok"`: **Required**, boolean, true = approve, false = block
- `"reason"`: **Required**, string, explanation of decision

---

## Testing Status

### Ready for Re-Test #2

The test from before should now work completely:
```bash
claude "Create a function called calculateSum that adds two numbers. Write unit tests."
```

**Expected behavior**:
1. Hook fires when Claude tries to stop
2. Hook analyzes context (no transcript errors)
3. Hook returns `{"ok": true/false, "reason": "..."}`
4. Schema validation passes
5. If `ok: false`: Claude receives guidance and continues
6. If `ok: true`: Claude stops normally

### What to Observe

✅ **Success indicators**:
- No transcript access errors (fixed in Fix #1)
- No schema validation errors (fixed in Fix #2)
- Hook makes approve/block decision
- If blocking: Claude receives continuation guidance
- If approving: Claude stops normally

❌ **Failure indicators**:
- Same schema validation error
- Hook returns malformed JSON
- Hook timeout (>30s)

---

## Technical Insights

### Stop Hook Schema Requirements

Learned from schema validation errors:

1. **Required fields**:
   - `ok` (boolean): true = approve, false = block
   - `reason` (string): explanation of decision

2. **Optional fields**: None discovered yet

3. **Return format**: Pure JSON object, no markdown wrapping

4. **Forbidden**:
   - Using `"decision"` instead of `"ok"`
   - Returning markdown code blocks (```json ... ```)
   - Missing required fields
   - Wrong data types (string instead of boolean)

### How I Discovered This

1. Initial prompt used `"decision": "approve"`
2. Hook fired but schema validation failed
3. Error message revealed: `"ok"` field (boolean) required
4. Updated prompt to use `{"ok": true/false}`
5. Added safeguard: "Return ONLY the JSON object"

---

## Files Modified

**File**: `~/.claude/settings.json`
**Section**: `hooks.Stop[0].hooks[0].prompt`
**Changes**: Response format examples updated to use `{"ok": true/false}`
**Validation**: ✓ JSON syntax valid

---

## Lessons Learned

### ✅ What Worked
- Schema validation errors are informative (show exact fields/types expected)
- Prompt can be updated without restarting Claude
- jq is excellent for programmatic JSON updates

### ❌ What Didn't Work
- Guessing the response schema format
- Using generic field names like "decision"
- Assuming hook schemas match intuition

### 🔧 Best Practices
- Check official documentation for hook response schemas
- Test with real hook execution to discover actual schema
- Use schema validation errors as authoritative source
- Add explicit instructions to return clean JSON (no markdown)

---

## Next Steps

1. **Re-test #2** with same test command
2. **Verify** schema validation passes
3. **Observe** approve/block behavior
4. **Monitor** autonomous continuation quality
5. **Proceed to Phase 2** if working correctly

---

## Summary of All Fixes

**Fix #1**: Removed transcript file access (prompt hooks can't read files)
**Fix #2**: Corrected response schema (`"ok"` boolean, not `"decision"` string)

**Combined result**: Stop hook should now fire, evaluate, and respond correctly.

---

**Status**: Fix deployed, ready for re-test #2 in fresh Claude session.

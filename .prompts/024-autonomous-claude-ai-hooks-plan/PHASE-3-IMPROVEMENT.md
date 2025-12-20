# Phase 3 Improvement: Context-Aware Decision Making

**Date**: 2025-12-17
**Improvement**: Added context awareness to UserPromptSubmit directive
**User Feedback**: "Ensure Claude gets familiar with choices already made in documents and/or code"

---

## What Was Improved

### Problem Identified

Original Phase 3 directive told Claude to "make reasonable decisions" but didn't emphasize:
- Reading existing documentation first
- Understanding established patterns
- Maintaining consistency with existing code
- Learning from previous implementation choices

**Result**: Claude might make arbitrary "reasonable" decisions that conflict with existing project patterns.

### Solution Applied

Updated UserPromptSubmit hook to include **Context-Aware Decision Making** section:

```
**Context-Aware Decision Making**:
- **ALWAYS review existing context before deciding**:
  - Read README.md, ARCHITECTURE.md, CONTRIBUTING.md if they exist
  - Examine existing code patterns, naming conventions, file structure
  - Check for similar existing implementations to maintain consistency
  - Review recent commits/changes to understand project direction
  - Look for configuration files (tsconfig, package.json, etc.) that reveal choices already made
- Make decisions **consistent with existing project choices**
- When you find established patterns, follow them (don't introduce new patterns without reason)
- Note: "Following existing pattern from [file/location]" when applying learned conventions
```

### Key Additions

1. **"ALWAYS review existing context before deciding"**
   - Explicit instruction to survey the landscape first
   - Lists specific files to check (README, ARCHITECTURE, CONTRIBUTING)
   - Includes code patterns and configuration files

2. **"Make decisions consistent with existing project choices"**
   - Prioritizes consistency over "better" approaches
   - Prevents introducing unnecessary new patterns

3. **"Note: 'Following existing pattern from [file/location]'"**
   - Claude should cite where patterns came from
   - Provides transparency in decision-making

4. **Updated Work Flow with explicit first step**:
   - "1. **First: Survey the landscape**"
   - Makes context review the primary action before any decisions

5. **New question trigger**:
   - "When existing code shows conflicting patterns (ask which to follow)"
   - Handles cases where project has inconsistencies

---

## Why This Matters

### Without Context Awareness

```
User: "Add a new API endpoint for user profiles"

Claude (arbitrary decision):
- Chooses Express.js patterns (but project uses Fastify)
- Uses camelCase (but project uses snake_case)
- Puts code in /api/ (but project uses /routes/)
- Creates inconsistency in codebase
```

### With Context Awareness

```
User: "Add a new API endpoint for user profiles"

Claude (informed decision):
1. Reads existing route files in /routes/
2. Sees project uses Fastify, snake_case, specific error handling
3. Examines /routes/auth.ts as reference implementation
4. Notes in response: "Following existing pattern from routes/auth.ts"
5. Creates /routes/user_profile.ts using established conventions
6. Maintains consistency across codebase
```

---

## Impact on Behavior

### Autonomous Decisions Are Now

**✅ Informed** - Based on actual project context
**✅ Consistent** - Follows established patterns
**✅ Educated** - Understands "why" behind existing choices
**✅ Transparent** - Cites sources for decisions
**✅ Safe** - Asks when patterns conflict

### Examples of Improved Behavior

**Before improvement**:
```
Claude: "I'll use TypeScript interfaces for data models"
(arbitrary choice, might conflict with existing Zod schemas)
```

**After improvement**:
```
Claude: "I'll use Zod schemas for data models, following existing
pattern from src/models/user.ts"
(informed choice, maintains consistency)
```

---

## Testing the Improvement

### Test Scenario: Existing Patterns

**Setup**: Project with established patterns
- Uses Vitest (not Jest)
- Uses functional components (not classes)
- Uses kebab-case file names
- Has specific error handling pattern

**Task**: "Add user authentication"

**Expected behavior with improvement**:
1. ✅ Claude reads existing test files → discovers Vitest
2. ✅ Claude examines components → sees functional style
3. ✅ Claude checks file names → sees kebab-case
4. ✅ Claude finds error-handler.ts → uses same pattern
5. ✅ Claude implements: auth-service.ts (kebab-case), functional, Vitest, consistent error handling
6. ✅ Claude notes: "Following existing patterns from components/user.tsx and utils/error-handler.ts"

**Result**: Consistent, informed implementation

---

## Updated Directive Structure

### 1. Context-Aware Decision Making (NEW)
- Review docs, code, patterns first
- Maintain consistency
- Cite sources

### 2. Technical Decision Making
- Make reasonable decisions
- Choose simple approaches
- Prefer consistency over "better"

### 3. Quality Standards
- Clean, tested, documented code
- SOLID, KISS, DRY, YAGNI, TRIZ
- TDD workflow

### 4. Completion Criteria
- All requirements met
- Tests passing
- No placeholders

### 5. When to Ask Questions
- Architecture/safety decisions
- User preferences
- Business logic
- Trade-offs
- **Conflicting patterns (NEW)**

### 6. Work Flow (UPDATED)
- **Step 1: Survey the landscape (NEW)**
- Make informed decisions
- Implement with conventions
- Test, commit, verify

---

## Comparison: Before vs After

### Original Phase 3 Directive

```
**Decision Making**:
- Make reasonable technical decisions without asking when the choice is clear
- Choose simple, well-established approaches over complex ones when uncertain
```

**Problem**: What's "reasonable" without context? Could be arbitrary.

### Improved Phase 3 Directive

```
**Context-Aware Decision Making**:
- **ALWAYS review existing context before deciding**:
  - Read README.md, ARCHITECTURE.md, CONTRIBUTING.md if they exist
  - Examine existing code patterns, naming conventions, file structure
  [...]
- Make decisions **consistent with existing project choices**
```

**Improvement**: "Reasonable" now means "consistent with existing project context"

---

## Benefits

### For Consistency
- ✅ New code matches existing style
- ✅ Patterns remain uniform across project
- ✅ No surprise "improvements" that break conventions

### For Quality
- ✅ Decisions based on understanding, not guessing
- ✅ Leverages existing good choices
- ✅ Avoids reinventing the wheel

### For Trust
- ✅ Claude cites sources for decisions
- ✅ User can verify Claude learned correctly
- ✅ Transparent decision-making process

### For Autonomy
- ✅ Fewer questions (context provides answers)
- ✅ More confident decisions (based on evidence)
- ✅ Better quality (informed choices)

---

## Edge Cases Handled

### Case 1: No Existing Patterns

**Scenario**: Brand new project, no code yet

**Behavior**:
- Claude reads README/docs (if present)
- Falls back to well-established industry patterns
- Notes: "No existing patterns found, using industry standard [X]"

### Case 2: Conflicting Patterns

**Scenario**: Project has mix of styles (legacy + modern)

**Behavior**:
- Claude detects conflict
- Asks: "I see both Class components and Functional components. Which pattern should I follow?"
- User clarifies
- Claude proceeds consistently

### Case 3: Outdated Patterns

**Scenario**: Existing code uses deprecated approach

**Behavior**:
- Claude follows existing pattern (consistency)
- Unless: Pattern is security risk or critically broken
- Then: Claude asks before deviating

---

## Implementation Details

### Files Modified

**~/.claude/settings.json** - UserPromptSubmit hook command updated

### Changes Made

1. **Added**: "Context-Aware Decision Making" section (top priority)
2. **Updated**: "Technical Decision Making" to reference consistency
3. **Added**: "When existing code shows conflicting patterns" to question triggers
4. **Updated**: Work Flow to start with "Survey the landscape"
5. **Maintained**: All existing quality, completion, and workflow guidance

### Backward Compatible

- ✅ All previous Phase 3 behavior preserved
- ✅ Added layer on top (doesn't break anything)
- ✅ Works with Phases 1, 2, 4 unchanged

---

## Success Metrics (Updated)

### New Metrics for Context Awareness

- [ ] Claude reads docs/code before deciding (observable in behavior)
- [ ] Decisions cite sources ("Following pattern from X")
- [ ] New code matches existing style (>90% consistency)
- [ ] Zero introduction of conflicting patterns
- [ ] Questions asked when patterns conflict (catch rate >80%)

### Existing Metrics (Still Apply)

- [ ] Questions per task: <2 (was 3-5)
- [ ] Decision quality: >80% reasonable
- [ ] Time saved: 5-20 minutes per session

---

## Next Steps

### Testing

Test with projects that have:
1. **Established patterns** - Verify Claude follows them
2. **Documentation** - Verify Claude reads it
3. **Conflicting patterns** - Verify Claude asks
4. **No patterns** (new project) - Verify Claude notes this

### Tuning

If Claude:
- **Doesn't read docs** → Strengthen "ALWAYS review" language
- **Ignores patterns** → Add more examples of following patterns
- **Never asks about conflicts** → Lower threshold for asking

---

## Conclusion

**Phase 3 improvement deployed successfully!**

**Key enhancement**: Autonomous decisions are now **context-aware** and **informed** rather than arbitrary.

**User benefit**: Claude makes educated decisions consistent with your project, not random "reasonable" choices.

**Ready for testing in next fresh session!**

---

**Files Updated**:
- ✅ `~/.claude/settings.json` - UserPromptSubmit hook improved
- ✅ `PHASE-3-IMPROVEMENT.md` - This documentation

**Status**: Phase 3 v2 deployed, ready to test

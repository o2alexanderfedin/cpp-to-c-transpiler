# Implement: Fix Pointer Type Recursion Bug (TDD)

<objective>
Execute the pointer bug fix plan using strict Test-Driven Development. Follow the RED-GREEN-REFACTOR cycle religiously: write failing test → implement minimal fix → verify test passes → refactor → repeat.

**Why this matters**: TDD ensures the fix is correct, complete, and won't regress. Each test proves a specific behavior works.

**End goal**: Transpiler no longer generates infinite pointer wrapper functions. All tests pass. Real-world code transpiles correctly.
</objective>

<context>
**Plan to execute**:
@.prompts/037-pointer-bug-plan/pointer-bug-plan.md - Detailed phase-by-phase plan
@.prompts/037-pointer-bug-plan/SUMMARY.md - Quick reference

**Research findings**:
@.prompts/036-pointer-bug-research/pointer-bug-research.md - Root cause and fix strategies

**Current bug state**:
@test-logs/transpiler-regression-analysis.md - Bug symptoms
@test-logs/transpiler-fix-validation.txt - Current test results

**Project conventions**:
@CLAUDE.md - TDD requirements, SOLID principles, testing standards
</context>

<implementation_requirements>

## TDD Cycle (MANDATORY)

**For EVERY feature/fix**, follow this exact cycle:

### 1. RED Phase
```bash
# Write the test FIRST
# Test MUST fail (proves it tests the bug)
cd build_working
make [TestName]
./[TestName]
# OUTPUT: Test FAILS ❌
```

### 2. GREEN Phase
```bash
# Implement MINIMAL code to pass
# Only add what's needed for THIS test
make [TestName]
./[TestName]
# OUTPUT: Test PASSES ✅
```

### 3. REFACTOR Phase
```bash
# Clean up code while keeping tests green
# Improve design, remove duplication
make [TestName]
./[TestName]
# OUTPUT: Test still PASSES ✅
```

### 4. COMMIT
```bash
git add [changed files]
git commit -m "test: add test for [feature]"
git add [implementation files]
git commit -m "fix: implement [feature] to pass test"
```

**Repeat for next test/feature**

## Execution Protocol

**Follow the plan phases EXACTLY**:

1. Read phase from pointer-bug-plan.md
2. For each task in phase:
   - If type="test": Write test, verify it FAILS
   - If type="impl": Implement fix, verify test PASSES
   - If type="refactor": Clean up, verify tests still PASS
3. Run phase verification commands
4. Mark phase complete
5. Move to next phase

**DO NOT skip ahead** - phases build on each other.

## Test Writing Standards

**Every test must**:
- Have descriptive name: `TEST(PointerTypeTest, SimplePointerDoesNotRecurse)`
- Test ONE specific behavior
- Have clear ARRANGE-ACT-ASSERT structure
- Use assertions that give helpful failure messages
- Be independent (no shared state between tests)

**Example**:
```cpp
TEST(PointerTypeTest, SimplePointerGeneratesExactlyOneWrapper) {
    // ARRANGE
    string cpp_code = "int* ptr;";
    TranspilerAPI transpiler;

    // ACT
    auto result = transpiler.transpile(cpp_code);

    // ASSERT
    EXPECT_TRUE(result.success);
    int wrapper_count = countFunctionMatching(result.c, ".*_ptr$");
    EXPECT_EQ(1, wrapper_count)
        << "Expected exactly 1 pointer wrapper, got " << wrapper_count;
}
```

## Implementation Standards

**Code must**:
- Follow SOLID principles (see CLAUDE.md)
- Be minimal (only what's needed to pass current test)
- Have clear, self-documenting names
- Include comments for non-obvious logic
- Handle edge cases discovered in tests

**Example**:
```cpp
// Fix: Add recursion depth tracking to prevent infinite wrapper generation
class PointerTypeGenerator {
private:
    std::set<std::string> visitedTypes;  // Memoization
    int maxDepth = 5;  // Prevent deep recursion

public:
    std::string generateWrapper(const Type* type, int depth = 0) {
        // Termination: depth limit
        if (depth >= maxDepth) {
            return "/* max pointer depth reached */";
        }

        // Termination: already generated
        string typeName = type->getCanonicalType().getAsString();
        if (visitedTypes.count(typeName)) {
            return "/* pointer type already generated */";
        }
        visitedTypes.insert(typeName);

        // Generate wrapper...
    }
};
```

## Progress Tracking

**Use TodoWrite extensively**:
```javascript
TodoWrite({
  todos: [
    {content: "Phase 1: Test Infrastructure", status: "completed"},
    {content: "Phase 2: Write failing tests", status: "in_progress"},
    {content: "Phase 2.1: Test simple pointer", status: "completed"},
    {content: "Phase 2.2: Test nested pointers", status: "in_progress"},
    {content: "Phase 3: Implement fix", status: "pending"},
    // etc.
  ]
});
```

Update after each task completion for visibility.

## Validation Commands

**After each phase**, run:

```bash
# 1. All unit tests
cd build_working
make all_tests
./run_all_unit_tests

# 2. Specific pointer tests
./PointerTypeHandlingTest

# 3. Integration test with test-point.cpp
./transpiler-api-cli ../test-point.cpp --json | jq -r '.c' | wc -l
# Should be <500 lines, not 4MB

# 4. Real-world validation
./transpiler-api-cli ../tests/real-world/json-parser/src/JsonValue.cpp \
  -I ../tests/real-world/json-parser/include --json | jq -r '.c' | wc -l
# Should be reasonable size

# 5. Regression check
make test
```

## Error Handling

**If a test fails unexpectedly**:
1. DON'T skip it - investigate why
2. Check if test assumptions are wrong
3. Check if implementation has side effects
4. Fix the issue before moving on
5. Document the learning

**If implementation breaks existing tests**:
1. STOP immediately
2. Review what changed
3. Determine if breaking change is necessary
4. If yes: update affected tests with justification
5. If no: fix implementation to maintain compatibility

## Documentation Requirements

**Update after implementation**:
1. Add comments to changed code explaining WHY (not just WHAT)
2. Update README.md if behavior changes
3. Add entry to CHANGELOG.md
4. Document any new configuration options
5. Update test documentation

</implementation_requirements>

<output>
**Code changes**:
- Modified source files with fixes
- New/updated test files
- Updated documentation

**Test results**:
All tests passing with output logs in: `test-logs/pointer-bug-fix-tests.txt`

**Summary**: `.prompts/038-pointer-bug-implement/SUMMARY.md`

**Required format**:

```markdown
# Pointer Bug Fix Implementation Summary

**[One substantive sentence describing what was fixed and how]**

## Files Changed
• [File 1] - [What changed]
• [File 2] - [What changed]
• [File 3] - [What changed]

## Tests Added
- Unit tests: [count] tests
- Integration tests: [count] tests
- Regression tests: [count] tests

## Test Results
✅ All [total] tests passing
✅ test-point.cpp output: [size] (was 4.4MB)
✅ Real-world code transpiles successfully

## Verification Commands
```bash
[Commands to verify the fix]
```

## Decisions Needed
[Any remaining decisions, or "None - fix complete"]

## Blockers
[Any issues encountered, or "None"]

## Next Step
[What to do next: test with more real-world code, merge to develop, etc.]
```
</output>

<constraints>
- **NEVER skip the RED phase** - tests must fail first
- **NEVER implement without a failing test** - that's not TDD
- **NEVER commit broken tests** - always fix before committing
- Follow CLAUDE.md principles religiously (SOLID, TDD, KISS, DRY)
- Run linters before each commit (zero errors/warnings required)
- Use git flow if creating a feature branch
- Write meaningful commit messages
</constraints>

<verification>
Before declaring complete, verify:
- ✅ All tests written BEFORE implementation
- ✅ All tests initially FAILED (RED phase documented)
- ✅ All tests now PASS (GREEN phase verified)
- ✅ Code refactored for clarity (REFACTOR phase done)
- ✅ test-point.cpp generates reasonable output (<500 lines)
- ✅ Real-world code transpiles successfully
- ✅ No regression in existing tests
- ✅ All linters pass (zero errors/warnings)
- ✅ SUMMARY.md created with test results
- ✅ Changes committed with proper messages
</verification>

<success_criteria>
- Pointer recursion bug is fixed (no infinite wrapper generation)
- Comprehensive test coverage added (15+ tests)
- All tests passing (100% pass rate)
- test-point.cpp output <500 lines (vs 4.4MB before)
- Real-world projects transpile successfully
- No regression in existing functionality
- Code follows SOLID, TDD, and project conventions
- SUMMARY.md documents the fix and verification
</success_criteria>

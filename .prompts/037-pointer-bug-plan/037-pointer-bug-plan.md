# Plan: Fix Pointer Type Recursion Bug with TDD

<objective>
Create a detailed, phased implementation plan to fix the pointer type recursion bug using Test-Driven Development. Each phase must have tests written BEFORE implementation.

**Why this matters**: Ensures the fix is robust, doesn't break existing functionality, and prevents regression.

**End goal**: Step-by-step plan ready for autonomous execution with full test coverage.
</objective>

<context>
**Research findings**:
@.prompts/036-pointer-bug-research/pointer-bug-research.md - Root cause analysis and fix strategies
@.prompts/036-pointer-bug-research/SUMMARY.md - Quick reference

**Project structure**:
@CLAUDE.md - TDD and testing requirements
@tests/ - Existing test structure
@CMakeLists.txt - Build configuration

**Available testing frameworks**:
- Google Test (gtest) - for unit tests
- Integration test harness - for end-to-end transpilation tests
</context>

<plan_requirements>

## Phase Structure

Create a plan with 4-6 phases following strict TDD:
1. **Test Infrastructure Phase** - Set up testing scaffolding
2. **Failing Tests Phase** - Write tests that expose the bug
3. **Fix Implementation Phase** - Implement the fix to make tests pass
4. **Regression Prevention Phase** - Add tests for edge cases
5. **Integration Validation Phase** - Test with real-world code
6. **Cleanup & Documentation Phase** - Refactor and document

## For Each Phase

Include:

### 1. Objective
- What this phase accomplishes
- Why it comes in this order
- Success criteria

### 2. Pre-requisites
- What must be complete before starting
- Required files or setup
- Dependencies on previous phases

### 3. Test-First Tasks
**CRITICAL**: Tests MUST be written before implementation

<test_task>
**Task**: Write unit test for [specific behavior]
**File**: tests/unit/[TestFile].cpp
**Test cases**:
- [Specific test case 1]
- [Specific test case 2]
**Expected outcome**: Tests FAIL (bug not fixed yet)
</test_task>

### 4. Implementation Tasks
Only after tests are written and failing

<impl_task>
**Task**: Implement [specific fix]
**File**: src/[SourceFile].cpp:[line-range]
**Changes**:
- [Specific change 1]
- [Specific change 2]
**Validation**: Run tests from step 3, should now PASS
</impl_task>

### 5. Verification
- Commands to run tests
- Expected output
- How to confirm phase success

### 6. Rollback Plan
- How to undo changes if phase fails
- Which tests to check
- Safe stopping point

## Test Coverage Requirements

**Unit Tests** (tests/unit/):
- Pointer type handling in isolation
- Type comparison and caching
- Recursion depth limiting
- Type memoization (if applicable)

**Integration Tests** (tests/integration/):
- Simple pointer transpilation (int*)
- Nested pointers (int**, int***)
- Method pointers
- Const pointers
- Pointer-to-member functions
- Template pointers

**Regression Tests** (tests/regression/):
- Original test-point.cpp
- Real-world code samples
- Edge cases from research

**Performance Tests** (optional but recommended):
- Output size verification
- Transpilation time limits
- Memory usage checks

## Example Phase Format

```xml
<phase number="1" name="Test Infrastructure Setup">
<objective>
Set up Google Test framework for pointer type testing. Create test fixtures and utilities.
No implementation changes yet - pure test infrastructure.
</objective>

<prerequisites>
- Google Test dependency added to CMakeLists.txt
- tests/unit/ directory exists
</prerequisites>

<tasks>
<task type="test" order="1">
**Create**: tests/unit/PointerTypeHandlingTest.cpp
**Content**:
- Test fixture: PointerTypeTest with transpiler setup
- Helper: transpileCode(string cpp) → TranspileResult
- Helper: countWrapperFunctions(string c_code) → int
**Verify**: File compiles, test runner finds fixture
</task>

<task type="test" order="2">
**Create**: tests/unit/fixtures/simple-pointer.cpp
**Content**: Minimal test cases for pointer scenarios
**Verify**: Fixtures loadable by test framework
</task>
</tasks>

<verification>
```bash
cd build_working && cmake .. && make PointerTypeHandlingTest
./PointerTypeHandlingTest --gtest_list_tests
```
Expected: Test fixture listed, no tests run yet
</verification>

<rollback>
Delete tests/unit/PointerTypeHandlingTest.cpp if setup fails
</rollback>
</phase>
```

## Risk Mitigation

For each phase, identify:
- **High risk changes**: Files that affect core functionality
- **Mitigation**: How to minimize risk (feature flags, incremental changes)
- **Validation**: Extra testing for risky changes

## Timeline Estimation

Provide rough estimates (not hard deadlines):
- Phase 1: [X hours] - test setup
- Phase 2: [X hours] - failing tests
- Phase 3: [X hours] - implementation
- etc.

Total: [X hours/days]

</plan_requirements>

<output>
Create detailed plan at: `.prompts/037-pointer-bug-plan/pointer-bug-plan.md`

**Required structure**:

```xml
<plan_summary>
One paragraph overview of fix approach and phases
</plan_summary>

<phases>
<phase number="1" name="...">
[Full phase detail as shown above]
</phase>
<!-- Repeat for each phase -->
</phases>

<test_coverage_summary>
<unit_tests count="X">Brief description</unit_tests>
<integration_tests count="X">Brief description</integration_tests>
<regression_tests count="X">Brief description</regression_tests>
</test_coverage_summary>

<risk_assessment>
<high_risk_areas>
Files and changes with highest risk
</high_risk_areas>
<mitigation_strategies>
How risks are addressed
</mitigation_strategies>
</risk_assessment>

<dependencies>
What's needed before implementation (decisions, resources, etc.)
</dependencies>

<open_questions>
What remains uncertain
</open_questions>

<assumptions>
What was assumed during planning
</assumptions>

<confidence>High|Medium|Low</confidence>
</plan_summary>
```

Also create: `.prompts/037-pointer-bug-plan/SUMMARY.md`

**Required format**:

```markdown
# Pointer Bug Fix Plan Summary

**[One substantive sentence describing the fix approach and TDD strategy]**

## Key Phases
• Phase 1: [Name] - [One sentence description]
• Phase 2: [Name] - [One sentence description]
• Phase 3: [Name] - [One sentence description]
[etc.]

## Test Coverage
- Unit tests: [count] tests covering [what]
- Integration tests: [count] tests covering [what]
- Regression tests: [count] tests covering [what]

## Estimated Effort
[X] hours/days total across [Y] phases

## Decisions Needed
[What user needs to approve, or "None - ready to implement"]

## Blockers
[External impediments, or "None"]

## Next Step
Execute pointer-bug-implement.md following TDD strictly
```
</output>

<constraints>
- EVERY implementation task MUST have corresponding tests written FIRST
- Tests must FAIL before implementation (proving they test the bug)
- Tests must PASS after implementation (proving the fix works)
- No skipping TDD cycle - it's mandatory per CLAUDE.md
- Plan must be executable by autonomous agent without human intervention
- Each phase must be independently verifiable
</constraints>

<verification>
Before completing plan, verify:
- ✅ Every phase has test tasks BEFORE implementation tasks
- ✅ At least 15 test cases designed across unit/integration/regression
- ✅ Each task has clear success criteria
- ✅ Rollback plans provided for risky phases
- ✅ Risk mitigation strategies defined
- ✅ SUMMARY.md created with substantive one-liner
- ✅ Plan is executable without further research or decisions
</verification>

<success_criteria>
- Plan follows strict TDD: test → fail → implement → pass → refactor
- Test coverage is comprehensive (unit + integration + regression)
- Each phase is atomic and independently verifiable
- Rollback strategy exists for each phase
- SUMMARY.md enables quick understanding
- Ready for autonomous execution
</success_criteria>

# Research: Pointer Type Recursion Bug

<objective>
Conduct deep investigation into the infinite pointer type recursion bug discovered in the C++ to C transpiler. The bug causes exponential explosion of pointer-to-pointer wrapper functions, making transpiled output unusable.

**Why this matters**: This bug blocks all practical use of the transpiler. A simple Point class generates 4.4MB of output instead of ~1KB due to millions of recursive pointer wrapper functions.

**End goal**: Comprehensive understanding of root cause, affected components, and potential fix strategies for planning phase.
</objective>

<context>
**Known symptoms**:
- Simple C++ class with methods generates millions of wrapper functions
- Pattern: `Point_getX_ptr_ptr_ptr_ptr...` repeated thousands of times
- Output file size: 4.4MB+ for ~10 line class (should be ~1KB)
- No termination condition in pointer wrapper generation

**Test case** (test-point.cpp):
```cpp
class Point {
public:
    int x, y;
    Point(int x, int y) : x(x), y(y) {}
    int getX() const { return x; }
    int getY() const { return y; }
};
```

**Project structure**:
@src/CppToCVisitor.cpp - Main visitor that translates C++ AST to C
@src/CodeGenerator.cpp - Generates C code from intermediate representation
@src/TranspilerAPI.cpp - API layer
@include/CNodeBuilder.h - C code AST builder
@CLAUDE.md - Project conventions

**Previous investigation**:
@test-logs/transpiler-regression-analysis.md - Initial findings
@test-logs/transpiler-fix-validation.txt - Validation results
</context>

<research_requirements>

## Phase 1: Code Path Analysis

**1. Trace pointer type handling**:
- Use `grep -r "ptr_" src/ include/` to find all pointer-related code
- Identify where pointer wrapper functions are generated
- Map the call stack from AST visitor to code generation
- Find recursion entry point and why it doesn't terminate

**2. Examine type system**:
- How are C++ pointer types represented internally?
- How are they converted to C equivalents?
- Is there a type cache or memoization?
- Where should recursion stop but doesn't?

**3. Review related components**:
- Template handling (might interact with pointers)
- Function signature generation
- Method pointer handling
- Type mangling logic

## Phase 2: Root Cause Identification

**Investigate these hypotheses** (test each thoroughly):

1. **Missing termination condition**:
   - Is there supposed to be a depth limit?
   - Is there a visited types set that's broken?
   - Is recursion detection bypassed for certain cases?

2. **Type identity bug**:
   - Are `int*` and `int**` incorrectly treated as distinct needing separate wrappers?
   - Is type comparison using pointer equality instead of structural equality?
   - Is there a hash collision in type caching?

3. **Function pointer confusion**:
   - Are method pointers (`int (Point::*)()`) triggering wrapper generation?
   - Is const-correctness creating infinite type variants?
   - Are return type pointers creating cascading wrapper needs?

4. **Template interaction**:
   - Is template monomorphization generating pointer type variants?
   - Are template type parameters with pointers handled incorrectly?

**For each hypothesis**:
- Write test to verify/disprove
- Document evidence found
- Assign confidence level (High/Medium/Low)

## Phase 3: Fix Strategy Analysis

**Evaluate potential fixes**:

1. **Add recursion depth limit**:
   - Pros: Quick fix, prevents infinite loops
   - Cons: Might hide underlying issue, arbitrary limit
   - Complexity: Low
   - Risk: Low

2. **Implement type memoization**:
   - Pros: Prevents duplicate wrapper generation
   - Cons: Requires careful cache key design
   - Complexity: Medium
   - Risk: Medium (cache invalidation issues)

3. **Refactor pointer handling architecture**:
   - Pros: Fixes root cause, enables future improvements
   - Cons: Large change, higher risk
   - Complexity: High
   - Risk: High (might break other features)

4. **Disable pointer wrappers**:
   - Pros: Immediate workaround
   - Cons: Might break pointer-dependent features
   - Complexity: Low
   - Risk: Medium

**For each strategy**:
- Identify files that need changes
- Estimate lines of code affected
- List affected features/tests
- Note migration/rollback plan

## Phase 4: Test Case Design

**Design comprehensive test cases** for validation:

1. **Simple pointer tests**:
   - `int* ptr`
   - `int** ptrptr`
   - `int*** triple`

2. **Method pointer tests**:
   - `int (Point::*methodPtr)()`
   - `const int* getPtr() const`

3. **Pointer in templates**:
   - `vector<int*>`
   - `unique_ptr<T>`

4. **Edge cases**:
   - Function returning pointer to function
   - Pointer to member function
   - Void pointers
   - Null pointers

</research_requirements>

<output>
Create comprehensive research output at: `.prompts/036-pointer-bug-research/pointer-bug-research.md`

**Required structure**:

```xml
<research_summary>
One paragraph executive summary of findings
</research_summary>

<root_cause>
Detailed explanation of what causes the bug

<evidence>
Code snippets, test results, call stacks proving the root cause
</evidence>

<affected_components>
List of files/classes/functions involved with line numbers
</affected_components>
</root_cause>

<hypothesis_results>
<hypothesis name="missing-termination" confidence="High|Medium|Low">
Findings and evidence
</hypothesis>
<!-- Repeat for each hypothesis -->
</hypothesis_results>

<fix_strategies>
<strategy name="recursion-limit" recommendation="Recommended|Consider|Not Recommended">
<pros>...</pros>
<cons>...</cons>
<complexity>Low|Medium|High</complexity>
<risk>Low|Medium|High</risk>
<files_affected>List with line numbers</files_affected>
</strategy>
<!-- Repeat for each strategy -->
</fix_strategies>

<test_cases>
Comprehensive test case design for TDD
<unit_tests>...</unit_tests>
<integration_tests>...</integration_tests>
<regression_tests>...</regression_tests>
</test_cases>

<dependencies>
What's needed to proceed with planning (e.g., decisions, clarifications)
</dependencies>

<open_questions>
What remains uncertain or needs user input
</open_questions>

<assumptions>
What was assumed during research
</assumptions>

<confidence>High|Medium|Low - overall confidence in findings</confidence>
</research_summary>
```

Also create: `.prompts/036-pointer-bug-research/SUMMARY.md`

**Required format**:

```markdown
# Pointer Bug Research Summary

**[One substantive sentence describing the root cause]**

## Key Findings
• [Bullet 1: Most important finding]
• [Bullet 2: Second most important]
• [Bullet 3: Third most important]

## Root Cause
[2-3 sentences explaining what's broken]

## Recommended Fix Strategy
[Name of recommended strategy with 1-sentence rationale]

## Decisions Needed
[What user needs to decide, or "None - ready for planning"]

## Blockers
[External impediments, or "None"]

## Next Step
Create pointer-bug-plan.md with [specific focus based on findings]
```
</output>

<constraints>
- Do NOT modify any transpiler code yet - this is research only
- Do NOT skip hypothesis testing - test each one thoroughly
- Use git history to understand why current implementation exists
- Check for related issues in comments or TODOs
- Verify findings with multiple test cases
- Document ALL evidence (code snippets, test outputs, git commits)
</constraints>

<verification>
Before completing research, verify:
- ✅ Root cause identified with high confidence
- ✅ At least 3 hypotheses tested
- ✅ Each fix strategy evaluated with pros/cons
- ✅ Test cases cover simple, complex, and edge case scenarios
- ✅ All affected files identified with line numbers
- ✅ Evidence documented (code snippets, test outputs)
- ✅ SUMMARY.md created with substantive one-liner
- ✅ Dependencies and open questions clearly stated
</verification>

<success_criteria>
- Root cause understood at architectural level
- Fix strategies compared with clear recommendation
- Test case design ready for TDD implementation
- SUMMARY.md enables quick understanding without reading full research
- Ready to create detailed implementation plan
</success_criteria>

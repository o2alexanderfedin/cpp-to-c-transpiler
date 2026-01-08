<objective>
Conduct a comprehensive audit of the current multiple inheritance and virtual inheritance implementation in the C++ to C transpiler. This audit will inform subsequent implementation and testing efforts.

The goal is to produce a detailed assessment of:
- What handler infrastructure exists for multiple and virtual inheritance
- How well it's integrated into the 3-stage pipeline (C++ AST → C AST → C Source)
- What gaps exist in implementation and testing
- Concrete recommendations for completing the implementation
</objective>

<context>
This is a C++ to C transpiler built with Clang's AST infrastructure. The project follows:
- **3-stage pipeline architecture**: C++ AST → Handler Chain → C AST → C Code
- **TDD practices**: Tests written before implementation, comprehensive coverage required
- **SOLID principles**: Single responsibility, handler-based dispatch system

Read @CLAUDE.md for detailed architecture and conventions.

Known infrastructure (from initial investigation):
- `include/VirtualInheritanceAnalyzer.h` - Virtual base detection
- `VirtualBaseDetectionTest` - Detection tests
- `VirtualBaseOffsetTableTest` - Offset table tests
- `VTTGeneratorTest` - VTT generation tests
- Multiple inheritance analyzer exists

The TODO item states:
- Currently marked as "ON (not implemented)" in runtime configuration
- Need to track virtual bases separately from direct bases
- Need to emit offset adjustments in derived class constructors
- Need to modify vtable generation to include virtual base offsets
</context>

<research>
Thoroughly investigate the following areas. For maximum efficiency, whenever you need to perform multiple independent operations, invoke all relevant tools simultaneously rather than sequentially.

1. **Handler Infrastructure**:
   - Search for all files related to inheritance handling (multiple and virtual)
   - Examine handler dispatch integration (are handlers registered properly?)
   - Check if handlers follow the established patterns (see other handlers in `src/dispatch/`)

2. **Test Coverage Assessment**:
   - Unit tests: What components have unit tests? What's missing?
   - Integration tests: Are there tests for handler interactions?
   - E2E tests: Are there end-to-end transpilation tests with real C++ code?

3. **Implementation Completeness**:
   - VTable generation: Does it support virtual base offsets?
   - Constructor handling: Are offset adjustments emitted?
   - Runtime configuration: What does "ON (not implemented)" mean?
   - C AST generation: Are virtual inheritance constructs properly represented?

4. **Gap Analysis**:
   - Compare against working handlers (e.g., virtual method handlers)
   - Identify missing pieces in the handler chain
   - Check for TODOs or FIXMEs related to inheritance
</research>

<investigation_steps>
1. Map the current inheritance handler architecture
   - Find all relevant source files (use Grep with patterns: "virtual.*inherit", "multiple.*inherit", "VirtualBase", "diamond")
   - Read key files to understand current implementation state
   - Document the handler registration and dispatch flow

2. Assess test infrastructure
   - List all existing tests (unit, integration, E2E)
   - For each test, note: what it covers, what passes/fails, what's marked as "not yet implemented"
   - Identify testing gaps by comparing to similar features (e.g., virtual method tests)

3. Review runtime configuration
   - Find where "ON (not implemented)" is defined
   - Understand what needs to happen to mark it as "implemented"
   - Check if there are runtime flags or feature toggles

4. Analyze C AST representation
   - How are virtual bases represented in the C AST?
   - How are vtable structures defined for virtual inheritance?
   - Are there examples of correct C output for virtual inheritance?

5. Study existing working handlers
   - Read 2-3 well-implemented handlers (e.g., VirtualMethodHandler, RecordHandler)
   - Note the patterns they follow
   - Compare inheritance handlers against these patterns
</investigation_steps>

<output>
Create a comprehensive audit report:

Save to: `./audit-reports/inheritance-handlers-audit.md`

Structure:
```markdown
# Multiple and Virtual Inheritance Handler Audit

## Executive Summary
[3-5 bullet points: current state, major gaps, effort estimate]

## Current Implementation

### Handler Infrastructure
- Files found: [list with brief descriptions]
- Handler dispatch integration: [status]
- Follows established patterns: [yes/no with details]

### Test Coverage
#### Unit Tests
- Existing: [list with status]
- Missing: [list with priority]

#### Integration Tests
- Existing: [list with status]
- Missing: [list with priority]

#### E2E Tests
- Existing: [list with status]
- Missing: [list with priority]

### Implementation Completeness
- VTable generation: [status and gaps]
- Constructor handling: [status and gaps]
- Runtime configuration: [current state]
- C AST representation: [status and gaps]

## Gap Analysis

### Critical Gaps (must fix)
1. [Gap description]
   - Impact: [what breaks without this]
   - Files affected: [list]
   - Estimated effort: [hours/story points]

### Important Gaps (should fix)
[Same structure as critical]

### Nice-to-have Improvements
[Same structure]

## Recommendations

### Implementation Priority
1. [High priority item] - Why: [reasoning]
2. [Medium priority item] - Why: [reasoning]
3. [Low priority item] - Why: [reasoning]

### Testing Strategy
- Unit test approach: [description]
- Integration test approach: [description]
- E2E test scenarios: [list of real-world cases to test]

### Integration Points
[Which parts of the codebase need updates to integrate completed handlers]

## Next Steps
1. [Concrete actionable step]
2. [Concrete actionable step]
3. [Concrete actionable step]
```
</output>

<success_criteria>
Before declaring this audit complete, verify:

- ✅ All relevant source files identified and analyzed
- ✅ Test coverage comprehensively assessed (unit, integration, E2E)
- ✅ Implementation gaps clearly identified with impact analysis
- ✅ Recommendations are specific, actionable, and prioritized
- ✅ Audit report saved to `./audit-reports/inheritance-handlers-audit.md`
- ✅ Report includes concrete next steps for implementation phase
- ✅ Cross-referenced with working handlers to ensure consistency with established patterns
</success_criteria>

<verification>
After completing the audit:

1. Review the audit report for completeness
2. Ensure recommendations are backed by evidence from the investigation
3. Verify that all gaps have estimated effort and impact
4. Confirm the testing strategy aligns with project's TDD practices
5. Check that next steps are concrete and executable
</verification>

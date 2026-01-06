# C++23 Feature Support Implementation Plan

## Objective

Create a comprehensive, phased implementation plan for adding C++23 feature support to the cpptoc transpiler, addressing the 25% of Phase 33 failures caused by missing C++23 feature transformation visitors.

**Target**: Improve C++23 support from **0%** to **20-25%** through systematic implementation of critical language features.

**Why this matters**: Pipeline verification research (043) identified that while the three-stage pipeline is architecturally sound, we lack transformation visitors for C++23-specific language features. This plan will provide a clear roadmap for incrementally adding these features while maintaining code quality and architectural consistency.

## Context

**Reference pipeline verification research**:
- @.prompts/043-pipeline-verification-research/pipeline-verification-research.md
- @.prompts/043-pipeline-verification-research/SUMMARY.md

**Key findings from research**:
1. Pipeline architecture is 95% correct (Stage 1 and 3 fully implemented)
2. Stage 2 transformation is partial - missing C++23 feature visitors (25% impact)
3. Header file skipping accounts for 70% of failures (separate issue)
4. Existing RecursiveASTVisitor pattern works well for C++11/14 features
5. CNodeBuilder successfully constructs C AST nodes

**Architecture constraints**:
- Must integrate with RecursiveASTVisitor pattern in CppToCVisitor
- Must use CNodeBuilder for C AST node construction
- Must maintain C99 output compatibility
- Should follow existing transformation patterns (classes→structs, vtables, etc.)

**Existing successful transformations** (to learn from):
- Classes → Structs (VisitCXXRecordDecl)
- Virtual functions → Vtables (VirtualMethodAnalyzer, VtableGenerator)
- Templates → Monomorphization (TemplateExtractor)
- Exceptions → setjmp/longjmp (TryCatchTransformer)

## Requirements

### C++23 Features to Implement

Based on Phase 33 test failures and C++23 standard:

#### Priority 1: High Impact (Must Have)
1. **Deducing this (P0847R7)** - 22 tests
   - Explicit object parameter syntax
   - Template deduction for `this`
   - Transformation challenge: Expand to const/non-const/rvalue overloads

2. **if consteval (P1938R3)** - 13 tests
   - Compile-time vs runtime branch selection
   - Transformation challenge: Evaluate at transpile-time or emit runtime equivalent

3. **Multidimensional subscript operator (P2128R6)** - 16 tests
   - `operator[](T1, T2, ...)` with multiple arguments
   - Transformation challenge: Convert to named function with multiple parameters

#### Priority 2: Medium Impact (Should Have)
4. **Static operator() and operator[] (P1169R4)** - 8 tests
   - Static member operators
   - Transformation challenge: Convert to static free functions

5. **auto(x) and auto{x} decay-copy (P0849R8)** - 22 tests (partial support)
   - Decay-copy semantics
   - Transformation challenge: Proper type decay and copy construction

#### Priority 3: Lower Impact (Nice to Have)
6. **[[assume]] attribute (P1774R8)** - 13 tests
   - Compiler hint attribute
   - Transformation challenge: Strip or convert to C equivalent

7. **Constexpr enhancements** - 19 tests
   - Extended constexpr contexts
   - Transformation challenge: Compile-time evaluation or runtime fallback

8. **CTAD with inherited constructors (P2582R1)** - 10 tests (partial support)
   - Class template argument deduction
   - Transformation challenge: Enhanced type inference

### Implementation Phases

Create **4-6 implementation phases**, each delivering working transformations for 1-2 features.

**Phase structure** (for each):
1. **Research & Design** (20% of phase time)
   - Study C++23 feature specification
   - Design C transformation strategy
   - Identify AST patterns to match
   - Plan testing approach

2. **Visitor Implementation** (30% of phase time)
   - Add new Visit methods to CppToCVisitor
   - Implement AST node matching
   - Call appropriate transformation handlers

3. **Transformation Logic** (30% of phase time)
   - Create transformation classes (e.g., DeducingThisTranslator)
   - Implement C AST construction via CNodeBuilder
   - Handle edge cases and error conditions

4. **Testing & Validation** (20% of phase time)
   - Write unit tests
   - Run relevant Phase 33 tests
   - Validate C output correctness
   - A/B test against C++ version

**Each phase should**:
- Take 1-2 weeks maximum
- Increase C++23 support by 3-5%
- Include full test coverage
- Be independently committable
- Not break existing functionality

### Architecture Integration Points

**Key files to modify/extend**:
- `include/CppToCVisitor.h` - Add new Visit method declarations
- `src/CppToCVisitor.cpp` - Implement Visit methods, route to handlers
- `include/CNodeBuilder.h` - Extend if new C AST patterns needed
- New files: `include/{Feature}Translator.h`, `src/{Feature}Translator.cpp`

**Pattern to follow** (from existing code):
```cpp
// In CppToCVisitor.h
class CppToCVisitor : public RecursiveASTVisitor<CppToCVisitor> {
  // Add new visitor method
  bool VisitFeatureDecl(clang::FeatureDecl *D);

  // Add handler member
  std::unique_ptr<FeatureTranslator> FeatureHandler;
};

// In CppToCVisitor.cpp
bool CppToCVisitor::VisitFeatureDecl(clang::FeatureDecl *D) {
  if (!Context.getSourceManager().isInMainFile(D->getLocation())) {
    return true;  // Skip headers (for now)
  }

  // Use handler to transform
  auto C_Decl = FeatureHandler->transform(D, Context, C_TU);
  if (C_Decl) {
    C_TU->addDeclaration(C_Decl);
  }
  return true;
}

// In FeatureTranslator.cpp
Decl* FeatureTranslator::transform(FeatureDecl *D, ASTContext &Ctx, C_TranslationUnit *C_TU) {
  // Use CNodeBuilder to create C AST nodes
  auto C_Struct = CNodeBuilder::createStruct(/*...*/);
  // Add transformed elements
  return C_Struct;
}
```

### Success Metrics

**Overall goal**: 0% → 20-25% C++23 support by end of all phases

**Per-phase metrics**:
- Test pass rate increase: +3-5% per phase
- Code coverage: 80%+ for new transformation code
- No regression: All existing tests still pass
- Build time impact: <10% increase
- C output validation: Valid C99, compiles without warnings

**Quality gates**:
- All unit tests pass
- Relevant Phase 33 tests pass
- A/B testing shows correct output
- Code review approved
- Documentation updated

## Planning Requirements

### Phase Breakdown

For each implementation phase, provide:

1. **Phase identifier**: (e.g., "Phase 1: Deducing This Support")
2. **Features included**: Which C++23 features
3. **Estimated effort**: Time estimate in days/weeks
4. **Dependencies**: What must be done first
5. **Technical approach**: High-level transformation strategy
6. **Files to create/modify**: Specific file changes
7. **Testing strategy**: How to validate
8. **Risk assessment**: What could go wrong
9. **Success criteria**: How to know it's done

### Prioritization Criteria

Consider when ordering phases:
- **Test coverage impact**: Features with more Phase 33 tests first
- **Complexity**: Start with simpler transformations
- **Dependencies**: Features that enable others go first
- **User value**: Most requested features prioritized
- **Risk**: De-risk complex features early

### Implementation Patterns

Document for each feature:
- **C++ syntax**: What the feature looks like in C++
- **C equivalent**: What it should become in C
- **AST pattern**: What Clang AST nodes to match
- **Transformation steps**: How to convert
- **Edge cases**: Special handling needed
- **Examples**: Before/after code samples

## Output Specification

Save the complete plan to: `.prompts/044-cpp23-feature-support-plan/cpp23-feature-support-plan.md`

Use XML structure for machine readability:

```xml
<plan>
  <metadata>
    <created>YYYY-MM-DD</created>
    <author>Claude Sonnet 4.5</author>
    <version>1.0</version>
    <estimated_duration>Total time for all phases</estimated_duration>
  </metadata>

  <overview>
    <current_support>0%</current_support>
    <target_support>20-25%</target_support>
    <total_phases>4-6</total_phases>
    <features_covered>8 C++23 features</features_covered>
  </overview>

  <phase id="1" name="Phase Name">
    <features>
      <feature name="Deducing This" proposal="P0847R7" priority="high">
        <test_count>22</test_count>
        <complexity>high</complexity>
      </feature>
    </features>

    <effort>
      <estimated_days>10-14</estimated_days>
      <research>2 days</research>
      <implementation>6 days</implementation>
      <testing>2 days</testing>
    </effort>

    <dependencies>
      <dependency>Pipeline verification research complete</dependency>
    </dependencies>

    <technical_approach>
      <strategy>High-level transformation strategy</strategy>
      <ast_patterns>
        <pattern>Clang AST nodes to match</pattern>
      </ast_patterns>
      <transformation_steps>
        <step>1. Detect explicit object parameter</step>
        <step>2. Expand to const/non-const/rvalue overloads</step>
        <step>3. Generate C function signatures</step>
      </transformation_steps>
      <c_equivalent>
        <before>
          <![CDATA[
          struct S {
              template<typename Self>
              auto&& get(this Self&& self) { return self.data; }
          };
          ]]>
        </before>
        <after>
          <![CDATA[
          int* S_get(struct S* self);
          const int* S_get_const(const struct S* self);
          ]]>
        </after>
      </c_equivalent>
    </technical_approach>

    <implementation>
      <files_to_create>
        <file>include/DeducingThisTranslator.h</file>
        <file>src/DeducingThisTranslator.cpp</file>
      </files_to_create>
      <files_to_modify>
        <file>include/CppToCVisitor.h - Add VisitExplicitObjectParamDecl</file>
        <file>src/CppToCVisitor.cpp - Route to DeducingThisTranslator</file>
      </files_to_modify>
    </implementation>

    <testing>
      <unit_tests>
        <test>tests/DeducingThisTranslatorTest.cpp</test>
      </unit_tests>
      <integration_tests>
        <test>Phase 33: auto-deduction-P0849 (relevant subset)</test>
      </integration_tests>
      <validation_strategy>A/B test against C++ reference implementation</validation_strategy>
    </testing>

    <risks>
      <risk severity="high">
        <description>Template expansion complexity</description>
        <mitigation>Start with non-template cases, expand incrementally</mitigation>
      </risk>
    </risks>

    <success_criteria>
      <criterion>All DeducingThisTranslator tests pass</criterion>
      <criterion>At least 10/22 deducing-this Phase 33 tests pass</criterion>
      <criterion>C++23 support increases to 4-5%</criterion>
      <criterion>No regression in existing tests</criterion>
    </success_criteria>

    <deliverables>
      <deliverable>DeducingThisTranslator implementation</deliverable>
      <deliverable>Unit tests with 80%+ coverage</deliverable>
      <deliverable>Documentation updates</deliverable>
      <deliverable>Phase 33 test results</deliverable>
    </deliverables>
  </phase>

  <!-- Repeat <phase> blocks for all phases -->

  <overall_strategy>
    <prioritization>
      High-impact features first (deducing this, if consteval, multidim subscript)
      Then medium-impact (static operators, auto decay-copy)
      Then lower-impact (attributes, constexpr enhancements)
    </prioritization>

    <risk_mitigation>
      <strategy>Incremental delivery - each phase standalone</strategy>
      <strategy>Comprehensive testing - unit + integration + A/B</strategy>
      <strategy>Code review gates - architectural approval required</strategy>
    </risk_mitigation>

    <quality_assurance>
      <requirement>All phases maintain 80%+ test coverage</requirement>
      <requirement>C output must compile with gcc -std=c99 -Wall -Werror</requirement>
      <requirement>Performance: <10% build time increase per phase</requirement>
    </quality_assurance>
  </overall_strategy>

  <timeline>
    <phase id="1" start="Week 1" end="Week 2-3"/>
    <phase id="2" start="Week 3-4" end="Week 5-6"/>
    <!-- etc -->
    <total_duration>12-18 weeks for complete implementation</total_duration>
  </timeline>

  <resource_requirements>
    <developer_time>Full-time: 12-18 weeks</developer_time>
    <testing_resources>Phase 33 test suite, A/B framework</testing_resources>
    <tools>Clang LibTooling, CNodeBuilder, existing test infrastructure</tools>
  </resource_requirements>

  <confidence>high | medium | low</confidence>
  <dependencies>
    <dependency>Pipeline verification research complete (✓)</dependency>
    <dependency>Phase 33 test suite available (✓)</dependency>
    <dependency>CNodeBuilder infrastructure stable (✓)</dependency>
  </dependencies>
  <open_questions>
    <question>Should we address header file skipping (70% impact) before or after C++23 features?</question>
    <question>What is the priority order between different C++23 features from user perspective?</question>
  </open_questions>
  <assumptions>
    <assumption>Existing RecursiveASTVisitor pattern will scale to C++23 features</assumption>
    <assumption>CNodeBuilder can represent all needed C constructs</assumption>
    <assumption>20-25% support is valuable to users (vs 100% or nothing)</assumption>
  </assumptions>
</plan>
```

## Planning Strategy

### Phase 1: Feature Prioritization and Research
1. Review Phase 33 test failures by feature
2. Analyze C++23 feature specifications
3. Estimate transformation complexity
4. Prioritize by (test_count × ease_of_implementation)

### Phase 2: Architecture Design
1. Design visitor integration points
2. Plan CNodeBuilder extensions if needed
3. Define transformation handler interfaces
4. Create example transformations for each feature

### Phase 3: Phased Roadmap
1. Group features into logical phases (1-2 features per phase)
2. Sequence phases by dependencies and complexity
3. Define success criteria and testing strategy per phase
4. Estimate effort and timeline

### Phase 4: Risk and Mitigation
1. Identify technical risks per phase
2. Plan mitigation strategies
3. Define fallback options if transformations prove too complex
4. Establish quality gates

## SUMMARY.md Requirement

After completing the plan, create `.prompts/044-cpp23-feature-support-plan/SUMMARY.md` with:

**One-liner**: Substantive description (e.g., "6-phase roadmap to add C++23 feature support, targeting 20-25% coverage through incremental visitor implementation")

**Version**: v1

**Key Findings**:
- Number of phases and features per phase
- Total estimated timeline
- Major technical approaches
- Risk areas

**Decisions Needed**:
- Feature prioritization approval
- Resource allocation (timeline acceptable?)
- Header file skipping: address first or defer?

**Blockers**:
- External impediments (if any)

**Next Step**:
- Concrete forward action (e.g., "Begin Phase 1 implementation: Deducing This support")

## Success Criteria

This plan is successful when:
1. All 8 C++23 features have transformation strategies defined
2. Features are grouped into 4-6 logical implementation phases
3. Each phase has clear deliverables and success criteria
4. Timeline is realistic (12-18 weeks total)
5. Technical approach is architecturally sound
6. Risk mitigation strategies are in place
7. SUMMARY.md provides executive-level clarity
8. Plan is actionable - implementer can start immediately on Phase 1

## Quality Controls

### Verification Checklist
Before submitting plan:
- [ ] All 8 C++23 features addressed
- [ ] Phases have realistic effort estimates
- [ ] Technical approaches are specific (not hand-waving)
- [ ] Code examples provided for transformations
- [ ] Testing strategy defined per phase
- [ ] Risks identified with mitigations
- [ ] Dependencies and sequencing make sense

### Sources to Consult
1. **Pipeline verification research** (@043-pipeline-verification-research/)
2. **C++23 proposals**: P0847R7, P1938R3, P2128R6, P1169R4, P0849R8, P1774R8, P2582R1
3. **Existing transformation code**: CppToCVisitor.cpp, VtableGenerator, TemplateExtractor
4. **Phase 33 test suite**: tests/real-world/cpp23-validation/gcc-adapted/
5. **Clang AST documentation**: https://clang.llvm.org/doxygen/

### QA Questions
Before finalizing:
1. Can an implementer start Phase 1 immediately after reading this plan?
2. Are the transformation strategies technically feasible?
3. Is the 20-25% support target achievable with these 8 features?
4. Have we learned from existing successful transformations?
5. Are phases independently deliverable (can we stop after any phase)?

## Additional Considerations

### Trade-offs to Address

**Incremental vs Big Bang**:
- ✅ Recommended: Incremental phases (safer, testable)
- ❌ Avoid: Implementing all features at once (risky)

**Perfection vs Progress**:
- Partial support for many features > Perfect support for one feature
- Goal is 20-25%, not 100%

**Header Files**:
- C++23 features AND header file support = two separate problems
- This plan addresses C++23 features only
- Header file skipping (70% impact) is a separate initiative

### Integration with Existing Work

Reference these successfully implemented transformations:
- Classes → Structs: CppToCVisitor.cpp:108 (VisitCXXRecordDecl)
- Virtual functions: VirtualMethodAnalyzer, VtableGenerator
- Templates: TemplateExtractor, TemplateMonomorphizer
- Exceptions: TryCatchTransformer
- RTTI: TypeidTranslator, DynamicCastTranslator

Learn from their patterns:
1. AST node matching in Visit methods
2. Delegation to specialized translators
3. C AST construction via CNodeBuilder
4. Comprehensive unit testing

---

**Begin planning now. Create a detailed, actionable roadmap that an implementer can execute immediately.**

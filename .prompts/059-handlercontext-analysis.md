<objective>
Thoroughly analyze HandlerContext to determine if it's actually needed or if CppToCVisitorDispatcher already provides equivalent functionality (possibly in limited form). This analysis is critical before refactoring E2E tests to ensure we don't duplicate functionality that already exists.

Produce a detailed, comprehensive report with concrete evidence from the codebase.
</objective>

<context>
The transpiler has migrated from instance-based ASTHandler pattern to static CppToCVisitorDispatcher pattern. The core library now uses CppToCVisitorDispatcher exclusively, but many E2E tests still use HandlerContext.

**Current Architecture:**
- Modern: CppToCVisitorDispatcher (include/dispatch/CppToCVisitorDispatcher.h)
  - Static handler registration and dispatch
  - Provides: DeclMapper, TypeMapper, StmtMapper, PathMapper
  - Target path resolution via getTargetPath()

- Legacy: HandlerContext (include/handlers/HandlerContext.h)
  - Used by E2E tests
  - Purpose unclear - may overlap with dispatcher functionality

**Critical Question:** Does HandlerContext provide anything that CppToCVisitorDispatcher doesn't? Or can E2E tests be refactored to use CppToCVisitorDispatcher directly?

**Files to examine:**
@include/handlers/HandlerContext.h
@src/handlers/HandlerContext.cpp
@include/dispatch/CppToCVisitorDispatcher.h
@src/dispatch/CppToCVisitorDispatcher.cpp
@include/mapping/DeclMapper.h
@include/mapping/TypeMapper.h
@include/mapping/StmtMapper.h
@include/mapping/PathMapper.h

**Test files using HandlerContext:**
@tests/e2e/phase1/E2EPhase1Test.cpp
@tests/e2e/phase2/ControlFlowE2ETest.cpp
@tests/e2e/phase3/GlobalVariablesE2ETest.cpp
@tests/e2e/phase4/PointersE2ETest.cpp
@tests/e2e/phase5/StructsE2ETest.cpp
</context>

<analysis_requirements>
Perform a thorough, systematic analysis with these steps:

## 1. HandlerContext API Analysis
Read HandlerContext header and implementation. Document:
- Every public method it provides
- Every private member variable it maintains
- Dependencies on other classes
- Usage patterns (how methods are called together)

## 2. CppToCVisitorDispatcher API Analysis
Read CppToCVisitorDispatcher header and implementation. Document:
- Every public method it provides
- Every mapper it manages (DeclMapper, TypeMapper, StmtMapper, PathMapper)
- Dependencies on other classes
- How handlers access functionality through it

## 3. Mapper Classes Analysis
Read all mapper headers (DeclMapper, TypeMapper, StmtMapper, PathMapper). Document:
- What functionality each mapper provides
- How they store mappings (C++ → C)
- Any functionality HandlerContext might duplicate

## 4. Feature-by-Feature Comparison
Create a comparison table:

| Feature | HandlerContext | CppToCVisitorDispatcher | Verdict |
|---------|----------------|-------------------------|---------|
| [Feature name] | [How HC provides it] | [How Dispatcher provides it / Not provided] | [Duplicate/Unique/Missing] |

Include ALL features from both classes.

## 5. E2E Test Usage Patterns
Examine E2E test files. Document:
- How they instantiate HandlerContext
- Which HandlerContext methods they call
- What they're trying to accomplish
- Whether CppToCVisitorDispatcher could accomplish the same thing

## 6. Migration Feasibility Assessment
For each unique HandlerContext feature:
- Can it be added to CppToCVisitorDispatcher? (Yes/No + reasoning)
- What would the migration path look like?
- Are there architectural reasons to keep HandlerContext separate?

## 7. Concrete Code Examples
Provide side-by-side code examples showing:
- Current E2E test pattern using HandlerContext
- Proposed equivalent using CppToCVisitorDispatcher
- Identify any gaps or missing functionality

## 8. Recommendations
Based on evidence, provide clear recommendations:
- Should HandlerContext be retired? (Yes/No + detailed reasoning)
- If yes: Migration strategy with concrete steps
- If no: Why HandlerContext is architecturally necessary
- Any middle-ground options (e.g., slim down HandlerContext, extend dispatcher)
</analysis_requirements>

<research_approach>
Use parallel tool calling for maximum efficiency:
1. Read all headers in parallel (HandlerContext.h, CppToCVisitorDispatcher.h, all mapper headers)
2. Read all implementations in parallel
3. Read representative E2E test files in parallel

After gathering data, deeply consider:
- Design principles: Are we duplicating abstractions?
- SOLID principles: Does having both violate SRP or ISP?
- Maintenance burden: What's the cost of keeping both?
- Migration risk: What could break if we remove HandlerContext?
</research_approach>

<output_format>
Create a comprehensive markdown report saved to:
`./analyses/handlercontext-vs-dispatcher-analysis.md`

The report must include:

## Executive Summary
- 1-paragraph verdict with clear recommendation
- Key findings (3-5 bullet points)

## Detailed Analysis
All 8 sections from analysis_requirements above with concrete evidence

## Appendices
- A: Full HandlerContext API reference
- B: Full CppToCVisitorDispatcher API reference
- C: Migration code examples (if recommending retirement)

Use tables, code blocks, and examples extensively. This is a critical architectural decision - be thorough.
</output_format>

<verification>
Before completing, verify:
- ✅ Read ALL mentioned header and implementation files
- ✅ Examined at least 3 E2E test files thoroughly
- ✅ Created feature comparison table with concrete evidence
- ✅ Provided code examples (not just descriptions)
- ✅ Clear recommendation with reasoning
- ✅ If recommending retirement: migration path is concrete and actionable
- ✅ If recommending retention: architectural justification is solid
- ✅ Report saved to ./analyses/handlercontext-vs-dispatcher-analysis.md
</verification>

<success_criteria>
- Analysis is evidence-based with concrete code references
- Every claim is backed by file:line references
- Feature comparison table is exhaustive
- Code examples demonstrate feasibility (or infeasibility) of migration
- Recommendation is actionable with clear next steps
- Report can be used by another developer to make the architectural decision
</success_criteria>

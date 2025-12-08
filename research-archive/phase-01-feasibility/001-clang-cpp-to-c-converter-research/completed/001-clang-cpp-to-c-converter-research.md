<research_objective>
Research the technical feasibility and implementation approach for building a Clang-based tool that converts contemporary C++ code (C++11/14/17/20/23 with all features) to human-readable, compilable C code with `#line` directives for source mapping.

The goal is to determine:
1. **Where to intercept** in Clang's compilation pipeline (AST vs CodeGen phase)
2. **How to handle modern C++ features** (templates, RAII, exceptions, STL, lambdas, etc.)
3. **What existing tools/techniques** can be leveraged or learned from
4. **What implementation strategy** is most viable for generating readable C code

This research will inform whether this approach is technically feasible and provide a concrete roadmap for implementation.
</research_objective>

<context>
**Background context:**
- Previous research (./research/cpp-to-c-conversion-tools.md) found NO production-ready C++ to C converters
- LLVM-CBE exists but generates unreadable machine code
- The hypothesis: Intercept at Clang AST level (before LLVM IR) to preserve high-level structure
- Target: Full modern C++ support with human-readable C output

**Technical constraints:**
- Must use Clang frontend (leverage existing C++ parsing)
- Must emit compilable C code (valid C99 or C11)
- Must include `#line` directives for source mapping
- Must handle ALL contemporary C++ features (ambitious goal)

**User context:**
- Target audience is Claude Code CLI (can handle technical depth)
- Open to expert-level Clang/LLVM implementation details
</context>

<research_process>
This research requires DEEP technical investigation across multiple domains. Approach systematically:

### Phase 1: Clang Architecture Deep Dive

**Understand the compilation pipeline:**
1. Parse Clang documentation on compilation phases:
   - Lexer → Parser → AST → Sema (semantic analysis) → CodeGen → LLVM IR
2. Identify WHERE to intercept for C code generation:
   - Option A: AST traversal (after Sema, before CodeGen)
   - Option B: Custom CodeGen consumer (replace LLVM IR emission)
   - Option C: Hybrid approach
3. Research Clang Plugin architecture vs standalone tool design

**AST structure investigation:**
1. Study Clang AST node types for modern C++ features:
   - `CXXRecordDecl` (classes), `ClassTemplateDecl` (templates)
   - `CXXConstructExpr`, `CXXDestructorDecl` (RAII)
   - `LambdaExpr`, `CXXThrowExpr`, `CXXCatchStmt`
2. Understand AST traversal APIs: `RecursiveASTVisitor`, `ASTConsumer`, `ASTFrontendAction`
3. Research AST matchers and rewriting tools

**Search for:**
- Official Clang documentation on AST traversal and custom code generation
- Clang API tutorials and examples
- Source code of Clang's own CodeGen (how it emits LLVM IR)

### Phase 2: Existing Tools Analysis

**Study Clang-based transpilers and source-to-source tools:**

1. **Clava** (Java-based, C++ to C++ transformations)
   - URL: https://github.com/specs-feup/clava
   - Study: How does it traverse AST and emit C++ code?
   - Extract: Code generation patterns, readability techniques

2. **LLVM C Backend (llvm-cbe)**
   - URL: https://github.com/JuliaComputing/llvm-cbe
   - Study: Why is output unreadable? What causes the verbosity?
   - Learn: What NOT to do for human-readable output

3. **Clang-based refactoring tools**
   - clang-tidy, clang-format, clang-rename
   - Study: How they manipulate and rewrite source code
   - Extract: Rewriting APIs, source location preservation

4. **Academic projects**
   - Search for research papers on C++ to C translation using Clang
   - Look for theses/dissertations on source-to-source compilation

**For each tool, document:**
- Architecture (AST visitor? CodeGen consumer? Other?)
- Code generation approach
- What works well, what doesn't
- Reusable patterns or libraries

### Phase 3: Feature Conversion Strategy Research

For EACH major C++ feature, research conversion approach:

**Classes and Objects:**
- Struct-based representation in C
- Virtual function tables (vtables) implementation
- Constructor/destructor call simulation
- Member function → static function with `this` pointer

**Templates:**
- Template instantiation extraction from AST
- Monomorphization (generate C function per instantiation)
- How Clang stores instantiated template AST nodes
- SFINAE and template metaprogramming handling

**RAII (Resource Acquisition Is Initialization):**
- Scope-based destructor calls
- Exception-safe resource management in C
- Cleanup function generation and injection

**Exceptions:**
- setjmp/longjmp-based exception handling
- Exception object propagation
- Stack unwinding simulation
- Try-catch block transformation

**STL (Standard Template Library):**
- Which STL components can be converted vs need C reimplementation?
- Container representation (vector, map, string, etc.)
- Algorithm template instantiation
- Iterator pattern in C

**Lambdas and Closures:**
- Closure capture → struct representation
- Lambda → function pointer with context
- Capture by reference vs value

**Move Semantics and Rvalue References:**
- How to represent move operations in C?
- Rvalue reference → pointer manipulation?

**Other Modern Features:**
- `auto` type deduction (already resolved in AST)
- Range-based for loops → traditional for loops
- `constexpr` → compile-time evaluation
- Concepts (C++20) → template constraint verification

**Research sources:**
- How compilers implement these features (ABI documentation)
- Itanium C++ ABI specifications
- Existing decompilers (how they represent C++ constructs in C)

### Phase 4: Code Emission Strategy

**Readable C code generation:**
1. Name mangling approach for C++ symbols
   - Keep names readable (not Itanium mangling)
   - Namespace → prefix strategy
2. Comment generation (preserve intent)
3. Whitespace and formatting for readability
4. `#line` directive placement strategy

**Technical implementation:**
1. Research Clang's `Rewriter` class for source modifications
2. Study `SourceLocation` and source range APIs
3. Investigate how to generate NEW C code (not just transform existing)
4. Pretty-printer patterns for C code generation

**Build system integration:**
1. How to invoke Clang as a library?
2. Compilation database integration (`compile_commands.json`)
3. Header file handling and dependency resolution

### Phase 5: Feasibility Assessment

**Critical questions to answer:**
1. Can ALL modern C++ features be converted to readable C?
   - If no, which features are blockers?
   - What subset is realistically achievable?

2. What's the estimated complexity of each feature?
   - Simple (auto, range-for) vs Hard (templates, exceptions)

3. What's the performance profile?
   - AST traversal overhead
   - Generated code size and runtime performance

4. What are the showstoppers?
   - Technical impossibilities
   - Maintenance burden
   - Corner cases that break the approach

### Phase 6: Implementation Roadmap

If feasible, outline HIGH-LEVEL implementation phases:
1. Proof of concept scope (minimal viable features)
2. Core infrastructure (AST visitor, C code emitter)
3. Feature implementation order (simple → complex)
4. Testing strategy (how to validate correctness?)

</research_process>

<output_specification>
Create comprehensive research output saved to: `.prompts/001-clang-cpp-to-c-converter-research/clang-cpp-to-c-converter-research.md`

Structure the output with XML tags for Claude-to-Claude parsing:

```xml
<research_output>
<executive_summary>
[3-4 paragraphs answering:]
- Is this approach technically feasible?
- What's the recommended interception point in Clang?
- What are the major technical challenges?
- Overall assessment: Viable / Partially Viable / Not Viable
</executive_summary>

<clang_architecture>
<compilation_pipeline>
[Detailed explanation of Clang compilation phases]
[Where to intercept and why]
</compilation_pipeline>

<recommended_approach>
[AST-based / CodeGen-based / Hybrid]
[Justification with technical reasoning]
</recommended_approach>

<implementation_strategy>
[Plugin vs Standalone tool]
[Key APIs and classes to use]
</implementation_strategy>
</clang_architecture>

<existing_tools>
<tool name="Clava">
<url>...</url>
<architecture>...</architecture>
<lessons_learned>...</lessons_learned>
<reusable_patterns>...</reusable_patterns>
</tool>

<tool name="llvm-cbe">
[Similar structure]
</tool>

[Repeat for each tool studied]
</existing_tools>

<feature_conversion_matrix>
<feature name="Classes and Objects">
<c_representation>
[How to represent in C]
</c_representation>
<complexity>Low / Medium / High / Extreme</complexity>
<feasibility>Straightforward / Challenging / Severe Limitations / Impractical</feasibility>
<implementation_notes>
[Key techniques, gotchas, examples]
</implementation_notes>
</feature>

[Repeat for: Templates, RAII, Exceptions, STL, Lambdas, Move Semantics, etc.]
</feature_conversion_matrix>

<code_emission_strategy>
<name_mangling>
[Approach for readable symbol names]
</name_mangling>

<line_directive_placement>
[Strategy for #line directives]
</line_directive_placement>

<readability_techniques>
[How to generate human-readable C code]
</readability_techniques>

<pretty_printing>
[Formatting and indentation strategy]
</pretty_printing>
</code_emission_strategy>

<feasibility_assessment>
<achievable_features>
[List features that CAN be converted with reasonable effort]
</achievable_features>

<problematic_features>
[List features with severe challenges]
[For each: What's the blocker? Any workarounds?]
</problematic_features>

<showstoppers>
[List any deal-breaker issues that make this impractical]
[If none, state: "No fundamental showstoppers identified"]
</showstoppers>

<realistic_scope>
[What subset of C++ can this tool realistically handle?]
[All modern C++ / Practical subset / Limited subset]
</realistic_scope>
</feasibility_assessment>

<implementation_roadmap>
<phase number="1" name="Proof of Concept">
<scope>
[Minimal features to demonstrate viability]
</scope>
<deliverables>
[What to build in this phase]
</deliverables>
<effort_estimate>
[Complexity assessment: Trivial / Small / Medium / Large / Very Large]
</effort_estimate>
</phase>

[Repeat for phases 2-N]

<critical_path>
[What must be built first? What are the dependencies?]
</critical_path>

<testing_strategy>
[How to validate correctness of conversions?]
</testing_strategy>
</implementation_roadmap>

<technical_risks>
[List major risks and mitigation strategies]
</technical_risks>

<alternative_approaches>
[If primary approach has issues, what are alternatives?]
</alternative_approaches>

<recommendations>
<primary_recommendation>
[Go forward / Pivot to different approach / Abandon]
[Detailed justification]
</primary_recommendation>

<next_steps>
1. [Concrete action items if proceeding]
2. [What to prototype or validate first]
3. [Decision points and criteria]
</next_steps>
</recommendations>

<confidence>
[Overall confidence in findings: High / Medium / Low]

<confidence_breakdown>
- Clang architecture understanding: [High/Medium/Low]
- Feature conversion strategies: [High/Medium/Low]
- Feasibility assessment: [High/Medium/Low]
- Implementation effort estimates: [High/Medium/Low]
</confidence_breakdown>

<verification_status>
[Which claims were verified vs assumed]
- Verified: [List key facts verified with official docs/source code]
- Assumed: [List any assumptions or unverified claims]
</verification_status>
</confidence>

<dependencies>
[What's needed to proceed with implementation?]
- Development environment setup (Clang/LLVM version X)
- Specific knowledge/skills required
- External libraries or tools
</dependencies>

<open_questions>
[What remains uncertain after this research?]
1. [Question requiring experimentation or deeper investigation]
2. [Question requiring prototype to answer]
</open_questions>

<assumptions>
[Key assumptions made during this research]
1. [Assumption and its implications]
2. [Assumption and fallback if wrong]
</assumptions>

<sources>
## Official Documentation
- [Clang documentation URLs]
- [LLVM documentation URLs]

## Tools and Projects
- [GitHub repos studied]

## Academic Papers
- [Any research papers consulted]

## Other Resources
- [Stack Overflow, blog posts, etc.]
</sources>
</research_output>
```

**CRITICAL: Quality Controls**

Before completing the research, execute this verification checklist:

<verification_checklist>
✓ Clang compilation pipeline documented with official sources
✓ At least 3-5 existing Clang-based tools analyzed in depth
✓ ALL major C++ features evaluated for conversion feasibility
✓ Specific Clang APIs and classes identified for implementation
✓ Realistic feasibility assessment (not overly optimistic)
✓ Technical risks and challenges honestly documented
✓ Sources cited with working URLs
✓ Confidence levels assigned to all major claims
✓ Open questions clearly identified
</verification_checklist>

**Quality Assurance:**
- Distinguish VERIFIED facts (from official docs/source code) from INFERRED approaches
- For each feature conversion strategy, cite source (ABI spec / existing tool / first principles)
- If uncertain about feasibility, say so explicitly (don't speculate as fact)
- Include code examples where helpful (AST node structures, C output examples)

**Pre-submission Check:**
Before declaring research complete, ask yourself:
1. Could a skilled C++ developer use this to START implementing the tool?
2. Are the major technical risks clearly identified?
3. Is the feasibility assessment realistic (not wishful thinking)?
4. Are all critical C++ features addressed?

If any answer is NO, continue researching that area.
</output_specification>

<deliverables>
**Required files to create:**

1. **Main research output:** `.prompts/001-clang-cpp-to-c-converter-research/clang-cpp-to-c-converter-research.md`
   - Full XML-structured research findings
   - For Claude-to-Claude consumption

2. **Executive summary:** `.prompts/001-clang-cpp-to-c-converter-research/SUMMARY.md`
   - Human-readable summary
   - Use this exact structure:

```markdown
# Clang C++ to C Converter - Research Summary

**[One-liner: Substantive finding, not "Research completed"]**

Version: v1

## Key Findings
• [Finding 1 - most important technical insight]
• [Finding 2 - feasibility assessment]
• [Finding 3 - recommended approach]
• [Finding 4 - major challenges]
• [Finding 5 - critical next step]

(Use bullet points, be specific and actionable)

## Decisions Needed
[What requires user input to proceed?]
- [Decision 1]
- [Decision 2]

OR "None - ready for planning" if research is conclusive

## Blockers
[External impediments preventing progress]
- [Blocker 1]
- [Blocker 2]

OR "None" if no blockers

## Next Step
[Single, concrete action to take next]
Example: "Create implementation plan for Phase 1 POC" or "Prototype template instantiation extraction"
```

**Streaming write for large output:**
For the main research file, use STREAMING WRITE approach:
1. Write file incrementally as research progresses (don't accumulate in memory)
2. Use Edit tool to append sections as they're completed
3. This prevents context overflow for large research outputs

</deliverables>

<success_criteria>
Research is complete when:

✓ **Comprehensive coverage:**
  - Clang architecture thoroughly understood
  - 3-5+ existing tools analyzed
  - All major C++ features evaluated
  - Code emission strategy designed

✓ **Actionable output:**
  - Clear feasibility verdict (Viable / Partially Viable / Not Viable)
  - Specific implementation approach recommended
  - Concrete roadmap provided (if feasible)
  - Major risks identified with mitigation strategies

✓ **Quality validated:**
  - Verification checklist completed
  - Sources cited and verified
  - Confidence levels assigned
  - Assumptions explicitly stated
  - Open questions documented

✓ **Properly formatted:**
  - Main output uses XML structure for Claude parsing
  - SUMMARY.md uses human-readable format
  - One-liner is substantive (answers "what did we learn?")
  - All required metadata included (confidence, dependencies, open_questions, assumptions)

✓ **Research can be used to:**
  - Make go/no-go decision on implementation
  - Start coding a proof of concept
  - Create detailed implementation plan
  - Understand technical risks and challenges
</success_criteria>

<meta_instructions>
- This is a DEEP research task - allocate significant effort
- Prioritize OFFICIAL Clang/LLVM documentation over blog posts
- Study actual Clang source code where documentation is insufficient
- Be HONEST about feasibility - don't oversell if features are problematic
- Focus on READABLE C output (not machine-generated like llvm-cbe)
- Remember: Target is ALL modern C++ features (ambitious scope)
- Use extended thinking for complex feasibility analysis
- Create SUMMARY.md AFTER completing research (not placeholder)
</meta_instructions>

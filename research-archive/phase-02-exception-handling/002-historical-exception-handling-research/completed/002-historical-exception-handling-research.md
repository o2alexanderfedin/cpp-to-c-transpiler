<research_objective>
Research how early C++ compilers and historical C++-to-C transpilers implemented exception handling and RAII when generating C code, to discover proven patterns and practical solutions that can be adapted for a modern Clang-based C++ to C converter.

**Primary Goal:** Find actionable, proven implementation strategies for exception+RAII interaction in generated C code.

**Context:** Current research (@.prompts/001-clang-cpp-to-c-converter-research/clang-cpp-to-c-converter-research.md:1200-1450) identifies exception+RAII as the primary remaining challenge. Historical compilers (especially Cfront era) had to solve this exact problem when translating C++ to C in the 1980s-1990s, before native code generation became standard.

**Key Questions:**
1. How did Cfront handle exceptions in generated C code?
2. What simplifications or pragmatic choices did early compilers make?
3. Are there proven patterns that avoid the complexity identified in current research?
4. What lessons from historical implementations can inform modern design?
</research_objective>

<context>
**Background from current research:**
- Exception+RAII interaction requires nested setjmp frames at every destructible scope
- Current assessment: "Complex but feasible - generates verbose C code"
- Two approaches identified: setjmp/longjmp (complete) vs error codes (simple)
- STL showstopper eliminated via self-bootstrapping (v1.1 breakthrough)

**Why historical research matters:**
- Early compilers had severe constraints (memory, performance) → forced simplicity
- Production systems used these compilers for decades → patterns are proven
- Historical solutions may reveal overlooked simplifications
- Academic papers from that era may document specific techniques

**Referenced research:**
@.prompts/001-clang-cpp-to-c-converter-research/clang-cpp-to-c-converter-research.md
@.prompts/001-clang-cpp-to-c-converter-research/feasibility-and-roadmap.md
</context>

<research_process>
This is a COMPREHENSIVE historical investigation. Thoroughly explore multiple eras and approaches:

### Phase 1: Cfront Era (1980s-1993)

**Cfront - The Original C++ to C Translator**

Cfront was Bjarne Stroustrup's original C++ compiler that translated C++ to C. This is THE most important source for our research.

**Research Tasks:**

1. **Exception Handling in Cfront**
   - Did Cfront support exceptions at all? (Exceptions added to C++ in late 1980s/early 1990s)
   - If yes: How did it translate try/catch/throw to C?
   - If no: Why not? What were the acknowledged limitations?

2. **RAII and Destructors in Cfront**
   - How did Cfront ensure destructors were called at scope exit?
   - Did it use goto-based cleanup? setjmp/longjmp? Other patterns?
   - How did it handle early returns, breaks, continues?

3. **Exception+RAII Interaction**
   - If Cfront supported both: How did it combine them?
   - What C code patterns did it generate?
   - Were there known performance or code size issues?

**Sources to Investigate:**
- Bjarne Stroustrup's papers and books (esp. "The Design and Evolution of C++")
- Cfront source code (if available - check AT&T archives, historical repositories)
- Academic papers citing Cfront's implementation
- Usenet comp.lang.c++ archives from 1985-1995

### Phase 2: Early Exception Implementations

**Other C++-to-C Compilers and Early C++ Implementations:**

1. **GNU C++ (g++) Early Versions (1987-1995)**
   - When did g++ add exception support?
   - Did early g++ generate C code or native assembly?
   - If C generation existed: How did it handle exceptions?

2. **Comeau C++**
   - Commercial C++-to-C compiler used in embedded systems
   - Known for high-quality C output
   - May have documentation on exception handling strategies

3. **Edison Design Group (EDG) Frontend**
   - Used by many commercial compilers
   - May have generated C as intermediate representation
   - Check for academic papers or technical documentation

4. **Zortech C++/Symantec C++**
   - Early PC-based C++ compilers
   - Check if they had C generation backends

**Research Questions:**
- Which compilers actually generated C code (vs. direct assembly)?
- For those that did: What exception handling patterns did they use?
- Were there standard approaches or did each compiler solve it differently?

### Phase 3: Academic Research and Papers

**Search for Academic Literature:**

1. **ACM Digital Library / IEEE Xplore Search Terms:**
   - "C++ exception handling implementation"
   - "exception handling in C"
   - "RAII implementation"
   - "C++ to C translation"
   - "exception table generation"
   - "stack unwinding"
   - Date range: 1985-2000 (early C++ era)

2. **Key Research Areas:**
   - Exception handling mechanisms (zero-cost vs table-driven)
   - Stack unwinding algorithms
   - Destructor injection techniques
   - Resource management in C

3. **Specific Papers to Find:**
   - Papers by Bjarne Stroustrup on C++ implementation
   - Papers on exception handling by Andrew Koenig, Barbara Moo
   - Any papers describing C++ compiler implementation details

### Phase 4: Itanium C++ ABI and Exception Handling

**While not historical C generation, the Itanium ABI documents the "correct" way:**

1. **Itanium C++ ABI Exception Handling Specification**
   - How are exceptions supposed to work?
   - Stack unwinding mechanism
   - Destructor registration
   - Exception tables

2. **Can these concepts be adapted to C?**
   - Which parts require runtime support?
   - Which parts could be emulated in C?
   - What's the minimal viable subset?

### Phase 5: Embedded C++ and Restricted Dialects

**EC++ (Embedded C++) and Similar Efforts:**

1. **Embedded C++ Specification**
   - Subset of C++ designed for embedded systems
   - Often restricted exception handling
   - May document simpler alternatives

2. **MISRA C++ Guidelines**
   - Safety-critical C++ coding standard
   - Restrictions on exception usage
   - May suggest simpler exception patterns

3. **DO-178C and Safety-Critical C++**
   - How do safety-critical systems handle exceptions?
   - Are there certified patterns for exception+RAII?

### Phase 6: Modern Tools - Reverse Analysis

**Analyze How Modern C++-to-C Tools Work:**

1. **emmtrix eCPP2C (already researched, but dig deeper)**
   - Request trial/demo if possible
   - Examine generated C code examples
   - Look for technical whitepapers or documentation
   - Specifically: How do they handle exceptions?

2. **LLVM C Backend (llvm-cbe) - Detailed Analysis**
   - Previously dismissed as "unreadable"
   - But: Examine WHAT it does, not just output quality
   - How does it handle exception constructs?
   - Can we extract the algorithm but improve readability?

3. **Circle C++ (if relevant)**
   - Modern tool, may have insights
   - Check if it has C generation mode

### Phase 7: Practical Patterns and Workarounds

**Real-World Solutions and Best Practices:**

1. **C Exception Handling Libraries**
   - libexcept, exceptions4c, CException
   - How do pure C projects implement exception-like behavior?
   - Can these patterns scale to C++ conversion?

2. **longjmp Best Practices**
   - Historical wisdom on setjmp/longjmp usage
   - Known pitfalls and solutions
   - Performance characteristics

3. **Error Handling Patterns in C**
   - errno and return codes
   - Error callback mechanisms
   - How do large C codebases handle errors?

</research_process>

<output_specification>
Create comprehensive research output saved to: `.prompts/002-historical-exception-handling-research/historical-exception-handling-research.md`

Structure with XML for Claude-to-Claude consumption:

```xml
<research_output>
<executive_summary>
[3-4 paragraphs:]
- What did historical compilers actually do for exception+RAII?
- What proven patterns were discovered?
- What practical insights can we extract?
- Recommended approach based on historical evidence
</executive_summary>

<cfront_analysis>
<exception_support>
[Did Cfront support exceptions? When? How?]
</exception_support>

<raii_implementation>
[How did Cfront ensure destructors were called?]
[Code examples of generated C for RAII]
</raii_implementation>

<exception_raii_interaction>
[How did Cfront combine exceptions + RAII?]
[If not supported: Why not? What were the blockers?]
</exception_raii_interaction>

<generated_code_examples>
[Actual C code examples from Cfront output, if found]
</generated_code_examples>

<lessons_learned>
[Key insights from Cfront's approach]
</lessons_learned>
</cfront_analysis>

<early_compilers>
<compiler name="GNU C++ (early versions)">
<exception_approach>[How g++ handled exceptions in early versions]</exception_approach>
<code_generation>[Did it generate C? If so, what patterns?]</code_generation>
<lessons>[Reusable insights]</lessons>
</compiler>

<compiler name="Comeau C++">
[Similar structure]
</compiler>

[Repeat for each compiler investigated]
</early_compilers>

<academic_research>
<paper title="[Paper Title]" authors="[Authors]" year="[Year]" url="[URL or DOI]">
<key_findings>
[What did this paper discover about exception implementation?]
</key_findings>

<applicability>
[Can we use these techniques? How?]
</applicability>
</paper>

[Repeat for significant papers found]
</academic_research>

<exception_handling_patterns>
<pattern name="[Pattern Name]">
<description>
[How this pattern works]
</description>

<c_code_example>
```c
[Example C code demonstrating the pattern]
```
</c_code_example>

<pros>
[Advantages of this approach]
</pros>

<cons>
[Disadvantages or limitations]
</cons>

<historical_usage>
[Which compilers/tools used this pattern?]
</historical_usage>

<applicability_to_modern_tool>
[Can we use this in our Clang-based converter? How?]
</applicability_to_modern_tool>
</pattern>

[Document 3-5 major patterns discovered]
</exception_handling_patterns>

<raii_patterns>
<pattern name="[Pattern Name]">
[Similar structure to exception patterns]
[Focus on destructor injection techniques]
</pattern>
</raii_patterns>

<simplifications_and_pragmatism>
<simplification name="[What was simplified]">
<rationale>
[Why did historical compilers make this choice?]
</rationale>

<trade_offs>
[What was gained? What was lost?]
</trade_offs>

<modern_applicability>
[Should we adopt this simplification?]
</modern_applicability>
</simplification>

[Examples: "Exceptions disabled in destructors", "No exception specifications", "Error codes for certain exception types"]
</simplifications_and_pragmatism>

<comparison_with_current_research>
<current_approach>
[Summary of current research findings from 001-clang-cpp-to-c-converter-research]
</current_approach>

<historical_approaches>
[Summary of discovered historical approaches]
</historical_approaches>

<gaps_and_differences>
[What did current research miss that historical research reveals?]
[What did historical compilers NOT do that we should consider?]
</gaps_and_differences>
</comparison_with_current_research>

<recommendations>
<primary_recommendation>
[Based on historical evidence, what's the best approach for exception+RAII?]
[Specific implementation strategy with code examples]
</primary_recommendation>

<rationale>
[Why this approach is recommended]
[Historical precedent supporting it]
[Known production usage validating it]
</rationale>

<implementation_notes>
[Key techniques to use]
[Pitfalls to avoid based on historical failures]
</implementation_notes>

<alternative_approaches>
[Other viable historical patterns]
[When to use each]
</alternative_approaches>
</recommendations>

<actionable_insights>
[List of 5-10 concrete, actionable insights]
1. [Specific technique discovered and how to apply it]
2. [Pattern validated by historical usage]
3. [Simplification that proved practical]
...
</actionable_insights>

<confidence>
Overall: [High/Medium/Low]

<confidence_breakdown>
- Cfront analysis: [High/Medium/Low - based on source availability]
- Early compiler research: [High/Medium/Low]
- Academic paper findings: [High/Medium/Low]
- Pattern applicability: [High/Medium/Low]
</confidence_breakdown>

<verification_status>
**Verified with primary sources:**
- [List what was verified with original documentation, source code, or academic papers]

**Inferred from secondary sources:**
- [List what was pieced together from blogs, forum discussions, or incomplete documentation]

**Assumed without verification:**
- [List any assumptions made where sources were unavailable]
</verification_status>
</confidence>

<dependencies>
[What's needed to validate these findings?]
- Access to Cfront source code (if not found)
- Testing historical patterns in modern context
- Benchmarking performance characteristics
</dependencies>

<open_questions>
[What remains uncertain after research?]
1. [Question requiring experimentation]
2. [Question where sources disagree]
3. [Question requiring prototype to answer]
</open_questions>

<assumptions>
[Key assumptions made]
1. [Assumption about historical implementation details]
2. [Assumption about applicability to modern tool]
</assumptions>

<sources>
## Primary Sources
- [Cfront documentation, source code, or Stroustrup's writings]
- [Other compiler documentation]

## Academic Papers
- [Full citations with DOI/URLs]

## Secondary Sources
- [Blog posts, Stack Overflow, forums]
- [Book references]

## Tools Analyzed
- [URLs to tools examined]
</sources>
</research_output>
```

**CRITICAL: Quality Controls**

<verification_checklist>
✓ Cfront exception handling thoroughly researched with primary sources
✓ At least 3-5 early compilers investigated
✓ Academic papers from 1985-2000 era reviewed
✓ At least 3-5 proven exception handling patterns documented with code examples
✓ Each pattern evaluated for modern applicability
✓ Historical simplifications identified and assessed
✓ Comparison with current research (001) performed
✓ Concrete, actionable recommendations provided
✓ All claims sourced (primary, secondary, or labeled as inferred)
✓ Open questions and unknowns explicitly documented
</verification_checklist>

**Pre-Submission Questions:**
1. Can an implementer use this research to choose an exception handling strategy?
2. Are the historical patterns concrete enough to code from?
3. Is it clear WHY historical compilers made specific choices?
4. Have we extracted maximum value from historical precedent?

If NO to any: Continue research in that area.

</output_specification>

<deliverables>
**Required files:**

1. **Main research:** `.prompts/002-historical-exception-handling-research/historical-exception-handling-research.md`
   - Full XML-structured historical analysis
   - For Claude-to-Claude consumption

2. **Executive summary:** `.prompts/002-historical-exception-handling-research/SUMMARY.md`
   - Human-readable findings
   - Structure:

```markdown
# Historical Exception Handling Research - Summary

**[One-liner: Most important discovery about historical exception handling]**

Version: v1

## Key Findings
• [Finding 1 - Cfront's approach]
• [Finding 2 - Most proven pattern]
• [Finding 3 - Recommended strategy]
• [Finding 4 - Critical insight from historical failures]
• [Finding 5 - Actionable next step]

## Decisions Needed
[What requires user input based on historical options?]
- [Choice between historical approaches]
- [Trade-off decisions]

OR "None - clear recommendation from historical evidence"

## Blockers
[Missing historical sources or information]
- [Unavailable documentation]

OR "None"

## Next Step
[Immediate action based on findings]
Example: "Implement Cfront-style destructor injection pattern" or "Prototype pattern X from early g++"
```

**Streaming write approach:**
- Write sections incrementally as discovered
- Prevents context overflow for large research

</deliverables>

<success_criteria>
Research complete when:

✓ **Historical depth:**
  - Cfront thoroughly analyzed
  - 3-5+ early compilers researched
  - Academic papers from 1985-2000 reviewed
  - Modern tools reverse-analyzed

✓ **Actionable patterns:**
  - 3-5 proven exception handling patterns documented
  - Each pattern has C code examples
  - Modern applicability assessed for each
  - Clear recommendation provided

✓ **Practical insights:**
  - Historical simplifications identified
  - Known pitfalls documented
  - Production-proven approaches highlighted
  - Implementation guidance provided

✓ **Properly formatted:**
  - XML structure for Claude parsing
  - SUMMARY.md for human scanning
  - All sources cited
  - Verification status clear

✓ **Integration with current research:**
  - Compared with 001-clang-cpp-to-c-converter findings
  - Gaps identified
  - Enhanced understanding documented

✓ **Research enables action:**
  - Can choose exception handling strategy from findings
  - Can start coding based on historical patterns
  - Understand trade-offs of each approach
  - Know what worked in production vs. what failed
</success_criteria>

<meta_instructions>
- This is COMPREHENSIVE historical research - allocate significant depth
- Prioritize PRIMARY sources (Stroustrup's writings, academic papers, source code)
- Extract ACTIONABLE patterns, not just historical trivia
- Focus on PROVEN approaches (production-used), not experimental
- Be honest about source availability - some historical info may be lost
- Compare with current research - what did we miss? What did history miss?
- Think like a compiler implementer from 1990 - what constraints forced simplicity?
- Create SUMMARY.md AFTER research (substantive findings, not placeholder)
- Use extended thinking for pattern analysis and applicability assessment
</meta_instructions>

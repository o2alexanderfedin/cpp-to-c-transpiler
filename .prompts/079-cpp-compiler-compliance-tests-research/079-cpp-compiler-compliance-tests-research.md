# C++ Compiler Compliance Test Suites Research

<research_objective>
Research and identify comprehensive test suites used to verify C++ compiler compliance by language version (C++98, C++03, C++11, C++14, C++17, C++20, C++23, C++26).

This research will inform the testing strategy for the C++ to C transpiler project, ensuring comprehensive coverage of C++ language features across different standards.

**End Goal**: Identify authoritative, well-maintained test suites that can:
1. Validate C++ compiler correctness for each standard version
2. Serve as reference for feature coverage benchmarking
3. Potentially be adapted for transpiler validation

Thoroughly explore multiple sources including official standards bodies, compiler projects, and academic resources.
</research_objective>

<scope>
**Include**:
- Official C++ standards committee test suites (if publicly available)
- Open-source compiler test suites (GCC, Clang/LLVM, MSVC)
- Third-party compliance verification tools and frameworks
- Academic or research-based test collections
- Language conformance test frameworks

**Focus on**:
- Tests organized by C++ standard version (C++11, C++14, C++17, C++20, C++23, C++26)
- Publicly accessible test suites (open source preferred)
- Actively maintained projects (recent activity within last 2 years)
- Comprehensive coverage (not just syntax, but semantics and behavior)

**Exclude**:
- Pure benchmarking suites (performance-focused, not correctness-focused)
- Proprietary or commercial-only test tools
- Abandoned projects (no updates in 3+ years)
- Company-internal test suites without public access
</scope>

<research_questions>
Answer these specific questions:

1. **Official Test Suites**:
   - Does the ISO C++ Standards Committee maintain an official conformance test suite?
   - If yes, is it publicly available? How to access it?
   - What versions of the standard does it cover?

2. **Compiler Project Test Suites**:
   - What test suites do GCC, Clang, and MSVC use internally?
   - Are these test suites publicly accessible?
   - How are they organized (by feature, by standard version)?
   - What is the license/usage terms?

3. **Third-Party Test Frameworks**:
   - What well-known third-party C++ compliance test projects exist?
   - Examples: Compiler Explorer test cases, C++ reference test collections
   - What standards do they target?

4. **Test Organization**:
   - How are compliance tests typically structured?
   - Are there standard patterns for organizing tests by language feature vs. standard version?
   - Do test suites provide expected output or just compilability checks?

5. **Coverage Analysis**:
   - Which test suites have the most comprehensive coverage?
   - Are there gaps in publicly available tests (e.g., newer C++20/C++23 features)?
   - Which areas of the standard are hardest to test?

6. **Practical Usage**:
   - How do compiler developers use these test suites?
   - Can test suites be run against custom compilers/transpilers?
   - What infrastructure is needed to run these tests?

7. **C++ Feature Catalogs**:
   - Are there comprehensive catalogs of C++ features by version?
   - Do any projects provide feature matrices (feature × compiler × version)?
</research_questions>

<deliverables>
Create a comprehensive research report saved to: `.prompts/079-cpp-compiler-compliance-tests-research/cpp-compiler-compliance-tests-research.md`

**Report Structure**:

```markdown
# C++ Compiler Compliance Test Suites Research

## Executive Summary
[1-2 paragraph overview of key findings]

## Official Test Suites

### ISO C++ Standards Committee
- [Availability, access, coverage]

### WG21 (C++ Working Group)
- [Any publicly available test materials]

## Compiler Project Test Suites

### GCC Test Suite
- **Location**: [GitHub/Git URL or path]
- **Coverage**: [Which C++ standards]
- **Organization**: [How tests are structured]
- **License**: [Usage terms]
- **Notable Features**: [What makes it valuable]
- **Access**: [How to obtain/use]

### Clang/LLVM Test Suite
- [Same structure as GCC]

### MSVC Test Suite
- [Same structure, note if not publicly available]

## Third-Party Test Frameworks

### [Framework Name 1]
- [Full details as above]

### [Framework Name 2]
- [Full details as above]

[Continue for all discovered frameworks]

## Feature Coverage Analysis

### Comprehensive Coverage Test Suites
[List suites with broad feature coverage]

### Gaps in Public Test Availability
[Identify missing coverage, especially for newer standards]

### Feature Organization Best Practices
[How best-in-class suites organize their tests]

## Standards-Specific Resources

### C++11 Test Resources
[Specific to C++11]

### C++14 Test Resources
[Specific to C++14]

### C++17 Test Resources
[Specific to C++17]

### C++20 Test Resources
[Specific to C++20]

### C++23 Test Resources
[Specific to C++23]

### C++26 Test Resources (Preview)
[Specific to C++26, if available]

## Feature Catalogs and Matrices

### Comprehensive Feature Lists
[Projects that catalog all C++ features by version]

### Compiler Support Matrices
[Resources showing feature support across compilers]

## Practical Usage Guidance

### Running Test Suites
[How to execute these test suites]

### Adapting for Custom Compilers
[Guidance on using these tests for transpilers or custom tools]

### Infrastructure Requirements
[What's needed to run large test suites]

## Recommendations for Transpiler Project

### Primary Test Sources
[Top 3-5 recommended test suites for the project]

### Integration Strategy
[How to incorporate these tests into the transpiler test suite]

### Coverage Prioritization
[Which standards/features to prioritize based on findings]

## Resources and Links

### Official Documentation
- [List all official standard docs, proposals, etc.]

### Test Suite Repositories
- [List all Git repos, download links]

### Community Resources
- [Forums, wikis, blog posts, papers]

### Tools and Utilities
- [Related tools that help with compliance testing]

## Open Questions
[List any questions that remain unanswered after research]

## References
[Numbered list of all sources consulted with URLs]
```
</deliverables>

<research_methodology>
1. **Start with official sources**:
   - ISO C++ Standards Committee website
   - WG21 (C++ Working Group) papers and resources
   - C++ Standard Library specification test repositories

2. **Explore major compiler projects**:
   - GCC testsuite (gcc/testsuite/g++.dg/)
   - Clang test suite (clang/test/)
   - LLVM test suite
   - Microsoft STL test suite

3. **Search for third-party frameworks**:
   - GitHub search for "C++ compliance test", "C++ conformance test"
   - Search academic papers on compiler testing
   - Check Compiler Explorer (godbolt.org) test collections

4. **Investigate language feature catalogs**:
   - cppreference.com feature lists
   - C++ compiler support matrices (e.g., cppreference compiler support)
   - Language feature proposals and tracking

5. **Verify and validate findings**:
   - Check repository activity (last commit date)
   - Verify license terms for potential use
   - Assess test quality and comprehensiveness
   - Note any dependencies or infrastructure requirements
</research_methodology>

<evaluation_criteria>
**Source Quality Assessment**:
- **Authoritative**: Official standards body > Major compiler project > Academic > Community
- **Maintenance**: Active (< 6 months) > Recent (< 2 years) > Stale (> 2 years)
- **Coverage**: Comprehensive (all features) > Broad (major features) > Narrow (specific areas)
- **Accessibility**: Open source + documented > Open source > Proprietary but accessible > Unavailable
- **Usability**: Automated + well-organized > Manual but clear > Requires expertise

**Answer Completeness**:
Before completing, verify you've answered ALL research questions from the <research_questions> section. Each question should have a clear, evidence-based answer in the report.

**Source Credibility**:
- Prioritize official standards bodies and major compiler projects
- Verify information from multiple independent sources when possible
- Note when information comes from unofficial or community sources
- Include URLs and access dates for all web sources
</evaluation_criteria>

<output_format>
**Primary deliverable**: Comprehensive markdown report (as specified in <deliverables>)

**Additional outputs**:
- Create `SUMMARY.md` with executive summary (1 page max)
- Create `QUICK_REFERENCE.md` with table of recommended test suites:
  ```markdown
  | Test Suite | Coverage | License | Accessibility | Last Updated | Recommendation |
  |------------|----------|---------|---------------|--------------|----------------|
  | GCC        | C++98-23 | GPL     | Public        | 2025-01      | ⭐⭐⭐⭐⭐     |
  | ...        | ...      | ...     | ...           | ...          | ...            |
  ```
</output_format>

<verification>
Before completing, verify:

- [ ] All 7 research questions have detailed answers
- [ ] At least 3 major test suites are thoroughly documented
- [ ] Each C++ standard version (C++11 through C++23 minimum) has identified test resources
- [ ] URLs are provided for all mentioned test suites and resources
- [ ] License and accessibility information is included for each test suite
- [ ] Practical recommendations are provided for the transpiler project
- [ ] Sources are credible and verifiable (include access dates)
- [ ] Report follows the specified structure in <deliverables>
- [ ] SUMMARY.md and QUICK_REFERENCE.md are created
- [ ] Open questions section lists any unresolved research areas
</verification>

<success_criteria>
- Comprehensive report covering all major C++ compliance test frameworks
- Clear identification of 3-5 recommended test suites for the transpiler project
- Complete coverage analysis by C++ standard version (C++11-C++23 minimum)
- Actionable guidance on accessing and using identified test suites
- All research questions answered with evidence-based responses
- Multiple authoritative sources cited for key findings
- Quick reference table enabling rapid comparison of test suite options
</success_criteria>

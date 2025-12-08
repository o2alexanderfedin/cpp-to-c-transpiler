<research_objective>
Research and evaluate available tools that can convert contemporary C++ code to C code.

This research will inform a decision on whether automated conversion is viable for this project, or if manual translation will be required. The goal is to identify practical, actively-maintained solutions that can handle modern C++ features.
</research_objective>

<scope>
Focus on:
- **Modern C++ support**: Tools that can handle C++11, C++14, C++17, C++20+ features
- **Active maintenance**: Projects updated within the last 2-3 years
- **Practical usability**: Tools that are documented and actually usable (not just research projects)
- **Open source preferred**: Commercial tools are acceptable if they offer trials or free tiers

Investigation areas:
1. Transpilers and source-to-source compilers (C++ → C)
2. Decompilation approaches (C++ binary → C)
3. Academic research tools and prototypes
4. Partial conversion tools (specific feature subsets)
5. Alternative approaches (if direct conversion tools don't exist)

Search strategies:
- GitHub repositories with relevant keywords
- Academic papers on C++ to C translation
- Stack Overflow discussions and recommendations
- Compiler toolchain projects (LLVM-based tools, etc.)
- Programming language conversion tool directories

Thoroughly explore multiple sources and consider various perspectives on feasibility.
</scope>

<evaluation_criteria>
For each tool discovered, document:

**Essential Information:**
- Tool name and repository/website URL
- Last update date and maintenance status
- C++ feature support (which standards: C++98, C++11, C++14, C++17, C++20+)
- Installation method and platform support
- License (open source, commercial, academic-only)

**Capability Assessment:**
- What C++ features can it convert? (classes, templates, STL, RAII, exceptions, etc.)
- What C++ features does it NOT support?
- Output quality (readable C code, or machine-generated mess?)
- Does it handle the standard library? How?
- Build system integration

**Practical Viability:**
- Documentation quality
- Active community or support
- Known limitations or bugs
- Real-world usage examples or case studies
- Performance characteristics

**Why these criteria matter:** We need to determine if automated conversion is practical for production use, or if these tools are only suitable for academic/prototype work. Understanding limitations upfront prevents wasted implementation effort.
</evaluation_criteria>

<research_process>
1. **Web search** for C++ to C conversion tools, transpilers, source-to-source compilers
2. **GitHub search** with keywords: "c++ to c converter", "c++ transpiler", "cpp2c", "source-to-source c++"
3. **Academic literature search** for papers on C++ translation/lowering
4. **LLVM ecosystem** investigation (LLVM-based conversion tools)
5. **Stack Overflow and Reddit** searches for developer experiences and recommendations
6. **Alternative approaches** research if direct tools are insufficient

For each discovered tool:
- Read documentation and README files
- Check repository activity (commits, issues, stars)
- Look for example conversions or test cases
- Identify any show-stopping limitations
</research_process>

<deliverables>
Create a comprehensive research report saved to: `./research/cpp-to-c-conversion-tools.md`

Structure the report as:

```markdown
# C++ to C Conversion Tools - Research Report

## Executive Summary
[2-3 paragraphs: Are viable tools available? Overall recommendation]

## Discovered Tools

### [Tool Name 1]
- **URL**: [link]
- **Status**: [Active/Abandoned/Academic]
- **Last Updated**: [date]
- **License**: [license type]
- **C++ Support**: [which standards]
- **Capabilities**: [what it can convert]
- **Limitations**: [what it cannot convert]
- **Viability**: [High/Medium/Low for production use]
- **Notes**: [important details, gotchas, etc.]

[Repeat for each tool...]

## Comparison Matrix
| Tool | C++ Standard | Active | Open Source | Template Support | STL Handling | Production Ready |
|------|--------------|--------|-------------|------------------|--------------|------------------|
| ... | ... | ... | ... | ... | ... | ... |

## Alternative Approaches
[If direct conversion tools are inadequate, what alternatives exist?]
- Manual translation strategies
- Hybrid approaches (partial automation)
- Subset compilation (restricted C++ features)
- Other solutions

## Recommendations
1. [Primary recommendation with reasoning]
2. [Alternative approaches if primary isn't viable]
3. [Next steps for evaluation/testing]

## Sources
[List all references, URLs, papers consulted]
```
</deliverables>

<verification>
Before completing, verify:
- ✓ At least 5-7 tools/approaches have been investigated (or clear evidence that fewer exist)
- ✓ Each tool has been evaluated against the criteria above
- ✓ Modern C++ support (C++11+) has been specifically assessed
- ✓ Maintenance status is current (checked within last week)
- ✓ Practical viability is honestly assessed (not just "this exists")
- ✓ Alternative approaches are documented if direct tools are insufficient
- ✓ Clear recommendation is provided based on findings
- ✓ All sources are properly cited with working URLs

Key questions that must be answered:
1. Do production-ready C++ to C conversion tools exist?
2. What's the best tool currently available?
3. What C++ features are commonly unsupported?
4. Is automated conversion viable, or is manual translation required?
</verification>

<success_criteria>
- Comprehensive catalog of available tools with honest capability assessment
- Clear understanding of what can and cannot be automatically converted
- Actionable recommendation for next steps
- Well-organized, easy-to-reference documentation
- Research can be confidently used to make technical decisions about the project approach
</success_criteria>

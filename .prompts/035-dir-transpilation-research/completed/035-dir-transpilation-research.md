# Directory-Based Transpilation Research

<session_initialization>
Before beginning research, verify today's date:
!`date +%Y-%m-%d`

Use this date when searching for "current" or "latest" information.
</session_initialization>

<research_objective>
Research directory-based transpilation with source directory structure preservation for cpptoc.

Purpose: Enable project-level transpilation where users provide source directory, target directory, and include paths, with the transpiler automatically finding all .cpp files and preserving the source tree structure in output.

Scope: Current FileOutputManager implementation, path preservation strategies, industry standards from similar tools (compilers, transpilers), edge cases

Output: dir-transpilation-research.md with findings and recommendations
</research_objective>

<research_scope>
<include>
**Current Implementation Analysis:**
- How FileOutputManager currently generates output paths
- Where basename extraction happens (strips all path information)
- How CppToCConsumer passes filenames to FileOutputManager
- Current --output-dir implementation

**Path Preservation Approaches:**
- Relative path calculation (input path relative to source root)
- Directory mirroring strategies
- Path normalization (handling .., symlinks, absolute paths)
- Cross-platform considerations (Windows vs Unix paths)

**Industry Standards:**
- How GCC/Clang handle -o with directory structures
- How TypeScript compiler (tsc) preserves source structure
- How Babel transpiler handles directory structures
- How CMake generates output directory hierarchies

**Edge Cases:**
- Absolute input paths vs relative paths
- Symlinks in source tree
- Files outside source directory (via ../)
- Name collisions (same basename in different dirs)
- Output directory creation (when to create, permissions)

**Command-Line Interface:**
- Should users provide source dir or list files?
- Backward compatibility with current file-list approach
- How to specify source root for path calculation
</include>

<exclude>
- Implementation details (save for plan phase)
- Specific code changes (save for implementation)
- Test implementation (save for test planning)
</exclude>

<sources>
**Code Analysis (use Read tool):**
- include/FileOutputManager.h - Current API
- src/FileOutputManager.cpp - Path generation logic
- src/CppToCConsumer.cpp - How filenames are passed
- src/main.cpp - CLI argument parsing
- tests/MultiFileTranspilationTest.cpp - Current behavior expectations

**Search for Standards:**
- "compiler output directory structure preservation"
- "transpiler directory mirroring best practices"
- "relative path calculation algorithms"
</sources>
</research_scope>

<verification_checklist>
□ Read all FileOutputManager code (header and implementation)
□ Trace how input filename becomes output filename (full call chain)
□ Identify exact line where path information is stripped
□ Document current --output-dir implementation completely
□ Check how TypeScript/Babel handle directory structures
□ Verify path calculation algorithm recommendations
□ Enumerate all edge cases with examples
□ Test current behavior to understand baseline
</verification_checklist>

<research_quality_assurance>
<completeness_check>
- [ ] Current implementation fully understood (call chain documented)
- [ ] All path preservation approaches evaluated
- [ ] Industry standard practices researched
- [ ] Edge cases enumerated with test scenarios
- [ ] Backward compatibility considerations documented
</completeness_check>

<source_verification>
- [ ] Code reading confirms actual behavior (not assumptions)
- [ ] Compiler documentation cited for comparison
- [ ] Path calculation algorithms verified with examples
- [ ] Edge case handling validated
</source_verification>

<blind_spots_review>
- [ ] Checked for platform-specific path handling (Windows backslashes)
- [ ] Considered security implications (path traversal attacks)
- [ ] Verified assumptions about file system behavior
- [ ] Looked for existing path manipulation code in codebase
</blind_spots_review>
</research_quality_assurance>

<output_requirements>
Write findings incrementally to `.prompts/035-dir-transpilation-research/dir-transpilation-research.md` as you discover them:

1. Create the file with initial structure
2. As you analyze each aspect, immediately append findings
3. After all research complete, write summary, recommendations, and metadata

Structure:
```xml
<research>
  <summary>{Executive summary of findings}</summary>

  <findings>
    <finding category="current-implementation">
      <title>How FileOutputManager Strips Paths</title>
      <detail>Exact code location and logic...</detail>
      <source>src/FileOutputManager.cpp:line</source>
      <relevance>This is where we need to inject relative path preservation</relevance>
    </finding>

    <finding category="path-calculation">
      <title>Relative Path Algorithm</title>
      <detail>std::filesystem::relative() or manual calculation...</detail>
      <source>C++17 filesystem documentation</source>
      <relevance>Standard library solution vs custom implementation</relevance>
    </finding>

    <finding category="industry-standard">
      <title>TypeScript Compiler Approach</title>
      <detail>tsc --outDir mirrors src structure...</detail>
      <source>TypeScript handbook</source>
      <relevance>Users expect this behavior from transpilers</relevance>
    </finding>

    <!-- More findings for edge cases, CLI design, etc. -->
  </findings>

  <recommendations>
    <recommendation priority="high">
      <action>Modify FileOutputManager to accept source root path</action>
      <rationale>Need reference point to calculate relative paths</rationale>
    </recommendation>

    <recommendation priority="high">
      <action>Use std::filesystem::relative() for path calculation</action>
      <rationale>Standard library, cross-platform, well-tested</rationale>
    </recommendation>

    <recommendation priority="medium">
      <action>Add --source-dir CLI option (optional, for backward compat)</action>
      <rationale>When omitted, use common ancestor of input files</rationale>
    </recommendation>

    <!-- More recommendations -->
  </recommendations>

  <code_examples>
```cpp
// Example: Calculate relative path
#include <filesystem>
namespace fs = std::filesystem;

fs::path sourceRoot = "/Users/alex/project/src";
fs::path inputFile = "/Users/alex/project/src/module/file.cpp";
fs::path outputRoot = "/Users/alex/project/build";

// Calculate relative path: "module/file.cpp"
fs::path relativePath = fs::relative(inputFile, sourceRoot);

// Construct output path: "/Users/alex/project/build/module/file.c"
fs::path outputFile = outputRoot / relativePath.parent_path() / (relativePath.stem().string() + ".c");
```

```cpp
// Edge case: Input outside source root
// Input: /Users/alex/other/file.cpp
// Source: /Users/alex/project/src
// Relative: ../../../other/file.cpp
// Problem: Output would be outside target dir
// Solution: Flatten or reject
```
  </code_examples>

  <metadata>
    <confidence level="high">
      std::filesystem provides robust cross-platform solution.
      Industry standards are clear (mirror structure).
      Current implementation is straightforward to modify.
    </confidence>

    <dependencies>
      - C++17 filesystem library (already used in project)
      - Backward compatibility decision (optional --source-dir vs required)
    </dependencies>

    <open_questions>
      - Should we support files outside source root? (flatten vs reject)
      - Should --source-dir be required or auto-detected?
      - Do we need --flatten option for backward compat?
    </open_questions>

    <assumptions>
      - Users want structure preservation (validated by user requirement)
      - Project already uses C++17 (check CMakeLists.txt)
      - Source files are typically within a common root
    </assumptions>

    <quality_report>
      <sources_consulted>
        - include/FileOutputManager.h (lines X-Y)
        - src/FileOutputManager.cpp (lines X-Y)
        - src/CppToCConsumer.cpp (lines X-Y)
        - C++17 filesystem documentation
        - TypeScript handbook (directory structure behavior)
      </sources_consulted>

      <claims_verified>
        - FileOutputManager currently strips path: Verified at src/FileOutputManager.cpp:XX
        - std::filesystem::relative() exists: Verified in C++17 standard
        - TypeScript preserves structure: Verified in official docs
      </claims_verified>

      <claims_assumed>
        - Users have C++17 compiler (need to verify CMakeLists.txt minimum)
        - Performance of fs::relative() is acceptable (likely yes, but untested)
      </claims_assumed>

      <confidence_by_finding>
        - Current implementation analysis: High (code read and understood)
        - Path calculation approach: High (standard library, well-documented)
        - Industry standards: High (multiple tools researched)
        - Edge case handling: Medium (enumerated but not all solutions validated)
        - CLI design: Medium (multiple valid approaches, user preference needed)
      </confidence_by_finding>
    </quality_report>
  </metadata>
</research>
```
</output_requirements>

<summary_requirements>
Create `.prompts/035-dir-transpilation-research/SUMMARY.md`:

```markdown
# Directory-Based Transpilation Research

**Recommendation: Use std::filesystem::relative() with --source-dir option**

## Key Findings
• FileOutputManager::getFullPath() currently strips all directory information
• std::filesystem::relative() provides cross-platform path calculation
• TypeScript compiler behavior is industry standard (--outDir mirrors --rootDir)
• Need source root reference point to calculate relative paths

## Decisions Needed
• Should --source-dir be required or auto-detected from common ancestor?
• How to handle files outside source root (reject vs flatten)?
• Add --flatten flag for backward compatibility?

## Blockers
None

## Next Step
Create implementation plan (dir-transpilation-plan.md)
```
</summary_requirements>

<success_criteria>
- FileOutputManager implementation fully documented (call chain, current behavior)
- Path calculation algorithm recommended with code examples
- Industry standards researched (TypeScript, Babel, compilers)
- Edge cases enumerated with handling strategies
- CLI design options presented (with trade-offs)
- Quality report distinguishes verified facts from assumptions
- SUMMARY.md created with clear recommendation
- Ready for planning phase
</success_criteria>

# Research: Recursive File Discovery for cpptoc

<session_initialization>
Before beginning research, verify today's date:
!`date +%Y-%m-%d`

Use this date when searching for "current" or "latest" information.
</session_initialization>

<research_objective>
Research recursive `.cpp` file discovery approaches for the cpptoc transpiler to enable automatic transpilation of entire C++ projects.

**Purpose:** Enable users to transpile entire projects by specifying `--source-dir` only, without manually listing every `.cpp` file. This builds on the recently implemented directory structure preservation feature.

**Scope:** Research directory traversal approaches, edge case handling, and performance optimization for recursive file discovery in C++ codebases.

**Output:** `recursive-file-discovery-research.md` with findings on C++17 filesystem APIs, edge cases, and recommendations.
</research_objective>

<context>
**Related work:**
- @.prompts/035-dir-transpilation-research/dir-transpilation-research.md - Existing directory structure preservation research
- @.prompts/036-dir-transpilation-plan/dir-transpilation-plan.md - Directory structure preservation implementation plan

**Current implementation:**
- cpptoc already supports `--source-dir` for preserving directory structure in output
- Currently requires explicit file list on command line
- Uses `std::filesystem` for path calculations (C++17 available)
- ClangTool infrastructure already handles multiple files

**User requirement:**
When `--source-dir` is specified, the tool should:
1. Auto-discover all `.cpp` files recursively under that directory
2. Ignore individual file arguments (or error if both provided)
3. Transpile all discovered files while preserving directory structure
</context>

<research_scope>
<include>
**Directory Traversal:**
- C++17 filesystem APIs for recursive directory iteration
- Filtering for `.cpp` files (case sensitivity, extensions)
- Performance characteristics for large codebases
- Cross-platform compatibility (macOS, Linux, Windows)

**Edge Cases to Research:**
- Symlinks (follow or ignore?)
- Hidden directories (`.git`, `.svn`, `node_modules`, `build`)
- Circular symlinks detection
- Permission denied errors
- Empty directories
- Files with multiple extensions (`.test.cpp`, `.impl.cpp`)
- Case sensitivity on different filesystems

**Integration with Current Code:**
- Where to perform discovery (main.cpp before ClangTool?)
- How to populate file list for ClangTool
- Error handling and user feedback
- CLI argument validation (--source-dir vs file list conflicts)

**Performance Considerations:**
- Large monorepos (100k+ files)
- Network filesystems
- Caching or memoization opportunities
- Early termination on errors
</include>

<exclude>
- Build system integration (CMake, Makefiles) - out of scope
- File watching or incremental transpilation - future feature
- Multi-threaded file discovery - premature optimization
- Database caching - unnecessary complexity
</exclude>

<sources>
**C++17 Filesystem API:**
- https://en.cppreference.com/w/cpp/filesystem/recursive_directory_iterator
- Search: "C++17 recursive directory iteration best practices {current_year}"
- Search: "std::filesystem recursive_directory_iterator performance"

**Cross-platform Considerations:**
- Search: "C++17 filesystem symlink handling cross-platform"
- Search: "std::filesystem case sensitivity macOS Linux Windows"

**Edge Case Handling:**
- Search: "recursive directory traversal skip hidden directories C++"
- Search: "filesystem permission denied error handling C++"
- Search: "detecting circular symlinks std::filesystem"

**Industry Examples:**
- Clang-tidy, clang-format source discovery
- TypeScript compiler file discovery
- Babel transpiler file discovery
</sources>
</research_scope>

<verification_checklist>
□ Verify ALL std::filesystem recursive iteration APIs:
  □ `std::filesystem::recursive_directory_iterator` - main API
  □ `directory_options` flags - skip_permission_denied, follow_directory_symlink
  □ Error handling mechanisms - exceptions vs error_code
  □ Path filtering - extension matching, exclude patterns

□ Document exact file locations/URLs for each API
□ Verify symlink behavior on different platforms
□ Confirm error handling best practices from official sources
□ Check for recent updates or changes to filesystem library
□ Test multiple search queries to avoid missing information
□ Check for Clang/LLVM specific file discovery patterns

**For all research:**
□ Verify negative claims ("X is not possible") with official docs
□ Confirm all primary claims have authoritative sources
□ Check both current docs AND recent updates/changelogs
□ Test multiple search queries to avoid missing information
□ Check for environment/tool-specific variations
</verification_checklist>

<research_quality_assurance>
Before completing research, perform these checks:

<completeness_check>
- [ ] All filesystem iteration APIs documented with evidence
- [ ] Each edge case evaluated with handling approach
- [ ] Official C++ reference documentation cited
- [ ] Cross-platform differences identified
- [ ] Performance characteristics analyzed
</completeness_check>

<source_verification>
- [ ] Primary claims backed by cppreference.com or official C++ docs
- [ ] Actual URLs provided (not just "search for X")
- [ ] Distinguish verified facts from assumptions
- [ ] Real-world examples from existing tools cited
</source_verification>

<blind_spots_review>
Ask yourself: "What might I have missed?"
- [ ] Are there directory traversal edge cases I didn't investigate?
- [ ] Did I check for multiple file extension patterns (.cpp, .cxx, .cc)?
- [ ] Did I verify symlink behavior across platforms?
- [ ] Did I look for existing Clang tool patterns for file discovery?
</blind_spots_review>

<critical_claims_audit>
For any statement like "X is not possible" or "Y is the only way":
- [ ] Is this verified by official documentation?
- [ ] Have I checked for existing tool implementations?
- [ ] Are there alternative approaches I haven't considered?
</critical_claims_audit>
</research_quality_assurance>

<output_structure>
Save to: `.prompts/038-recursive-file-discovery-research/recursive-file-discovery-research.md`

Write findings incrementally to avoid token limit failures:

1. Create the file with this initial structure:
   ```xml
   <research>
     <summary>[Will complete at end]</summary>
     <findings></findings>
     <recommendations></recommendations>
     <code_examples></code_examples>
     <metadata></metadata>
   </research>
   ```

2. As you research each aspect, immediately append findings:
   - Research filesystem APIs → Write finding
   - Discover edge case → Write finding
   - Find code example → Append to code_examples

3. After all research complete:
   - Write summary (synthesize all findings)
   - Write recommendations (based on findings)
   - Write metadata (confidence, dependencies, etc.)

Structure findings using this XML format:

```xml
<research>
  <summary>
    {2-3 paragraph executive summary of key findings}
  </summary>

  <findings>
    <finding category="filesystem-apis">
      <title>std::filesystem::recursive_directory_iterator</title>
      <detail>{Detailed explanation of API, options, behavior}</detail>
      <source>https://en.cppreference.com/...</source>
      <relevance>Primary mechanism for recursive file discovery</relevance>
    </finding>

    <finding category="edge-cases">
      <title>Symlink Handling</title>
      <detail>{How to detect, follow, or skip symlinks}</detail>
      <source>{Reference}</source>
      <relevance>Critical for avoiding infinite loops</relevance>
    </finding>

    <!-- Additional findings for performance, cross-platform, integration -->
  </findings>

  <recommendations>
    <recommendation priority="high">
      <action>Use recursive_directory_iterator with skip_permission_denied</action>
      <rationale>Prevents crashes on restricted directories, matches Clang tool behavior</rationale>
    </recommendation>

    <recommendation priority="high">
      <action>Follow symlinks by default to match user expectations</action>
      <rationale>C++ projects often use symlinks for dependencies</rationale>
    </recommendation>

    <recommendation priority="medium">
      <action>Exclude .git, .svn, build, node_modules directories</action>
      <rationale>Common patterns that should never contain transpilable source</rationale>
    </recommendation>

    <!-- Additional recommendations -->
  </recommendations>

  <code_examples>
    <example name="basic-recursive-iteration">
```cpp
#include <filesystem>
#include <vector>
#include <string>

namespace fs = std::filesystem;

std::vector<std::string> discoverCppFiles(const std::string& sourceDir) {
    std::vector<std::string> cppFiles;

    try {
        auto options = fs::directory_options::skip_permission_denied
                     | fs::directory_options::follow_directory_symlink;

        for (const auto& entry : fs::recursive_directory_iterator(sourceDir, options)) {
            if (entry.is_regular_file()) {
                auto ext = entry.path().extension();
                if (ext == ".cpp" || ext == ".cxx" || ext == ".cc") {
                    cppFiles.push_back(entry.path().string());
                }
            }
        }
    } catch (const fs::filesystem_error& e) {
        // Handle error
    }

    return cppFiles;
}
```
Source: Based on std::filesystem documentation patterns
    </example>

    <example name="exclude-patterns">
```cpp
// Common directories to skip
const std::set<std::string> excludeDirs = {
    ".git", ".svn", ".hg",
    "build", "cmake-build-debug", "cmake-build-release",
    "node_modules", ".cache"
};

bool shouldSkipDirectory(const fs::path& dir) {
    std::string dirname = dir.filename().string();
    return excludeDirs.find(dirname) != excludeDirs.end();
}
```
    </example>
  </code_examples>

  <metadata>
    <confidence level="{high|medium|low}">
      {Justification based on source quality and verification}
    </confidence>

    <dependencies>
      - C++17 compiler with full filesystem support
      - No additional libraries needed
    </dependencies>

    <open_questions>
      - Should we provide --exclude-dir option for custom exclusions?
      - Support for .c++ extension variant?
      - CLI flag for controlling symlink behavior?
    </open_questions>

    <assumptions>
      - Users want symlinks followed (can be made configurable)
      - Standard exclude patterns (.git, build, etc.) are universal
      - Case-insensitive extension matching not needed (Unix conventions)
    </assumptions>

    <quality_report>
      <sources_consulted>
        https://en.cppreference.com/w/cpp/filesystem
        {Other official documentation URLs}
      </sources_consulted>

      <claims_verified>
        - recursive_directory_iterator behavior with symlinks (official docs)
        - directory_options flags (C++ standard)
        - Cross-platform path handling (verified on multiple platforms)
      </claims_verified>

      <claims_assumed>
        - User expectations for symlink following (based on common practice)
        - Standard exclude patterns (based on ecosystem conventions)
      </claims_assumed>

      <contradictions_encountered>
        {Any conflicting information found and how resolved}
      </contradictions_encountered>

      <confidence_by_finding>
        - Filesystem API behavior: High (official C++ reference)
        - Symlink handling: High (tested across platforms)
        - Exclude patterns: Medium (based on convention, not standard)
        - Performance characteristics: Medium (no official benchmarks)
      </confidence_by_finding>
    </quality_report>
  </metadata>
</research>
```
</output_structure>

<pre_submission_checklist>
Before submitting your research report, confirm:

**Scope Coverage**
- [ ] All filesystem APIs for recursive iteration documented
- [ ] Each edge case from verification checklist documented
- [ ] Official documentation cited for all critical claims
- [ ] Cross-platform differences identified

**Claim Verification**
- [ ] Symlink behavior verified with official docs
- [ ] Permission error handling verified
- [ ] Extension matching approaches verified
- [ ] URLs to official documentation included

**Quality Controls**
- [ ] Blind spots review completed ("What did I miss?")
- [ ] Quality report section filled out honestly
- [ ] Confidence levels assigned with justification
- [ ] Assumptions clearly distinguished from verified facts

**Output Completeness**
- [ ] All required XML sections present
- [ ] SUMMARY.md created with substantive one-liner
- [ ] Sources consulted listed with URLs
- [ ] Next steps clearly identified (create plan)
</pre_submission_checklist>

<summary_requirements>
Create `.prompts/038-recursive-file-discovery-research/SUMMARY.md`

Template:
```markdown
# Recursive File Discovery Research Summary

**{Substantive one-liner - e.g., "recursive_directory_iterator with skip_permission_denied recommended for robust file discovery"}**

## Key Findings
- {Most important API recommendation}
- {Critical edge case handling}
- {Performance or cross-platform consideration}

## Decisions Needed
{Specific decisions requiring user input, or "None"}

## Blockers
None

## Next Step
Create recursive-file-discovery-plan.md

---
*Confidence: {High|Medium|Low}*
*Full output: recursive-file-discovery-research.md*
```
</summary_requirements>

<success_criteria>
- All scope questions answered with official sources
- All verification checklist items completed
- Filesystem APIs are current (C++17) and well-documented
- Edge cases have concrete handling approaches
- Recommendations are actionable and prioritized
- Code examples are compilable and correct
- Metadata captures gaps and assumptions honestly
- Quality report distinguishes verified from assumed
- SUMMARY.md created with substantive one-liner
- Ready for planning phase to consume findings
</success_criteria>

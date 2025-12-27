# Plan: Recursive File Discovery Implementation

<objective>
Create a phased implementation plan for adding recursive `.cpp` file discovery to the cpptoc transpiler.

**Purpose:** Enable project-level transpilation where users specify `--source-dir` only, and all `.cpp` files are automatically discovered and transpiled with preserved directory structure.

**Input:** Research findings from recursive-file-discovery-research.md

**Output:** `recursive-file-discovery-plan.md` with 3-4 actionable implementation phases
</objective>

<context>
**Research findings:** @.prompts/038-recursive-file-discovery-research/recursive-file-discovery-research.md

**Related work:**
- @.prompts/035-dir-transpilation-research/dir-transpilation-research.md - Directory structure preservation (already implemented)
- @.prompts/036-dir-transpilation-plan/dir-transpilation-plan.md - Directory structure implementation plan

**Current implementation state:**
- `--source-dir` flag exists and enables directory structure preservation
- Users must still provide explicit file list on command line
- FileOutputManager uses `--source-dir` for relative path calculation
- ClangTool infrastructure handles multiple files
- Uses C++17 std::filesystem throughout

**Target behavior:**
```bash
# Current (verbose, error-prone):
cpptoc --source-dir=src/ --output-dir=build/ src/foo.cpp src/bar.cpp ...

# Target (automatic):
cpptoc --source-dir=src/ --output-dir=build/
# Automatically discovers all .cpp files in src/ recursively
```
</context>

<planning_requirements>
**Must address:**
1. Where to add file discovery logic (main.cpp before ClangTool invocation)
2. CLI argument validation (prevent conflicts between --source-dir and file list)
3. Edge case handling (symlinks, permission errors, exclude patterns)
4. User feedback (show discovered files, error messages)
5. Backward compatibility (existing file list usage must still work)
6. Testing strategy (unit tests for discovery, integration tests for E2E)

**Constraints:**
- Maintain backward compatibility (no breaking changes)
- Use existing C++17 std::filesystem (no new dependencies)
- Follow existing code patterns in main.cpp and FileOutputManager
- Preserve all current CLI options and behavior
- Performance acceptable for large codebases (10k+ files)

**Success criteria:**
- `cpptoc --source-dir=tests/real-world --output-dir=out/` discovers and transpiles all .cpp files
- Existing usage with explicit file lists continues working
- Error messages guide users when arguments conflict
- Tests verify discovery logic and integration
- Documentation explains new usage pattern
</planning_requirements>

<output_structure>
Save to: `.prompts/039-recursive-file-discovery-plan/recursive-file-discovery-plan.md`

Structure the plan using this XML format:

```xml
<plan>
  <summary>
    {One paragraph overview of the 3-4 phase approach}

    Key strategy:
    - Phase 1: Core file discovery function in main.cpp
    - Phase 2: CLI integration and validation
    - Phase 3: Testing (unit + integration)
    - Phase 4: Documentation and examples
  </summary>

  <phases>
    <phase number="1" name="core-file-discovery">
      <objective>
        Implement recursive file discovery function using std::filesystem::recursive_directory_iterator
      </objective>

      <tasks>
        <task priority="high">Create discoverSourceFiles() function in main.cpp</task>
        <task priority="high">Implement extension filtering (.cpp, .cxx, .cc)</task>
        <task priority="high">Add exclude pattern matching (.git, build, node_modules)</task>
        <task priority="high">Handle filesystem errors (permission denied, symlink loops)</task>
        <task priority="medium">Add logging/diagnostics for discovered files</task>
        <task priority="low">Consider circular symlink detection</task>
      </tasks>

      <deliverables>
        <deliverable>discoverSourceFiles(const std::string& sourceDir) function</deliverable>
        <deliverable>Error handling for filesystem exceptions</deliverable>
        <deliverable>File count and list output for user feedback</deliverable>
      </deliverables>

      <implementation_details>
        Based on research findings:
        - Use recursive_directory_iterator with directory_options::skip_permission_denied
        - Follow symlinks by default (directory_options::follow_directory_symlink)
        - Match extensions: .cpp, .cxx, .cc (case-sensitive)
        - Exclude standard patterns: .git, .svn, build*, cmake-build*, node_modules
        - Return vector&lt;std::string&gt; of absolute paths

        Location: Add to main.cpp before ClangTool::run() invocation

        Example signature:
        ```cpp
        std::vector&lt;std::string&gt; discoverSourceFiles(
            const std::string& sourceDir,
            std::error_code& ec
        );
        ```
      </implementation_details>

      <dependencies>
        None - C++17 filesystem already available
      </dependencies>

      <verification>
        - Manually test with tests/real-world/ directory
        - Verify correct file count (11 .cpp files expected)
        - Verify excluded directories (.git, build*) are skipped
        - Test permission denied handling (create restricted directory)
        - Test symlink following behavior
      </verification>
    </phase>

    <phase number="2" name="cli-integration">
      <objective>
        Integrate file discovery with CLI argument parsing and add validation logic
      </objective>

      <tasks>
        <task priority="high">Detect when --source-dir is specified without file arguments</task>
        <task priority="high">Call discoverSourceFiles() to populate file list</task>
        <task priority="high">Validate mutual exclusivity (--source-dir alone vs file list)</task>
        <task priority="medium">Add --dry-run flag to show discovered files without transpiling</task>
        <task priority="medium">Add user feedback: "Discovered N files in SOURCE_DIR"</task>
        <task priority="low">Consider --exclude-dir option for custom exclusions</task>
      </tasks>

      <deliverables>
        <deliverable>Automatic file discovery when --source-dir specified without files</deliverable>
        <deliverable>Clear error message if both --source-dir and file list provided</deliverable>
        <deliverable>Optional --dry-run for preview</deliverable>
      </deliverables>

      <implementation_details>
        Modify main() function logic:

        ```cpp
        // After argument parsing
        std::vector&lt;std::string&gt; sourceFiles;

        if (!SourceDir.empty() && SourcePaths.empty()) {
            // Auto-discovery mode
            std::error_code ec;
            sourceFiles = discoverSourceFiles(SourceDir, ec);

            if (ec) {
                llvm::errs() &lt;&lt; "Error discovering files: " &lt;&lt; ec.message() &lt;&lt; "\n";
                return 1;
            }

            if (sourceFiles.empty()) {
                llvm::errs() &lt;&lt; "No .cpp files found in " &lt;&lt; SourceDir &lt;&lt; "\n";
                return 1;
            }

            llvm::outs() &lt;&lt; "Discovered " &lt;&lt; sourceFiles.size()
                         &lt;&lt; " files in " &lt;&lt; SourceDir &lt;&lt; "\n";
        } else if (!SourceDir.empty() && !SourcePaths.empty()) {
            // Conflict: both specified
            llvm::errs() &lt;&lt; "Error: Cannot specify both --source-dir and individual files\n"
                         &lt;&lt; "Use --source-dir alone for auto-discovery, or provide files without --source-dir\n";
            return 1;
        } else {
            // Legacy mode: use provided file list
            sourceFiles = SourcePaths;
        }

        // Continue with ClangTool using sourceFiles
        ```

        Decision points:
        - Should we allow mixing? NO - clear semantics preferred
        - Should we default to auto-discovery? NO - explicit --source-dir required
        - Should --output-dir be required with --source-dir? RECOMMEND but don't enforce
      </implementation_details>

      <dependencies>
        Phase 1 complete (discoverSourceFiles function exists)
      </dependencies>

      <verification>
        - Test auto-discovery: cpptoc --source-dir=tests/real-world --output-dir=out/
        - Test error case: cpptoc --source-dir=tests/real-world file.cpp (should error)
        - Test legacy mode: cpptoc file1.cpp file2.cpp (should work as before)
        - Test --dry-run: cpptoc --source-dir=tests/real-world --dry-run (show files, no transpile)
        - Test no files found: cpptoc --source-dir=empty-dir (graceful error)
      </verification>
    </phase>

    <phase number="3" name="comprehensive-testing">
      <objective>
        Create unit tests for discovery logic and integration tests for E2E workflows
      </objective>

      <tasks>
        <task priority="high">Create FileDiscoveryTest.cpp with unit tests</task>
        <task priority="high">Test basic discovery (find .cpp files)</task>
        <task priority="high">Test exclusion patterns (.git, build directories)</task>
        <task priority="high">Test permission denied handling</task>
        <task priority="high">Test symlink following</task>
        <task priority="high">Add integration test to MultiFileTranspilationTest.cpp</task>
        <task priority="medium">Test empty directory case</task>
        <task priority="medium">Test deeply nested directories</task>
        <task priority="low">Performance test with large directory (1000+ files)</task>
      </tasks>

      <deliverables>
        <deliverable>tests/FileDiscoveryTest.cpp - Unit tests for discovery function</deliverable>
        <deliverable>Extended MultiFileTranspilationTest - Integration test for auto-discovery</deliverable>
        <deliverable>All tests passing (backward compatibility + new feature)</deliverable>
      </deliverables>

      <implementation_details>
        Unit test structure (FileDiscoveryTest.cpp):
        ```cpp
        TEST_F(FileDiscoveryTest, DiscoverBasicCppFiles) {
            // Create temp directory with .cpp files
            CreateTestFile(tempDir / "file1.cpp", content);
            CreateTestFile(tempDir / "file2.cpp", content);
            CreateTestFile(tempDir / "file.h", content); // Should be excluded

            auto files = discoverSourceFiles(tempDir.string(), ec);

            ASSERT_EQ(files.size(), 2);
            EXPECT_TRUE(contains(files, "file1.cpp"));
            EXPECT_TRUE(contains(files, "file2.cpp"));
        }

        TEST_F(FileDiscoveryTest, ExcludesGitDirectory) {
            CreateTestFile(tempDir / ".git/hooks/pre-commit.cpp", content);
            CreateTestFile(tempDir / "src/main.cpp", content);

            auto files = discoverSourceFiles(tempDir.string(), ec);

            ASSERT_EQ(files.size(), 1);
            EXPECT_TRUE(contains(files, "src/main.cpp"));
        }

        TEST_F(FileDiscoveryTest, FollowsSymlinks) {
            CreateTestFile(tempDir / "real/file.cpp", content);
            fs::create_directory_symlink(tempDir / "real", tempDir / "link");

            auto files = discoverSourceFiles(tempDir.string(), ec);

            EXPECT_GE(files.size(), 1); // Should find file via symlink
        }
        ```

        Integration test (MultiFileTranspilationTest.cpp):
        ```cpp
        TEST_F(MultiFileTranspilationTest, AutoDiscovery_SourceDirMode) {
            // Create structure: temp/src/{module1,module2}/file.cpp
            CreateTestFile(tempDir / "src/module1/file1.cpp", simpleCppContent);
            CreateTestFile(tempDir / "src/module2/file2.cpp", simpleCppContent);
            CreateTestFile(tempDir / "src/.git/file.cpp", simpleCppContent); // Excluded

            // Run with --source-dir only (no file list)
            RunTranspiler({}, { // Empty file list
                "--source-dir=" + (tempDir / "src").string(),
                "--output-dir=" + (tempDir / "out").string()
            });

            // Verify structure preserved and all files transpiled
            ASSERT_TRUE(fs::exists(tempDir / "out/module1/file1.c"));
            ASSERT_TRUE(fs::exists(tempDir / "out/module2/file2.c"));
            ASSERT_FALSE(fs::exists(tempDir / "out/.git/file.c")); // Excluded
        }
        ```
      </implementation_details>

      <dependencies>
        Phase 1 and 2 complete (function exists and integrated with CLI)
      </dependencies>

      <verification>
        - All unit tests pass (FileDiscoveryTest)
        - All integration tests pass (MultiFileTranspilationTest)
        - All existing tests still pass (backward compatibility)
        - Test coverage >80% for new code
        - No regressions in existing functionality
      </verification>
    </phase>

    <phase number="4" name="documentation">
      <objective>
        Update documentation to explain automatic file discovery and new usage patterns
      </objective>

      <tasks>
        <task priority="high">Update README.md with auto-discovery examples</task>
        <task priority="high">Update docs/MULTI_FILE_TRANSPILATION.md with new workflow</task>
        <task priority="high">Update cpptoc --help text for --source-dir</task>
        <task priority="medium">Add FAQ entry about file discovery</task>
        <task priority="medium">Update real-world example scripts to use auto-discovery</task>
        <task priority="low">Create migration guide for users with shell scripts</task>
      </tasks>

      <deliverables>
        <deliverable>Updated README.md with before/after examples</deliverable>
        <deliverable>Enhanced MULTI_FILE_TRANSPILATION.md guide</deliverable>
        <deliverable>Improved --help output</deliverable>
        <deliverable>Updated scripts/transpile-real-world.sh</deliverable>
      </deliverables>

      <implementation_details>
        README.md addition:
        ```markdown
        ## Automatic File Discovery

        Transpile entire projects by specifying the source directory:

        ```bash
        # Automatically discover and transpile all .cpp files
        cpptoc --source-dir=./src --output-dir=./build
        ```

        This will:
        - Recursively find all `.cpp`, `.cxx`, and `.cc` files in `src/`
        - Preserve directory structure in `build/`
        - Skip common directories (.git, build, node_modules)
        - Follow symlinks

        ### Before (Manual File Lists)
        ```bash
        cpptoc src/foo.cpp src/bar.cpp src/baz.cpp --output-dir=build/
        ```

        ### After (Automatic Discovery)
        ```bash
        cpptoc --source-dir=src/ --output-dir=build/
        ```

        ### Preview Discovered Files
        ```bash
        cpptoc --source-dir=src/ --dry-run
        ```
        ```

        Help text update:
        ```cpp
        static llvm::cl::opt&lt;std::string&gt; SourceDir(
            "source-dir",
            llvm::cl::desc(
                "Source root directory. When specified without file arguments, "
                "automatically discovers all .cpp files recursively. "
                "Also used to preserve directory structure in output."
            ),
            llvm::cl::value_desc("directory"),
            llvm::cl::cat(ToolCategory));
        ```
      </implementation_details>

      <dependencies>
        Phases 1-3 complete (feature fully implemented and tested)
      </dependencies>

      <verification>
        - README examples are accurate and runnable
        - Help text is clear and complete
        - Documentation covers common use cases
        - Migration path from old to new usage is clear
        - Real-world example scripts work with new approach
      </verification>
    </phase>
  </phases>

  <metadata>
    <confidence level="high">
      Plan is straightforward extension of existing functionality.
      Research provides clear implementation approach.
      Backward compatibility is maintainable.
    </confidence>

    <dependencies>
      - C++17 filesystem support (already available)
      - Existing --source-dir implementation (already complete)
      - ClangTool infrastructure (already in use)
    </dependencies>

    <open_questions>
      - Should --dry-run also show excluded directories? (Useful for debugging)
      - Should we log discovered files to stderr or stdout? (stdout preferred)
      - Should we support .c++ extension variant? (Defer unless user requests)
      - Should we add --include-pattern for custom extensions? (Future enhancement)
    </open_questions>

    <assumptions>
      - Users prefer automatic discovery over manual file lists for project-level transpilation
      - Standard exclude patterns (.git, build) are acceptable defaults
      - Following symlinks is expected behavior (can add --no-follow-symlinks later if needed)
      - Conflicting arguments (--source-dir + file list) should error, not auto-resolve
      - Performance is acceptable for typical C++ projects (< 10k files)
    </assumptions>
  </metadata>
</plan>
```
</output_structure>

<summary_requirements>
Create `.prompts/039-recursive-file-discovery-plan/SUMMARY.md`

Template:
```markdown
# Recursive File Discovery Plan Summary

**4-phase implementation: core discovery → CLI integration → comprehensive testing → documentation**

## Phase Breakdown

### Phase 1: Core File Discovery (2-3 hours)
- Implement discoverSourceFiles() using recursive_directory_iterator
- Extension filtering, exclude patterns, error handling

### Phase 2: CLI Integration (1-2 hours)
- Auto-discovery when --source-dir specified alone
- Validation logic to prevent argument conflicts
- User feedback and --dry-run support

### Phase 3: Comprehensive Testing (2-3 hours)
- Unit tests for discovery function (FileDiscoveryTest.cpp)
- Integration tests for E2E workflow (MultiFileTranspilationTest)
- Backward compatibility verification

### Phase 4: Documentation (1 hour)
- Update README, MULTI_FILE_TRANSPILATION.md, help text
- Migrate example scripts to use auto-discovery

## Decisions Needed
- Should --dry-run show excluded directories? (Recommend: yes, for debugging)
- Should we support .c++ extension? (Recommend: defer unless requested)

## Blockers
None

## Next Step
Execute Phase 1: Implement core file discovery function

---
*Confidence: High*
*Total Effort: 6-9 hours*
*Full plan: recursive-file-discovery-plan.md*
```
</summary_requirements>

<success_criteria>
- Plan addresses all requirements from research
- Phases are sequential and independently testable
- Tasks are specific and actionable
- Each phase has clear deliverables and verification
- Backward compatibility explicitly maintained
- Testing strategy is comprehensive
- Documentation covers migration path
- Metadata captures assumptions needing validation
- SUMMARY.md created with phase overview and effort estimates
- Ready for implementation phase to execute
</success_criteria>

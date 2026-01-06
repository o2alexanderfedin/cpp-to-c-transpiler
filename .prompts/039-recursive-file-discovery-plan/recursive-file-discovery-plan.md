# Implementation Plan: Recursive File Discovery for cpptoc

**Created:** 2025-12-23
**Status:** Ready for Execution
**Based On:** `.prompts/038-recursive-file-discovery-research/recursive-file-discovery-research.md`

---

<plan>

## Executive Summary

This plan implements automatic recursive `.cpp` file discovery for the cpptoc transpiler. When users specify `--source-dir` without individual file arguments, cpptoc will automatically discover all C++ source files in the directory tree, excluding build artifacts and version control directories.

**Strategic Goal:** Enhance user experience by eliminating manual file enumeration for project-level transpilation, differentiating cpptoc from Clang tools (clang-tidy, clang-format) which lack this feature.

**Implementation Complexity:** LOW (~100 lines of code)
**Risk Level:** LOW (mature C++17 APIs, graceful failure modes)
**Backward Compatibility:** PRESERVED (existing usage unchanged)

---

## Implementation Phases

<phases>

### Phase 1: Core File Discovery Implementation

**Objective:** Implement the `discoverSourceFiles()` function using `std::filesystem::recursive_directory_iterator` with robust error handling and directory exclusion.

**Duration Estimate:** 2-3 hours

<phase id="1" name="Core File Discovery">

#### Tasks

**1.1 Create File Discovery Function** (Priority: HIGH)
- **Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/main.cpp` (inline) OR new utility file
- **Function Signature:**
  ```cpp
  std::vector<std::string> discoverSourceFiles(
      const std::string& sourceDir,
      const std::vector<std::string>& excludeDirs = {
          ".git", ".svn", ".hg",
          "node_modules", "vendor"
      }
  );
  ```

- **Implementation Details:**
  ```cpp
  #include <filesystem>
  #include <vector>
  #include <string>
  #include <unordered_set>

  namespace fs = std::filesystem;

  // Helper: Check if file has valid C++ source extension
  bool isCppSourceFile(const fs::path& path) {
      static const std::unordered_set<std::string> validExtensions = {
          ".cpp", ".cxx", ".cc"
      };
      return validExtensions.contains(path.extension().string());
  }

  // Helper: Check if directory should be excluded
  bool shouldExcludeDirectory(const std::string& dirName,
                              const std::vector<std::string>& excludeDirs) {
      // Exact matches
      for (const auto& exclude : excludeDirs) {
          if (dirName == exclude) return true;
      }

      // Prefix patterns
      if (dirName.starts_with("build")) return true;         // build, build-debug, etc.
      if (dirName.starts_with("cmake-build-")) return true;  // CLion build dirs
      if (dirName.starts_with(".") && dirName != "..") return true;  // Hidden dirs

      return false;
  }

  // Main discovery function
  std::vector<std::string> discoverSourceFiles(
      const std::string& sourceDir,
      const std::vector<std::string>& excludeDirs) {

      std::vector<std::string> discoveredFiles;

      // Validate source directory
      fs::path sourcePath(sourceDir);
      if (!fs::exists(sourcePath)) {
          llvm::errs() << "Error: Source directory does not exist: "
                       << sourceDir << "\n";
          return discoveredFiles;
      }

      if (!fs::is_directory(sourcePath)) {
          llvm::errs() << "Error: Not a directory: " << sourceDir << "\n";
          return discoveredFiles;
      }

      // Configure directory iteration options
      fs::directory_options opts =
          fs::directory_options::skip_permission_denied;

      // Recursively iterate directory tree
      std::error_code ec;
      for (auto it = fs::recursive_directory_iterator(sourcePath, opts, ec);
           it != fs::recursive_directory_iterator();
           it.increment(ec)) {

          if (ec) {
              llvm::errs() << "Warning: " << ec.message()
                          << " for " << it->path() << "\n";
              ec.clear();
              continue;
          }

          // Skip excluded directories
          if (it->is_directory()) {
              std::string dirName = it->path().filename().string();
              if (shouldExcludeDirectory(dirName, excludeDirs)) {
                  it.disable_recursion_pending();  // Don't descend
                  continue;
              }
          }

          // Collect C++ source files
          if (it->is_regular_file() && isCppSourceFile(it->path())) {
              // Use absolute paths for consistency
              discoveredFiles.push_back(
                  fs::absolute(it->path()).string()
              );
          }
      }

      return discoveredFiles;
  }
  ```

**1.2 Add Validation Logic** (Priority: HIGH)
- Validate source directory exists before scanning
- Handle permission denied gracefully (skip with warning)
- Handle empty directory (return empty vector, not error)
- Return absolute paths for consistency

**1.3 Add User Feedback** (Priority: MEDIUM)
- Log discovered file count: `"Discovered N file(s) in DIR"`
- Optional: Log breakdown by extension (`.cpp`, `.cxx`, `.cc`)
- Warning when zero files found

#### Deliverables
- ✅ `discoverSourceFiles()` function implemented
- ✅ Helper functions: `isCppSourceFile()`, `shouldExcludeDirectory()`
- ✅ Error handling for invalid directories, permission denied
- ✅ User feedback logging

#### Dependencies
- C++17 `<filesystem>` header (already used in cpptoc)
- LLVM diagnostic APIs (`llvm::errs()`, `llvm::outs()`)

#### Verification Steps
1. Manual test: Call `discoverSourceFiles("tests/")` from `main()`
2. Verify correct file count and paths
3. Verify excluded directories are skipped (`.git`, `build/`)
4. Verify permission denied is handled gracefully
5. Verify empty directory returns empty vector

</phase>

---

### Phase 2: CLI Integration

**Objective:** Integrate file discovery with command-line argument parsing, adding validation to prevent conflicting options.

**Duration Estimate:** 1-2 hours

<phase id="2" name="CLI Integration">

#### Tasks

**2.1 Modify main() Argument Flow** (Priority: HIGH)
- **Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/main.cpp`
- **Integration Point:** After `CommonOptionsParser` creation, before `ClangTool` construction

- **Implementation:**
  ```cpp
  int main(int argc, const char **argv) {
      // ... existing setup code ...

      // Parse arguments
      auto ExpectedParser = CommonOptionsParser::create(argc, argv, CppToCCategory);
      if (!ExpectedParser) {
          llvm::errs() << ExpectedParser.takeError();
          return 1;
      }

      CommonOptionsParser &OptionsParser = ExpectedParser.get();

      // === NEW FILE DISCOVERY LOGIC ===
      std::vector<std::string> sourceFiles;
      const auto& providedFiles = OptionsParser.getSourcePathList();

      if (!SourceDir.empty() && !providedFiles.empty()) {
          // CONFLICT: Both --source-dir and file arguments provided
          llvm::errs() << "Error: Cannot specify both --source-dir and "
                       << "individual file arguments.\n"
                       << "Use --source-dir for auto-discovery OR "
                       << "provide explicit file list.\n";
          return 1;
      }

      if (!SourceDir.empty() && providedFiles.empty()) {
          // AUTO-DISCOVERY MODE
          llvm::outs() << "Auto-discovering C++ source files in: "
                       << SourceDir << "\n";

          sourceFiles = discoverSourceFiles(SourceDir);

          if (sourceFiles.empty()) {
              llvm::errs() << "Warning: No C++ source files (.cpp, .cxx, .cc) "
                          << "found in " << SourceDir << "\n";
              return 1;  // Non-fatal error code
          }

          llvm::outs() << "Discovered " << sourceFiles.size()
                       << " file(s) for transpilation\n";
      } else {
          // LEGACY MODE: Use provided file list
          sourceFiles.assign(providedFiles.begin(), providedFiles.end());
      }

      // Create ClangTool with discovered or provided files
      ClangTool Tool(OptionsParser.getCompilations(), sourceFiles);

      // ... rest of existing code ...
  }
  ```

**2.2 Update Error Messages** (Priority: MEDIUM)
- Clear error when both `--source-dir` and files provided
- Helpful suggestion: "Use --source-dir OR file list, not both"
- Warning (not error) when zero files discovered

**2.3 Preserve Backward Compatibility** (Priority: HIGH)
- Ensure existing usage continues working:
  ```bash
  cpptoc file1.cpp file2.cpp --output-dir=build/
  ```
- Only activate auto-discovery when:
  - `--source-dir` is specified AND
  - No individual file arguments provided

#### Deliverables
- ✅ `main()` updated with auto-discovery logic
- ✅ Validation prevents conflicting `--source-dir` + file arguments
- ✅ User feedback for auto-discovery mode
- ✅ Backward compatibility preserved

#### Dependencies
- Phase 1: `discoverSourceFiles()` function
- Existing CLI parsing infrastructure (`CommonOptionsParser`)

#### Verification Steps
1. Test auto-discovery mode:
   ```bash
   ./cpptoc --source-dir=tests/integration/ --output-dir=build/
   ```
2. Test legacy mode (unchanged):
   ```bash
   ./cpptoc tests/basic.cpp --output-dir=build/
   ```
3. Test conflict detection:
   ```bash
   ./cpptoc tests/basic.cpp --source-dir=tests/ --output-dir=build/
   # Should error: "Cannot specify both --source-dir and individual files"
   ```
4. Test empty directory:
   ```bash
   mkdir /tmp/empty-test
   ./cpptoc --source-dir=/tmp/empty-test --output-dir=build/
   # Should warn: "No C++ source files found"
   ```

</phase>

---

### Phase 3: Testing

**Objective:** Create comprehensive unit tests and integration tests to ensure correctness and edge case handling.

**Duration Estimate:** 3-4 hours

<phase id="3" name="Testing">

#### Tasks

**3.1 Unit Tests for discoverSourceFiles()** (Priority: HIGH)
- **Location:** New test file or existing test suite
- **Framework:** Google Test (already used in project)

- **Test Cases:**
  ```cpp
  // Test file: tests/unit/FileDiscoveryTest.cpp

  #include <gtest/gtest.h>
  #include <filesystem>
  #include "main.cpp"  // Or extract to utility header

  namespace fs = std::filesystem;

  class FileDiscoveryTest : public ::testing::Test {
  protected:
      void SetUp() override {
          // Create test directory structure
          testDir = fs::temp_directory_path() / "cpptoc-discovery-test";
          fs::create_directories(testDir);
          fs::create_directories(testDir / "src");
          fs::create_directories(testDir / ".git");
          fs::create_directories(testDir / "build");
          fs::create_directories(testDir / "src/subdir");
      }

      void TearDown() override {
          fs::remove_all(testDir);
      }

      fs::path testDir;
  };

  TEST_F(FileDiscoveryTest, DiscoversCppFiles) {
      // Create test files
      createFile(testDir / "main.cpp");
      createFile(testDir / "src/module.cpp");
      createFile(testDir / "src/subdir/helper.cxx");

      auto files = discoverSourceFiles(testDir.string());
      EXPECT_EQ(files.size(), 3);
  }

  TEST_F(FileDiscoveryTest, SupportsMultipleExtensions) {
      createFile(testDir / "a.cpp");
      createFile(testDir / "b.cxx");
      createFile(testDir / "c.cc");

      auto files = discoverSourceFiles(testDir.string());
      EXPECT_EQ(files.size(), 3);
  }

  TEST_F(FileDiscoveryTest, ExcludesGitDirectory) {
      createFile(testDir / "main.cpp");
      createFile(testDir / ".git/hooks.cpp");  // Should be excluded

      auto files = discoverSourceFiles(testDir.string());
      EXPECT_EQ(files.size(), 1);
      EXPECT_THAT(files[0], EndsWith("main.cpp"));
  }

  TEST_F(FileDiscoveryTest, ExcludesBuildDirectories) {
      createFile(testDir / "main.cpp");
      createFile(testDir / "build/generated.cpp");      // Excluded
      createFile(testDir / "build-debug/test.cpp");     // Excluded
      createFile(testDir / "cmake-build-release/a.cpp"); // Excluded

      auto files = discoverSourceFiles(testDir.string());
      EXPECT_EQ(files.size(), 1);
  }

  TEST_F(FileDiscoveryTest, HandlesEmptyDirectory) {
      auto files = discoverSourceFiles(testDir.string());
      EXPECT_TRUE(files.empty());
  }

  TEST_F(FileDiscoveryTest, HandlesNonExistentDirectory) {
      auto files = discoverSourceFiles("/nonexistent/path");
      EXPECT_TRUE(files.empty());
  }

  TEST_F(FileDiscoveryTest, ReturnsAbsolutePaths) {
      createFile(testDir / "main.cpp");

      auto files = discoverSourceFiles(testDir.string());
      ASSERT_EQ(files.size(), 1);

      fs::path filePath(files[0]);
      EXPECT_TRUE(filePath.is_absolute());
  }

  TEST_F(FileDiscoveryTest, IgnoresNonCppFiles) {
      createFile(testDir / "main.cpp");       // Included
      createFile(testDir / "header.h");       // Excluded
      createFile(testDir / "readme.txt");     // Excluded
      createFile(testDir / "build.sh");       // Excluded

      auto files = discoverSourceFiles(testDir.string());
      EXPECT_EQ(files.size(), 1);
  }
  ```

**3.2 Integration Tests** (Priority: HIGH)
- Test end-to-end auto-discovery with real cpptoc transpilation
- Verify `--source-dir` mode produces correct output
- Verify conflict detection between `--source-dir` and file arguments

- **Test Cases:**
  ```bash
  # Integration test script: tests/integration/test-auto-discovery.sh

  #!/bin/bash
  set -e

  CPPTOC="./build_working/cpptoc"
  TEST_DIR="tests/auto-discovery-test"
  OUTPUT_DIR="/tmp/cpptoc-auto-discovery-output"

  # Setup test directory
  mkdir -p "$TEST_DIR/src/module1"
  mkdir -p "$TEST_DIR/src/module2"
  mkdir -p "$TEST_DIR/build"  # Should be excluded

  # Create test files
  cat > "$TEST_DIR/src/module1/class1.cpp" << 'EOF'
  class TestClass {
  public:
      int getValue() { return 42; }
  };
  EOF

  cat > "$TEST_DIR/src/module2/class2.cpp" << 'EOF'
  class AnotherClass {
  public:
      void doSomething() {}
  };
  EOF

  # This should be excluded
  cat > "$TEST_DIR/build/generated.cpp" << 'EOF'
  // Generated file
  EOF

  # Test 1: Auto-discovery mode
  echo "Test 1: Auto-discovery with --source-dir"
  rm -rf "$OUTPUT_DIR"
  $CPPTOC --source-dir="$TEST_DIR/src" --output-dir="$OUTPUT_DIR" 2>&1 | tee output.log

  # Verify discovered 2 files (not 3, because build/ is excluded)
  if ! grep -q "Discovered 2 file(s)" output.log; then
      echo "FAIL: Expected 2 discovered files"
      exit 1
  fi

  # Verify transpiled files exist
  if [ ! -f "$OUTPUT_DIR/module1/class1.c" ]; then
      echo "FAIL: class1.c not generated"
      exit 1
  fi

  if [ ! -f "$OUTPUT_DIR/module2/class2.c" ]; then
      echo "FAIL: class2.c not generated"
      exit 1
  fi

  # Test 2: Conflict detection
  echo "Test 2: Conflict between --source-dir and file list"
  if $CPPTOC "$TEST_DIR/src/module1/class1.cpp" --source-dir="$TEST_DIR/src" --output-dir="$OUTPUT_DIR" 2>&1 | grep -q "Cannot specify both"; then
      echo "PASS: Conflict detected correctly"
  else
      echo "FAIL: Should error on conflicting arguments"
      exit 1
  fi

  # Test 3: Legacy mode (backward compatibility)
  echo "Test 3: Legacy mode without --source-dir"
  rm -rf "$OUTPUT_DIR"
  $CPPTOC "$TEST_DIR/src/module1/class1.cpp" --output-dir="$OUTPUT_DIR"

  if [ ! -f "$OUTPUT_DIR/class1.c" ]; then
      echo "FAIL: Legacy mode broken"
      exit 1
  fi

  echo "All integration tests passed!"
  ```

**3.3 Edge Case Tests** (Priority: MEDIUM)
- Symlinks (ensure NOT followed by default)
- Permission denied directories (skip gracefully)
- Mixed extensions in same project
- Deeply nested directory structures
- Unicode filenames (if applicable)

**3.4 Performance Test** (Priority: LOW)
- Test on large directory (1000+ files) to verify acceptable performance
- Ensure no memory leaks or excessive allocations

#### Deliverables
- ✅ Unit test suite for `discoverSourceFiles()`
- ✅ Integration test script for end-to-end auto-discovery
- ✅ Edge case test coverage
- ✅ All tests passing in CI/CD

#### Dependencies
- Phase 1: `discoverSourceFiles()` implementation
- Phase 2: CLI integration
- Google Test framework (already available)

#### Verification Steps
1. Run unit tests: `./build_working/test_file_discovery`
2. Run integration tests: `./tests/integration/test-auto-discovery.sh`
3. Verify test coverage: All critical paths tested
4. Verify CI/CD: Tests run automatically on push

</phase>

---

### Phase 4: Documentation

**Objective:** Update all user-facing documentation to explain the new auto-discovery feature and provide usage examples.

**Duration Estimate:** 1-2 hours

<phase id="4" name="Documentation">

#### Tasks

**4.1 Update README.md** (Priority: HIGH)
- **Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/README.md`

- **Additions:**
  ```markdown
  ### Auto-Discovery Mode

  cpptoc can automatically discover all C++ source files in a directory tree:

  ```bash
  cpptoc --source-dir=src/ --output-dir=build/
  ```

  **Supported Extensions:** `.cpp`, `.cxx`, `.cc`

  **Excluded Directories:** `.git`, `.svn`, `build*`, `cmake-build-*`,
  `node_modules`, and all hidden directories (`.something`)

  **Legacy Mode (Still Supported):**
  ```bash
  # Explicit file list
  cpptoc file1.cpp file2.cpp --output-dir=build/
  ```

  **Note:** You cannot combine `--source-dir` with individual file arguments.
  ```

**4.2 Update MULTI_FILE_TRANSPILATION.md** (Priority: HIGH)
- **Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/docs/MULTI_FILE_TRANSPILATION.md`

- **New Section:**
  ```markdown
  ## Automatic File Discovery

  ### Overview

  Instead of manually listing every `.cpp` file in your project, cpptoc can
  automatically discover them:

  ```bash
  cpptoc --source-dir=src/ --output-dir=build/
  ```

  ### How It Works

  1. cpptoc recursively scans the `--source-dir` directory
  2. Collects all files with extensions: `.cpp`, `.cxx`, `.cc`
  3. Excludes common build artifacts and version control directories
  4. Transpiles all discovered files while preserving directory structure

  ### Excluded Directories

  The following directories are automatically skipped:
  - `.git`, `.svn`, `.hg` (version control)
  - `build`, `build-*`, `cmake-build-*` (build artifacts)
  - `node_modules`, `vendor` (dependencies)
  - All hidden directories (starting with `.`)

  ### Comparison with Manual File Listing

  **Auto-Discovery (New):**
  ```bash
  cpptoc --source-dir=src/ --output-dir=build/
  ```

  **Manual Listing (Legacy):**
  ```bash
  cpptoc src/module1/class1.cpp src/module2/class2.cpp --output-dir=build/

  # Or using shell globbing
  cpptoc src/**/*.cpp --output-dir=build/
  ```

  ### Advantages

  - No need to update build scripts when adding new files
  - Automatically handles nested directory structures
  - Cleaner command-line invocations
  - Less error-prone than manual file lists

  ### Conflict Prevention

  You cannot use both `--source-dir` and individual file arguments:

  ```bash
  # ERROR: Cannot specify both
  cpptoc file.cpp --source-dir=src/ --output-dir=build/
  ```

  Choose ONE approach:
  - Auto-discovery: `--source-dir` only
  - Manual: File list only
  ```

**4.3 Update Help Text in main.cpp** (Priority: MEDIUM)
- **Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/main.cpp`

- **Update `SourceDir` option description:**
  ```cpp
  static cl::opt<std::string> SourceDir(
      "source-dir",
      cl::desc("Source directory for preserving directory structure in output.\n"
               "When specified without individual file arguments, cpptoc will\n"
               "automatically discover all .cpp, .cxx, and .cc files recursively.\n"
               "Excludes: .git, .svn, build*, cmake-build-*, node_modules, and\n"
               "hidden directories."),
      cl::cat(CppToCCategory));
  ```

**4.4 Add Examples Section** (Priority: MEDIUM)
- Create `docs/examples/auto-discovery.md` with real-world usage examples
- Include troubleshooting section for common issues

**4.5 Update CHANGELOG.md** (Priority: LOW)
- Document new feature in next release notes

#### Deliverables
- ✅ Updated README.md with auto-discovery section
- ✅ Updated MULTI_FILE_TRANSPILATION.md with detailed explanation
- ✅ Updated help text for `--source-dir` option
- ✅ Example documentation created
- ✅ CHANGELOG.md entry

#### Dependencies
- Phases 1-3: Feature must be implemented and tested

#### Verification Steps
1. Review all documentation for clarity and accuracy
2. Test all example commands in documentation
3. Verify help text displays correctly: `./cpptoc --help`
4. Ensure markdown formatting is correct

</phase>

</phases>

---

## Metadata

<metadata>

### Confidence Level
**HIGH (95%)**

**Rationale:**
- C++17 `std::filesystem` APIs are mature, well-documented, and cross-platform
- Research verified all technical approaches against official documentation
- Integration point in `main.cpp` is straightforward and well-understood
- Similar patterns exist in other CLI tools (validated approach)
- No novel algorithms or unproven techniques required

### Dependencies

**Language Features:**
- C++17 `<filesystem>` header (already in use)
- `std::unordered_set` for efficient lookups
- `std::vector` for file list storage

**Libraries:**
- LLVM diagnostic APIs (`llvm::errs()`, `llvm::outs()`)
- Existing CLI parsing infrastructure (`CommonOptionsParser`)

**External:**
- None (fully self-contained)

### Open Questions

**Q1: Should `--dry-run` flag be implemented?**
- **Description:** Show discovered files without transpiling
- **Decision Needed:** Include in Phase 1 or defer to future enhancement?
- **Recommendation:** DEFER - nice-to-have, not critical for MVP

**Q2: Should `--exclude-dir` option allow user-defined exclusions?**
- **Description:** Custom directory exclusions beyond hardcoded defaults
- **Example:** `--exclude-dir=third_party --exclude-dir=external`
- **Recommendation:** DEFER - add if users request it

**Q3: Error vs warning when no files found?**
- **Current Plan:** Return exit code 1 (non-fatal error) with warning message
- **Alternative:** Exit code 0 (success) with warning only
- **Recommendation:** Use exit code 1 (indicates potential user mistake)

**Q4: Verbosity control for discovery output?**
- **Description:** `--quiet` to suppress discovery messages, `--verbose` for per-file logging
- **Recommendation:** DEFER - implement if users find output too noisy

**Q5: Follow symlinks option?**
- **Description:** `--follow-symlinks` flag to enable symlink traversal
- **Recommendation:** DEFER - default (no follow) is safe; add only if requested

### Assumptions

**Technical Assumptions:**
1. `std::filesystem` is available in C++17 standard library (validated)
2. cpptoc already compiles with C++17 enabled (verified in research)
3. LLVM diagnostic APIs are consistent across supported LLVM versions
4. Absolute paths are safe to pass to `ClangTool` (current behavior)

**Workflow Assumptions:**
1. Users prefer auto-discovery over manual file listing
2. Standard exclusion list (`.git`, `build*`, etc.) covers 95% of use cases
3. Permission denied errors are acceptable to skip (with warning)
4. Empty directory is a user error (should warn and exit)

**Platform Assumptions:**
1. `std::filesystem` behavior is consistent on Linux, macOS, Windows
2. Symlink handling works identically on POSIX and Windows
3. Case-sensitive path handling is acceptable on case-insensitive filesystems

### Risk Assessment

**Implementation Risks:** LOW
- Well-defined scope with clear acceptance criteria
- No complex algorithms or data structures
- Straightforward integration into existing codebase

**Backward Compatibility Risks:** NONE
- Existing usage patterns unaffected
- Auto-discovery only activates with new argument pattern
- Explicit conflict detection prevents accidental misuse

**Performance Risks:** LOW
- File discovery is one-time upfront cost (not in hot path)
- Standard library optimizations handle large directory trees efficiently
- Research shows <1s for 10,000 files on typical hardware

**Maintenance Risks:** LOW
- Minimal new code (~100 lines)
- Standard library APIs are stable
- Clear separation of concerns (discovery vs. transpilation)

### Success Criteria

**Phase 1 Success:**
- [ ] `discoverSourceFiles()` returns correct file list for test directory
- [ ] Excluded directories (`.git`, `build*`) are skipped
- [ ] Permission denied handled gracefully
- [ ] Absolute paths returned

**Phase 2 Success:**
- [ ] Auto-discovery activates when `--source-dir` specified alone
- [ ] Legacy mode (file list) continues working
- [ ] Conflict detection prevents invalid argument combinations
- [ ] User feedback shows discovered file count

**Phase 3 Success:**
- [ ] All unit tests pass (8+ test cases)
- [ ] Integration tests pass (3+ end-to-end scenarios)
- [ ] Edge cases handled correctly
- [ ] CI/CD pipeline green

**Phase 4 Success:**
- [ ] README.md updated with clear examples
- [ ] MULTI_FILE_TRANSPILATION.md includes comprehensive guide
- [ ] Help text accurate and helpful
- [ ] All documentation tested and verified

**Overall Success:**
- [ ] Users can transpile entire projects with one command
- [ ] No backward compatibility breaks
- [ ] Zero crashes or segfaults on edge cases
- [ ] Documentation enables self-service user adoption

</metadata>

---

## Summary

This plan delivers automatic recursive file discovery for cpptoc in 4 focused phases:

1. **Phase 1 (2-3h):** Implement core `discoverSourceFiles()` function with robust error handling
2. **Phase 2 (1-2h):** Integrate with CLI argument parsing and validation
3. **Phase 3 (3-4h):** Comprehensive unit and integration testing
4. **Phase 4 (1-2h):** Update all user-facing documentation

**Total Estimated Time:** 8-11 hours
**Confidence Level:** HIGH (95%)
**Blockers:** None
**Next Step:** Execute Phase 1

The implementation leverages mature C++17 standard library APIs, maintains full backward compatibility, and provides a superior user experience compared to existing Clang tools.

</plan>

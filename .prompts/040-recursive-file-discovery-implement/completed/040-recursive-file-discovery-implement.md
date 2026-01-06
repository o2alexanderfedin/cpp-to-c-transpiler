# Implement: Recursive File Discovery for cpptoc

<objective>
Implement automatic `.cpp` file discovery for project-level transpilation when `--source-dir` is specified without individual file arguments.

**Purpose:** Enable users to transpile entire C++ projects with a single command: `cpptoc --source-dir=src/ --output-dir=build/` without manually listing every `.cpp` file.

**Output:** Working implementation with tests and documentation
</objective>

<context>
**Research findings:** @.prompts/038-recursive-file-discovery-research/recursive-file-discovery-research.md

**Implementation plan:** @.prompts/039-recursive-file-discovery-plan/recursive-file-discovery-plan.md

**Related implementation:**
- @.prompts/037-dir-transpilation-implement/SUMMARY.md - Directory structure preservation (already complete)

**Current codebase:**
- @src/main.cpp - CLI argument parsing and ClangTool invocation
- @include/FileOutputManager.h - Handles --source-dir for output paths
- @tests/MultiFileTranspilationTest.cpp - Integration tests for multi-file features

**Build system:**
- Uses CMake with GoogleTest
- C++17 required
- std::filesystem already in use
</context>

<requirements>
**Functional requirements:**
1. When `--source-dir` is specified without file arguments, automatically discover all `.cpp` files recursively
2. Support multiple extensions: `.cpp`, `.cxx`, `.cc`
3. Exclude common non-source directories: `.git`, `.svn`, `build*`, `cmake-build*`, `node_modules`
4. Follow symlinks by default (avoid infinite loops)
5. Handle permission denied errors gracefully
6. Provide user feedback: "Discovered N files in SOURCE_DIR"
7. Error if both `--source-dir` and file list provided
8. Maintain backward compatibility: explicit file lists continue working

**Quality requirements:**
1. All existing tests must pass (no regressions)
2. New unit tests for file discovery logic
3. Integration test for E2E auto-discovery workflow
4. Clear error messages for edge cases
5. Performance acceptable for large projects (10k+ files)

**Documentation requirements:**
1. Update README.md with auto-discovery examples
2. Update docs/MULTI_FILE_TRANSPILATION.md
3. Update --source-dir help text
4. Update example scripts (scripts/transpile-real-world.sh)
</requirements>

<implementation>
Follow the 4-phase plan from recursive-file-discovery-plan.md:

## Phase 1: Core File Discovery Function

**File:** `src/main.cpp`

Add file discovery function before `main()`:

```cpp
namespace {
// Directories to exclude from recursive search
const std::set<std::string> excludedDirs = {
    ".git", ".svn", ".hg",
    "build", "cmake-build-debug", "cmake-build-release",
    "node_modules", ".cache", ".vscode", ".idea"
};

// Extensions to include
const std::set<std::string> cppExtensions = {
    ".cpp", ".cxx", ".cc"
};

bool shouldSkipDirectory(const fs::path& dir) {
    std::string dirname = dir.filename().string();

    // Check exact match
    if (excludedDirs.find(dirname) != excludedDirs.end()) {
        return true;
    }

    // Check prefix match for build directories
    if (dirname.find("build") == 0 || dirname.find("cmake-build") == 0) {
        return true;
    }

    return false;
}

std::vector<std::string> discoverSourceFiles(const std::string& sourceDir) {
    std::vector<std::string> sourceFiles;

    try {
        auto options = fs::directory_options::skip_permission_denied
                     | fs::directory_options::follow_directory_symlink;

        for (const auto& entry : fs::recursive_directory_iterator(sourceDir, options)) {
            // Skip excluded directories
            if (entry.is_directory() && shouldSkipDirectory(entry.path())) {
                // Note: recursive_directory_iterator doesn't have disable_recursion_pending()
                // in C++17, so we filter entries after iteration
                continue;
            }

            if (entry.is_regular_file()) {
                auto ext = entry.path().extension().string();
                if (cppExtensions.find(ext) != cppExtensions.end()) {
                    sourceFiles.push_back(entry.path().string());
                }
            }
        }
    } catch (const fs::filesystem_error& e) {
        llvm::errs() << "Error discovering files in " << sourceDir << ": "
                     << e.what() << "\n";
        return {}; // Return empty vector on error
    }

    // Sort for deterministic ordering
    std::sort(sourceFiles.begin(), sourceFiles.end());

    return sourceFiles;
}

} // anonymous namespace
```

**Important:** Use C++17 `recursive_directory_iterator` which doesn't support skipping recursion into directories. We filter entries during iteration instead. This is acceptable for most use cases.

## Phase 2: CLI Integration

**File:** `src/main.cpp` (modify `main()` function)

Locate the section after argument parsing where `SourcePaths` is used. Replace with:

```cpp
// After cl::ParseCommandLineOptions()

std::vector<std::string> sourceFiles;
bool useAutoDiscovery = false;

// Determine mode: auto-discovery vs explicit file list
if (!SourceDir.empty() && SourcePaths.empty()) {
    // Auto-discovery mode
    useAutoDiscovery = true;
    llvm::outs() << "Auto-discovering .cpp files in " << SourceDir << "...\n";

    sourceFiles = discoverSourceFiles(SourceDir);

    if (sourceFiles.empty()) {
        llvm::errs() << "Error: No .cpp files found in " << SourceDir << "\n";
        llvm::errs() << "Searched for extensions: .cpp, .cxx, .cc\n";
        llvm::errs() << "Excluded directories: .git, build*, node_modules, etc.\n";
        return 1;
    }

    llvm::outs() << "Discovered " << sourceFiles.size() << " file(s)\n";

} else if (!SourceDir.empty() && !SourcePaths.empty()) {
    // Error: both specified
    llvm::errs() << "Error: Cannot specify both --source-dir and individual file arguments\n";
    llvm::errs() << "For auto-discovery: Use --source-dir without file arguments\n";
    llvm::errs() << "For explicit files: Omit --source-dir or use it only for output structure\n";
    return 1;

} else if (SourcePaths.empty()) {
    // Error: no files and no source-dir
    llvm::errs() << "Error: No input files specified\n";
    llvm::errs() << "Either provide file paths or use --source-dir for auto-discovery\n";
    return 1;

} else {
    // Legacy mode: explicit file list
    sourceFiles.assign(SourcePaths.begin(), SourcePaths.end());
}

// Continue with existing ClangTool logic using sourceFiles
// Replace SourcePaths with sourceFiles in ClangTool construction
```

**Update help text** for `--source-dir` option:

```cpp
static llvm::cl::opt<std::string> SourceDir(
    "source-dir",
    llvm::cl::desc(
        "Source root directory for:\n"
        "  1. Auto-discovery: Find all .cpp files recursively (when no files specified)\n"
        "  2. Structure preservation: Preserve directory structure in output\n"
        "Example: cpptoc --source-dir=src/ --output-dir=build/"
    ),
    llvm::cl::value_desc("directory"),
    llvm::cl::cat(ToolCategory));
```

## Phase 3: Testing

**Create:** `tests/FileDiscoveryTest.cpp`

```cpp
#include "gtest/gtest.h"
#include <filesystem>
#include <fstream>
#include <vector>
#include <string>
#include <set>

namespace fs = std::filesystem;

// Copy helper functions from main.cpp or extract to header
extern std::vector<std::string> discoverSourceFiles(const std::string& sourceDir);

class FileDiscoveryTest : public ::testing::Test {
protected:
    fs::path tempDir;

    void SetUp() override {
        tempDir = fs::temp_directory_path() / "cpptoc_discovery_test";
        fs::create_directories(tempDir);
    }

    void TearDown() override {
        if (fs::exists(tempDir)) {
            fs::remove_all(tempDir);
        }
    }

    void CreateTestFile(const fs::path& path, const std::string& content = "") {
        fs::create_directories(path.parent_path());
        std::ofstream file(path);
        file << content;
    }

    bool Contains(const std::vector<std::string>& vec, const std::string& substr) {
        return std::any_of(vec.begin(), vec.end(), [&](const std::string& s) {
            return s.find(substr) != std::string::npos;
        });
    }
};

TEST_F(FileDiscoveryTest, DiscoverBasicCppFiles) {
    CreateTestFile(tempDir / "file1.cpp");
    CreateTestFile(tempDir / "file2.cpp");
    CreateTestFile(tempDir / "file.h"); // Should be excluded

    auto files = discoverSourceFiles(tempDir.string());

    ASSERT_EQ(files.size(), 2);
    EXPECT_TRUE(Contains(files, "file1.cpp"));
    EXPECT_TRUE(Contains(files, "file2.cpp"));
}

TEST_F(FileDiscoveryTest, DiscoverMultipleExtensions) {
    CreateTestFile(tempDir / "file1.cpp");
    CreateTestFile(tempDir / "file2.cxx");
    CreateTestFile(tempDir / "file3.cc");
    CreateTestFile(tempDir / "file4.c"); // Should be excluded

    auto files = discoverSourceFiles(tempDir.string());

    ASSERT_EQ(files.size(), 3);
    EXPECT_TRUE(Contains(files, "file1.cpp"));
    EXPECT_TRUE(Contains(files, "file2.cxx"));
    EXPECT_TRUE(Contains(files, "file3.cc"));
}

TEST_F(FileDiscoveryTest, ExcludesGitDirectory) {
    CreateTestFile(tempDir / ".git/hooks/pre-commit.cpp");
    CreateTestFile(tempDir / "src/main.cpp");

    auto files = discoverSourceFiles(tempDir.string());

    ASSERT_EQ(files.size(), 1);
    EXPECT_TRUE(Contains(files, "src/main.cpp"));
    EXPECT_FALSE(Contains(files, ".git"));
}

TEST_F(FileDiscoveryTest, ExcludesBuildDirectories) {
    CreateTestFile(tempDir / "build/temp.cpp");
    CreateTestFile(tempDir / "cmake-build-debug/temp.cpp");
    CreateTestFile(tempDir / "src/main.cpp");

    auto files = discoverSourceFiles(tempDir.string());

    ASSERT_EQ(files.size(), 1);
    EXPECT_TRUE(Contains(files, "src/main.cpp"));
}

TEST_F(FileDiscoveryTest, NestedDirectories) {
    CreateTestFile(tempDir / "a/b/c/d/file.cpp");
    CreateTestFile(tempDir / "x/y/file.cpp");

    auto files = discoverSourceFiles(tempDir.string());

    ASSERT_EQ(files.size(), 2);
}

TEST_F(FileDiscoveryTest, EmptyDirectory) {
    auto files = discoverSourceFiles(tempDir.string());
    EXPECT_TRUE(files.empty());
}

TEST_F(FileDiscoveryTest, NonExistentDirectory) {
    auto files = discoverSourceFiles("/nonexistent/path/12345");
    EXPECT_TRUE(files.empty()); // Should return empty, not crash
}

// Add to CMakeLists.txt:
// add_executable(FileDiscoveryTest tests/FileDiscoveryTest.cpp src/main.cpp)
// target_link_libraries(FileDiscoveryTest gtest gtest_main)
// add_test(NAME FileDiscoveryTest COMMAND FileDiscoveryTest)
```

**Extend:** `tests/MultiFileTranspilationTest.cpp`

Add integration test:

```cpp
TEST_F(MultiFileTranspilationTest, AutoDiscovery_SourceDirOnly) {
    // Create test structure with multiple files in subdirectories
    CreateTestFile(tempDir / "src/module1/file1.cpp", simpleCppContent);
    CreateTestFile(tempDir / "src/module2/file2.cpp", simpleCppContent);
    CreateTestFile(tempDir / "src/.git/ignored.cpp", simpleCppContent);

    // Run with --source-dir only (no file arguments)
    int result = RunTranspiler(
        {}, // Empty file list
        {
            "--source-dir=" + (tempDir / "src").string(),
            "--output-dir=" + (tempDir / "out").string()
        }
    );

    ASSERT_EQ(result, 0) << "Auto-discovery transpilation failed";

    // Verify both files were transpiled with structure preserved
    ASSERT_TRUE(fs::exists(tempDir / "out/module1/file1.c"));
    ASSERT_TRUE(fs::exists(tempDir / "out/module1/file1.h"));
    ASSERT_TRUE(fs::exists(tempDir / "out/module2/file2.c"));
    ASSERT_TRUE(fs::exists(tempDir / "out/module2/file2.h"));

    // Verify excluded directory was skipped
    ASSERT_FALSE(fs::exists(tempDir / "out/.git/ignored.c"));
}

TEST_F(MultiFileTranspilationTest, AutoDiscovery_ConflictError) {
    CreateTestFile(tempDir / "file.cpp", simpleCppContent);

    // Both --source-dir and file arguments should error
    int result = RunTranspiler(
        {tempDir / "file.cpp"}, // File argument
        {"--source-dir=" + tempDir.string()} // And source-dir
    );

    ASSERT_NE(result, 0) << "Should error when both modes specified";
}
```

## Phase 4: Documentation

**Update:** `README.md`

Add section after "Multi-File Transpilation":

```markdown
## Automatic File Discovery

Transpile entire C++ projects automatically by specifying the source directory:

```bash
cpptoc --source-dir=./src --output-dir=./build
```

This command will:
- ✅ Recursively discover all `.cpp`, `.cxx`, and `.cc` files in `src/`
- ✅ Preserve the directory structure in `build/`
- ✅ Skip common non-source directories (`.git`, `build*`, `node_modules`)
- ✅ Follow symlinks

### Before: Manual File Lists

```bash
# Tedious and error-prone
cpptoc src/module1/file1.cpp src/module2/file2.cpp src/module3/file3.cpp \
       --output-dir=build/
```

### After: Automatic Discovery

```bash
# Simple and complete
cpptoc --source-dir=src/ --output-dir=build/
```

### Options

**Preview discovered files without transpiling:**
```bash
cpptoc --source-dir=src/ --dry-run
```

**Use with header separation:**
```bash
cpptoc --source-dir=src/ --output-dir=build/ --header-separation
```

### Excluded Directories

Auto-discovery skips these common directories:
- `.git`, `.svn`, `.hg` (version control)
- `build*`, `cmake-build*` (build outputs)
- `node_modules`, `.cache` (dependencies/caches)
- `.vscode`, `.idea` (IDE directories)

### Supported Extensions

- `.cpp` (standard)
- `.cxx` (alternative)
- `.cc` (alternative)
```

**Update:** `docs/MULTI_FILE_TRANSPILATION.md`

Add section at the beginning:

```markdown
## Automatic File Discovery (Recommended)

**New in v1.x:** cpptoc can automatically discover all C++ source files in your project.

### Basic Usage

```bash
cpptoc --source-dir=./src --output-dir=./build
```

This single command:
1. Finds all `.cpp`, `.cxx`, and `.cc` files in `src/` recursively
2. Transpiles each file to C
3. Preserves the directory structure in `build/`

### Real-World Example

For a project structure:
```
my-project/
├── src/
│   ├── core/
│   │   ├── engine.cpp
│   │   └── utils.cpp
│   ├── graphics/
│   │   └── renderer.cpp
│   └── main.cpp
└── build/
```

Run:
```bash
cpptoc --source-dir=src/ --output-dir=build/
```

Output:
```
build/
├── core/
│   ├── engine.c
│   ├── engine.h
│   ├── utils.c
│   └── utils.h
├── graphics/
│   ├── renderer.c
│   └── renderer.h
├── main.c
└── main.h
```

### When to Use Auto-Discovery

✅ **Use auto-discovery when:**
- Transpiling an entire project or module
- Directory structure should be preserved
- All `.cpp` files need transpilation

❌ **Use explicit file list when:**
- Transpiling specific files only
- Testing single file transpilation
- Custom file selection logic needed
```

**Update:** `scripts/transpile-real-world.sh`

Simplify to use auto-discovery:

```bash
#!/bin/bash
# Transpile all real-world test projects

set -e

echo "Transpiling real-world C++ projects..."

cpptoc \
  --source-dir=tests/real-world \
  --output-dir=tests/real-world/transpiled \
  -- \
  -Itests/real-world/json-parser/include \
  -Itests/real-world/logger/include \
  -Itests/real-world/resource-manager/include \
  -Itests/real-world/string-formatter/include \
  -Itests/real-world/test-framework/include \
  -std=c++17

echo "✅ Transpilation complete!"
echo "Output: tests/real-world/transpiled/"
```

</implementation>

<verification>
Before declaring complete, verify:

**Build and Test:**
1. Clean build: `rm -rf build_working && mkdir build_working && cd build_working && cmake .. && make`
2. Run all tests: `ctest` or `make test`
3. Verify no test failures
4. Specifically run: `./FileDiscoveryTest` and `./MultiFileTranspilationTest`

**Manual Testing:**
1. Test auto-discovery:
   ```bash
   ./build_working/cpptoc --source-dir=tests/real-world --output-dir=/tmp/test-out
   ```
   - Verify 11 files discovered
   - Verify output structure preserved
   - Verify .git directories skipped

2. Test error cases:
   ```bash
   # Should error: both modes
   ./build_working/cpptoc --source-dir=tests/real-world tests/real-world/json-parser/src/JsonParser.cpp

   # Should error: no files found
   ./build_working/cpptoc --source-dir=/tmp/empty-dir --output-dir=/tmp/out
   ```

3. Test backward compatibility:
   ```bash
   # Should work as before
   ./build_working/cpptoc tests/real-world/json-parser/src/JsonParser.cpp --output-dir=/tmp/out
   ```

**Documentation:**
4. Verify README examples are accurate and runnable
5. Verify help text: `./build_working/cpptoc --help`
6. Run updated script: `./scripts/transpile-real-world.sh`

**Edge Cases:**
7. Create test with symlink: verify followed
8. Create test with permission denied: verify graceful handling
9. Test with deeply nested directories (10+ levels)
10. Test with large directory (if available, 1000+ files)
</verification>

<success_criteria>
**Implementation complete when:**
- ✅ `cpptoc --source-dir=DIR --output-dir=OUT` discovers and transpiles all .cpp files
- ✅ Directory structure is preserved in output
- ✅ Excluded directories (.git, build) are skipped
- ✅ Clear error when both --source-dir and files provided
- ✅ All existing tests pass (backward compatibility)
- ✅ New unit tests pass (FileDiscoveryTest)
- ✅ New integration test passes (AutoDiscovery_SourceDirOnly)
- ✅ Documentation is updated and accurate
- ✅ Example scripts use new auto-discovery approach
- ✅ Help text is clear and complete
- ✅ No compiler warnings
- ✅ Build succeeds on clean build
- ✅ SUMMARY.md created with implementation details
</success_criteria>

<summary_requirements>
Create `.prompts/040-recursive-file-discovery-implement/SUMMARY.md`

Template:
```markdown
# Recursive File Discovery Implementation Summary

**Auto-discovery complete: `cpptoc --source-dir=DIR --output-dir=OUT` now finds all .cpp files automatically**

## Files Modified
- `src/main.cpp` - Added discoverSourceFiles() function, CLI integration logic
- `tests/FileDiscoveryTest.cpp` - New unit tests (8 tests for discovery logic)
- `tests/MultiFileTranspilationTest.cpp` - New integration tests (2 tests for E2E workflow)
- `README.md` - Added "Automatic File Discovery" section with examples
- `docs/MULTI_FILE_TRANSPILATION.md` - Added auto-discovery guide and real-world example
- `scripts/transpile-real-world.sh` - Simplified to use auto-discovery

## Test Results
- FileDiscoveryTest: 8/8 passing
- MultiFileTranspilationTest: 19/19 passing (17 existing + 2 new)
- All existing tests: passing (backward compatibility verified)

## Usage Examples

### Auto-Discovery (New)
```bash
cpptoc --source-dir=tests/real-world --output-dir=out/
# Discovers 11 files automatically
```

### Explicit Files (Backward Compatible)
```bash
cpptoc file1.cpp file2.cpp --output-dir=out/
# Still works as before
```

## Decisions Needed
None - implementation complete and tested

## Blockers
None

## Next Step
Use in production: Transpile real-world C++ projects with simple commands

---
*Test Pass Rate: 27/27 (100%)*
*Backward Compatibility: 100%*
*Implementation Time: ~6 hours*
```
</summary_requirements>

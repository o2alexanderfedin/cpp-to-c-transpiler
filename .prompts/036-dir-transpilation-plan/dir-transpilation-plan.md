# Directory-Based Transpilation Implementation Plan

## Metadata
- **Date**: 2025-12-23
- **Author**: Claude Code
- **Status**: Ready for Implementation
- **Based on**: `.prompts/035-dir-transpilation-research/dir-transpilation-research.md`
- **Goal**: Implement directory structure preservation for cpptoc transpiler

## Summary

This plan implements directory structure preservation for the cpptoc transpiler using a phased approach that maintains backward compatibility while adding the ability to mirror source directory structures in output. The implementation follows TypeScript's `rootDir`/`outDir` model with an opt-in `--preserve-structure` flag and required `--source-root` parameter. The plan is divided into 4 sequential phases: (1) core path calculation logic, (2) CLI integration and backward compatibility, (3) comprehensive testing including edge cases, and (4) documentation and examples. Each phase delivers incremental value and can be tested independently before proceeding to the next.

**Key Design Decision**: Opt-in structure preservation (default: off) to maintain 100% backward compatibility with existing usage and tests.

---

## Phase 1: Core Path Calculation Logic

**Goal**: Implement the foundational relative path calculation and directory creation without changing CLI interface.

**Duration**: 2-3 hours

### Tasks

#### Priority 1: Add FileOutputManager Members

**File**: `include/FileOutputManager.h`

```cpp
class FileOutputManager {
public:
    // Existing methods...

    // NEW: Structure preservation settings
    void setSourceRoot(const std::string& root);
    void setPreserveStructure(bool preserve);
    bool isPreservingStructure() const;

private:
    // Existing members...

    // NEW: Structure preservation state
    std::string sourceRootDir;
    bool preserveStructure = false;

    // NEW: Path calculation helper
    std::string calculateOutputPath(const std::string& extension) const;
};
```

**Why First**: Establishes the API contract before implementation.

**Acceptance Criteria**:
- [ ] Header compiles without errors
- [ ] New methods declared with clear semantics
- [ ] Private members properly encapsulated

---

#### Priority 2: Implement Relative Path Calculation

**File**: `src/FileOutputManager.cpp`

**Implementation**:

```cpp
#include <filesystem>

namespace fs = std::filesystem;

void FileOutputManager::setSourceRoot(const std::string& root) {
    sourceRootDir = root;
}

void FileOutputManager::setPreserveStructure(bool preserve) {
    preserveStructure = preserve;
}

bool FileOutputManager::isPreservingStructure() const {
    return preserveStructure;
}

std::string FileOutputManager::calculateOutputPath(const std::string& extension) const {
    // Legacy mode: strip path (current behavior)
    if (!preserveStructure || sourceRootDir.empty()) {
        return getFullPath(getBaseName() + extension);
    }

    // Structure preservation mode
    try {
        // Resolve symlinks and normalize paths
        fs::path inputPath = fs::weakly_canonical(inputFilename);
        fs::path rootPath = fs::weakly_canonical(sourceRootDir);

        // Calculate relative path
        fs::path relPath = inputPath.lexically_relative(rootPath);

        // Handle files outside source root
        if (relPath.string().find("..") == 0) {
            std::cerr << "Warning: File " << inputFilename
                      << " is outside source root " << sourceRootDir
                      << ". Using basename only." << std::endl;
            return getFullPath(getBaseName() + extension);
        }

        // Replace extension
        relPath.replace_extension(extension);

        return getFullPath(relPath.string());

    } catch (const fs::filesystem_error& e) {
        std::cerr << "Error calculating output path for " << inputFilename
                  << ": " << e.what() << std::endl;
        // Fallback to legacy behavior
        return getFullPath(getBaseName() + extension);
    }
}
```

**Why Second**: Core algorithm must be solid before wiring it up.

**Edge Cases Handled**:
- Files outside source root → fallback to basename with warning
- Symlinks → resolved via `weakly_canonical()`
- Filesystem errors → graceful fallback to legacy mode
- Empty source root → legacy behavior

**Acceptance Criteria**:
- [ ] Compiles without errors
- [ ] Legacy mode works (preserveStructure=false)
- [ ] Relative path calculation correct for files under source root
- [ ] Files outside source root fallback gracefully
- [ ] Cross-platform (uses `std::filesystem`)

---

#### Priority 3: Update Output Methods

**File**: `src/FileOutputManager.cpp`

Replace direct `getBaseName()` calls with `calculateOutputPath()`:

```cpp
std::string FileOutputManager::getHeaderFilename() const {
    // If custom header name specified, use it
    if (!outputHeader.empty()) {
        return getFullPath(outputHeader);
    }

    // Use new path calculation logic
    return calculateOutputPath(".h");
}

std::string FileOutputManager::getSourceFilename() const {
    // If custom source name specified, use it
    if (!outputSource.empty()) {
        return getFullPath(outputSource);
    }

    // Use new path calculation logic
    return calculateOutputPath(".c");
}
```

**Why Third**: Wire up the new logic to existing API.

**Acceptance Criteria**:
- [ ] Custom filenames still work (backward compat)
- [ ] New path calculation used when appropriate
- [ ] No changes to external API surface

---

#### Priority 4: Add Directory Creation

**File**: `src/FileOutputManager.cpp`

Update `writeFile()` to create parent directories:

```cpp
bool FileOutputManager::writeFile(const std::string& filename,
                                   const std::string& content) {
    // Create parent directories if needed
    fs::path filePath(filename);
    fs::path parentDir = filePath.parent_path();

    if (!parentDir.empty() && !fs::exists(parentDir)) {
        std::error_code ec;
        fs::create_directories(parentDir, ec);
        if (ec) {
            std::cerr << "Error: Could not create directory: " << parentDir
                      << " - " << ec.message() << std::endl;
            return false;
        }
    }

    // Original write logic
    std::ofstream outFile(filename);
    if (!outFile.is_open()) {
        std::cerr << "Error: Could not open file for writing: " << filename << std::endl;
        return false;
    }

    outFile << content;
    outFile.close();

    if (outFile.fail()) {
        std::cerr << "Error: Failed to write to file: " << filename << std::endl;
        return false;
    }

    return true;
}
```

**Why Fourth**: Needed for nested output paths to work.

**Acceptance Criteria**:
- [ ] Creates parent directories automatically
- [ ] Handles permission errors gracefully
- [ ] Works on both Unix and Windows
- [ ] Existing flat-file tests still pass

---

### Phase 1 Deliverables

- [ ] FileOutputManager header updated with new methods
- [ ] Path calculation logic implemented and tested
- [ ] Output methods use new calculation
- [ ] Directory creation working
- [ ] All existing tests still pass (backward compatibility verified)

### Phase 1 Dependencies

- C++17 `<filesystem>` (already in use per research)
- No new external dependencies

### Phase 1 Risks

**Low Risk**:
- Logic is isolated in FileOutputManager
- Legacy mode preserves existing behavior
- Can be tested independently

---

## Phase 2: CLI Integration and Wiring

**Goal**: Add CLI flags and wire up structure preservation through the transpiler pipeline.

**Duration**: 1-2 hours

### Tasks

#### Priority 1: Add CLI Flags

**File**: `src/main.cpp`

Add new command-line options:

```cpp
// After existing OutputDir flag
static llvm::cl::opt<bool> PreserveStructure(
    "preserve-structure",
    llvm::cl::desc("Preserve source directory structure in output (default: off)"),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(false));

static llvm::cl::opt<std::string> SourceRoot(
    "source-root",
    llvm::cl::desc("Source root directory for path calculation (required with --preserve-structure)"),
    llvm::cl::value_desc("directory"),
    llvm::cl::cat(ToolCategory));
```

**Validation Logic**:

```cpp
// In main() after option parsing
if (PreserveStructure && SourceRoot.empty()) {
    llvm::errs() << "Error: --source-root is required when --preserve-structure is enabled\n";
    return 1;
}

if (!SourceRoot.empty() && !PreserveStructure) {
    llvm::errs() << "Warning: --source-root specified but --preserve-structure is not enabled. "
                 << "Source root will be ignored.\n";
}
```

**Acceptance Criteria**:
- [ ] Flags compile and parse correctly
- [ ] Validation prevents invalid combinations
- [ ] Help text is clear and accurate

---

#### Priority 2: Wire Up in CppToCConsumer

**File**: `src/CppToCConsumer.cpp`

Update `HandleTranslationUnit()`:

```cpp
void CppToCConsumer::HandleTranslationUnit(ASTContext &Ctx) {
    // Existing setup...
    FileOutputManager outputMgr;
    outputMgr.setInputFilename(InputFilename);

    std::string outputDir = getOutputDir();
    if (!outputDir.empty()) {
        outputMgr.setOutputDir(outputDir);
    }

    // NEW: Structure preservation setup
    if (shouldPreserveStructure()) {
        outputMgr.setPreserveStructure(true);
        outputMgr.setSourceRoot(getSourceRoot());
    }

    // ... rest of existing code
}
```

**Add Helper Methods**:

```cpp
// In CppToCConsumer.h
private:
    bool shouldPreserveStructure() const;
    std::string getSourceRoot() const;

// In CppToCConsumer.cpp
bool CppToCConsumer::shouldPreserveStructure() const {
    // Access global CLI flag (or pass via constructor if refactoring)
    extern llvm::cl::opt<bool> PreserveStructure;
    return PreserveStructure;
}

std::string CppToCConsumer::getSourceRoot() const {
    extern llvm::cl::opt<std::string> SourceRoot;
    return SourceRoot;
}
```

**Acceptance Criteria**:
- [ ] Settings propagate from CLI to FileOutputManager
- [ ] Legacy mode (no flags) works unchanged
- [ ] New mode (with flags) activates structure preservation

---

#### Priority 3: TranspilerAPI Integration (Optional)

**File**: `include/TranspilerAPI.h`

Add source root to `TranspileOptions`:

```cpp
struct TranspileOptions {
    // Existing fields...

    // NEW: Directory structure preservation
    const char* sourceRoot = nullptr;      // Source root for path calculation
    bool preserveStructure = false;        // Enable structure preservation
};
```

**File**: `src/TranspilerAPI.cpp`

Wire up in `transpileFile()`:

```cpp
// Inside transpileFile() after setting outputDir
if (options && options->preserveStructure && options->sourceRoot) {
    outputMgr.setPreserveStructure(true);
    outputMgr.setSourceRoot(options->sourceRoot);
}
```

**Why Optional**: Only needed if library users want structure preservation. Can defer to Phase 4 if time-constrained.

**Acceptance Criteria**:
- [ ] API compiles with new fields
- [ ] Backward compatible (nullptr defaults work)
- [ ] Library users can enable structure preservation

---

### Phase 2 Deliverables

- [ ] CLI flags added and validated
- [ ] Settings flow through transpiler pipeline
- [ ] TranspilerAPI updated (if included)
- [ ] End-to-end manual test: `cpptoc --preserve-structure --source-root src/ --output-dir build/ src/test.cpp`

### Phase 2 Dependencies

- Phase 1 complete (path calculation working)

### Phase 2 Risks

**Low Risk**:
- CLI flags are straightforward
- Wiring is simple state passing
- Backward compatibility maintained by default

---

## Phase 3: Comprehensive Testing

**Goal**: Validate all functionality including edge cases and backward compatibility.

**Duration**: 2-3 hours

### Tasks

#### Priority 1: Unit Tests for Path Calculation

**New File**: `tests/PathCalculationTest.cpp`

Test the core algorithm in isolation:

```cpp
#include <gtest/gtest.h>
#include "FileOutputManager.h"

TEST(PathCalculationTest, LegacyModeStripsPath) {
    FileOutputManager mgr;
    mgr.setInputFilename("/project/src/math/Vector.cpp");
    mgr.setOutputDir("/project/build");
    mgr.setPreserveStructure(false);  // Legacy mode

    EXPECT_EQ(mgr.getHeaderFilename(), "/project/build/Vector.h");
    EXPECT_EQ(mgr.getSourceFilename(), "/project/build/Vector.c");
}

TEST(PathCalculationTest, PreservesStructureUnderSourceRoot) {
    FileOutputManager mgr;
    mgr.setInputFilename("/project/src/math/algebra/Vector.cpp");
    mgr.setOutputDir("/project/build");
    mgr.setSourceRoot("/project/src");
    mgr.setPreserveStructure(true);

    EXPECT_EQ(mgr.getHeaderFilename(), "/project/build/math/algebra/Vector.h");
    EXPECT_EQ(mgr.getSourceFilename(), "/project/build/math/algebra/Vector.c");
}

TEST(PathCalculationTest, FallbackForFilesOutsideRoot) {
    FileOutputManager mgr;
    mgr.setInputFilename("/vendor/external.cpp");
    mgr.setOutputDir("/project/build");
    mgr.setSourceRoot("/project/src");
    mgr.setPreserveStructure(true);

    // Should fall back to basename
    EXPECT_EQ(mgr.getHeaderFilename(), "/project/build/external.h");
}

TEST(PathCalculationTest, RelativePathsHandled) {
    FileOutputManager mgr;
    mgr.setInputFilename("src/math/Vector.cpp");
    mgr.setOutputDir("build");
    mgr.setSourceRoot("src");
    mgr.setPreserveStructure(true);

    EXPECT_TRUE(mgr.getHeaderFilename().find("math/Vector.h") != std::string::npos);
}

TEST(PathCalculationTest, SingleFileInSourceRoot) {
    FileOutputManager mgr;
    mgr.setInputFilename("/project/src/Point.cpp");
    mgr.setOutputDir("/project/build");
    mgr.setSourceRoot("/project/src");
    mgr.setPreserveStructure(true);

    EXPECT_EQ(mgr.getHeaderFilename(), "/project/build/Point.h");
}
```

**Coverage**:
- Legacy mode (no structure preservation)
- Structure preservation with nested paths
- Files outside source root
- Relative vs absolute paths
- Single file at source root level

**Acceptance Criteria**:
- [ ] All unit tests pass
- [ ] Edge cases covered
- [ ] Both modes tested

---

#### Priority 2: Integration Tests

**File**: `tests/MultiFileTranspilationTest.cpp`

Add new test cases (append to existing file):

```cpp
TEST_F(MultiFileTranspilationTest, PreservesDirectoryStructure) {
    // Create source files in subdirectories
    fs::path srcDir = tempDir / "src";
    fs::path mathDir = srcDir / "math";
    fs::path utilsDir = srcDir / "utils";
    fs::create_directories(mathDir);
    fs::create_directories(utilsDir);

    // Write test files
    writeFile(mathDir / "Vector.cpp",
        "class Vector { public: int x, y; };");
    writeFile(utilsDir / "helpers.cpp",
        "void help() {}");

    // Transpile with structure preservation
    std::vector<std::string> args = {
        "cpptoc",
        "--preserve-structure",
        "--source-root", srcDir.string(),
        "--output-dir", (tempDir / "build").string(),
        (mathDir / "Vector.cpp").string(),
        (utilsDir / "helpers.cpp").string()
    };

    int result = runTranspiler(args);
    ASSERT_EQ(result, 0);

    // Verify structure preserved
    EXPECT_TRUE(fs::exists(tempDir / "build/math/Vector.h"));
    EXPECT_TRUE(fs::exists(tempDir / "build/math/Vector.c"));
    EXPECT_TRUE(fs::exists(tempDir / "build/utils/helpers.h"));
    EXPECT_TRUE(fs::exists(tempDir / "build/utils/helpers.c"));
}

TEST_F(MultiFileTranspilationTest, BackwardCompatibilityWithoutFlags) {
    // Existing test should still pass - verify no regression
    fs::path srcDir = tempDir / "src";
    fs::create_directories(srcDir);

    writeFile(srcDir / "Point.cpp", "class Point { int x; };");

    // Run WITHOUT new flags (legacy mode)
    std::vector<std::string> args = {
        "cpptoc",
        "--output-dir", (tempDir / "build").string(),
        (srcDir / "Point.cpp").string()
    };

    int result = runTranspiler(args);
    ASSERT_EQ(result, 0);

    // Output should be flat (legacy behavior)
    EXPECT_TRUE(fs::exists(tempDir / "build/Point.h"));
    EXPECT_TRUE(fs::exists(tempDir / "build/Point.c"));
    EXPECT_FALSE(fs::exists(tempDir / "build/src/Point.h"));  // NOT nested
}

TEST_F(MultiFileTranspilationTest, ErrorWhenSourceRootMissing) {
    fs::path srcDir = tempDir / "src";
    fs::create_directories(srcDir);
    writeFile(srcDir / "test.cpp", "void f() {}");

    // Use --preserve-structure without --source-root
    std::vector<std::string> args = {
        "cpptoc",
        "--preserve-structure",
        "--output-dir", (tempDir / "build").string(),
        (srcDir / "test.cpp").string()
    };

    int result = runTranspiler(args);
    EXPECT_NE(result, 0);  // Should fail with error
}
```

**Coverage**:
- Directory structure preservation end-to-end
- Backward compatibility (existing behavior unchanged)
- Error handling for invalid flag combinations

**Acceptance Criteria**:
- [ ] New integration tests pass
- [ ] All existing tests still pass (regression check)
- [ ] Error cases validated

---

#### Priority 3: Real-World Project Tests

**Test**: Transpile actual test projects with directory structures

**Script**: Create `test-real-world-structure.sh`

```bash
#!/bin/bash
set -e

PROJECT_ROOT="/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c"
CPPTOC="$PROJECT_ROOT/build_working/cpptoc"

echo "Testing json-parser with structure preservation..."
mkdir -p /tmp/transpile-test/json-parser-output

$CPPTOC \
    --preserve-structure \
    --source-root "$PROJECT_ROOT/tests/real-world/json-parser" \
    --output-dir /tmp/transpile-test/json-parser-output \
    "$PROJECT_ROOT/tests/real-world/json-parser/src/JsonParser.cpp" \
    "$PROJECT_ROOT/tests/real-world/json-parser/src/JsonValue.cpp" \
    "$PROJECT_ROOT/tests/real-world/json-parser/tests/test_json_parser.cpp"

# Verify structure
if [ -f "/tmp/transpile-test/json-parser-output/src/JsonParser.h" ] && \
   [ -f "/tmp/transpile-test/json-parser-output/tests/test_json_parser.h" ]; then
    echo "✓ json-parser structure preserved correctly"
else
    echo "✗ json-parser structure NOT preserved"
    exit 1
fi

echo "All real-world tests passed!"
```

**Acceptance Criteria**:
- [ ] Real projects transpile successfully
- [ ] Directory structure mirrored correctly
- [ ] Generated C code compiles

---

#### Priority 4: Cross-Platform Tests

**Platforms to Test**:
- Linux (primary development platform)
- macOS (if available)
- Windows paths (via test cases)

**Windows Path Test**:

```cpp
TEST(PathCalculationTest, WindowsPathsHandled) {
    FileOutputManager mgr;

    // Simulate Windows paths (will be normalized by filesystem)
    mgr.setInputFilename("C:\\project\\src\\math\\Vector.cpp");
    mgr.setOutputDir("C:\\project\\build");
    mgr.setSourceRoot("C:\\project\\src");
    mgr.setPreserveStructure(true);

    std::string header = mgr.getHeaderFilename();

    // Should contain math/Vector.h (normalized separators)
    EXPECT_TRUE(header.find("math") != std::string::npos);
    EXPECT_TRUE(header.find("Vector.h") != std::string::npos);
}
```

**Acceptance Criteria**:
- [ ] Tests pass on Linux
- [ ] Tests pass on macOS (if tested)
- [ ] Windows path handling verified via tests

---

### Phase 3 Deliverables

- [ ] Unit tests for path calculation (10+ test cases)
- [ ] Integration tests for end-to-end flow (5+ test cases)
- [ ] Real-world project test script
- [ ] Cross-platform validation
- [ ] All existing tests pass (backward compatibility confirmed)
- [ ] Code coverage report shows >90% for new code

### Phase 3 Dependencies

- Phase 1 and 2 complete

### Phase 3 Risks

**Medium Risk**:
- Cross-platform testing may reveal platform-specific issues
- Real-world projects might expose edge cases

**Mitigation**:
- Use `std::filesystem` which is cross-platform
- Test early and often on different platforms

---

## Phase 4: Documentation and Examples

**Goal**: Document the new feature with clear examples and usage guidelines.

**Duration**: 1 hour

### Tasks

#### Priority 1: Update README

**File**: `README.md`

Add section after existing output-dir documentation:

```markdown
### Directory Structure Preservation

By default, cpptoc places all output files (.h and .c) in a flat directory structure.
To preserve your source directory structure in the output:

#### Basic Usage

```bash
cpptoc --preserve-structure --source-root src/ --output-dir build/ src/**/*.cpp
```

This will mirror your source structure:

```
Source:                    Output:
src/                       build/
  math/                      math/
    Vector.cpp                 Vector.h
                               Vector.c
  utils/                     utils/
    helpers.cpp                helpers.h
                               helpers.c
```

#### Options

- `--preserve-structure`: Enable directory structure preservation (default: off)
- `--source-root <dir>`: Source root directory for relative path calculation (required with --preserve-structure)
- `--output-dir <dir>`: Output directory (existing option)

#### Example: Transpiling a Project

```bash
# Preserve src/ and tests/ structure
cpptoc --preserve-structure \
       --source-root . \
       --output-dir build/ \
       src/**/*.cpp tests/**/*.cpp

# Result:
#   build/src/module/File.h
#   build/src/module/File.c
#   build/tests/test_module.h
#   build/tests/test_module.c
```

#### Backward Compatibility

Without `--preserve-structure`, the transpiler uses the original behavior:

```bash
# All output files in build/ (flat structure)
cpptoc --output-dir build/ src/math/Vector.cpp src/utils/helpers.cpp

# Result:
#   build/Vector.h
#   build/Vector.c
#   build/helpers.h
#   build/helpers.c
```
```

**Acceptance Criteria**:
- [ ] Clear explanation of feature
- [ ] Examples show before/after structure
- [ ] Backward compatibility documented
- [ ] Common use cases covered

---

#### Priority 2: Add Usage Examples

**New File**: `docs/DIRECTORY_STRUCTURE.md`

Comprehensive guide with examples:

```markdown
# Directory Structure Preservation Guide

## Overview

The cpptoc transpiler can preserve your source directory structure in the output,
similar to how TypeScript and Babel work.

## When to Use

Use structure preservation when:
- Your project has organized subdirectories (math/, utils/, core/, etc.)
- You have multiple files with the same name in different directories
- Your build system expects mirrored directory structures
- You want transpiled code to match source organization

## How It Works

The transpiler calculates relative paths from a source root:

```
Input:      /project/src/math/algebra/Vector.cpp
Source Root: /project/src
Output Dir:  /project/build

Relative Path: math/algebra/Vector.cpp
Output:        /project/build/math/algebra/Vector.h
               /project/build/math/algebra/Vector.c
```

## Examples

### Example 1: Simple Module Structure

Source:
```
myproject/
  src/
    core/
      Engine.cpp
    math/
      Vector.cpp
      Matrix.cpp
```

Command:
```bash
cpptoc --preserve-structure \
       --source-root src/ \
       --output-dir build/ \
       src/core/Engine.cpp src/math/*.cpp
```

Output:
```
myproject/
  build/
    core/
      Engine.h
      Engine.c
    math/
      Vector.h
      Vector.c
      Matrix.h
      Matrix.c
```

### Example 2: Including Tests

Source:
```
project/
  src/
    calculator.cpp
  tests/
    test_calculator.cpp
```

Command:
```bash
cpptoc --preserve-structure \
       --source-root . \
       --output-dir transpiled/ \
       src/calculator.cpp tests/test_calculator.cpp
```

Output:
```
project/
  transpiled/
    src/
      calculator.h
      calculator.c
    tests/
      test_calculator.h
      test_calculator.c
```

### Example 3: Handling Name Collisions

Without structure preservation:
```
src/frontend/Vector.cpp → build/Vector.h  ⚠️ Collision!
src/backend/Vector.cpp  → build/Vector.h  ⚠️ Collision!
```

With structure preservation:
```
src/frontend/Vector.cpp → build/frontend/Vector.h  ✓
src/backend/Vector.cpp  → build/backend/Vector.h   ✓
```

## Edge Cases

### Files Outside Source Root

Files outside the source root will fall back to basename only:

```bash
cpptoc --preserve-structure \
       --source-root src/ \
       vendor/external.cpp  # Outside src/

# Warning: File vendor/external.cpp is outside source root src/. Using basename only.
# Output: build/external.h (not build/../vendor/external.h)
```

### Symlinks

Symlinks are resolved before path calculation:

```
src/
  math/Vector.cpp (real file)
  alias/ → math/ (symlink)

Input: src/alias/Vector.cpp
Output: build/math/Vector.h (follows symlink)
```

## Migration Guide

### From Flat to Structured Output

1. Add `--preserve-structure` and `--source-root` flags
2. Update build scripts to expect nested directories
3. Test with your project

Before:
```bash
cpptoc --output-dir build/ src/**/*.cpp
```

After:
```bash
cpptoc --preserve-structure --source-root src/ --output-dir build/ src/**/*.cpp
```

## Integration with Build Systems

### CMake

```cmake
set(SOURCE_ROOT "${CMAKE_SOURCE_DIR}/src")
set(TRANSPILED_ROOT "${CMAKE_BINARY_DIR}/transpiled")

file(GLOB_RECURSE CPP_SOURCES "src/*.cpp")

foreach(SOURCE ${CPP_SOURCES})
    # Run cpptoc with structure preservation
    execute_process(
        COMMAND cpptoc
            --preserve-structure
            --source-root ${SOURCE_ROOT}
            --output-dir ${TRANSPILED_ROOT}
            ${SOURCE}
    )
endforeach()
```

### Makefile

```makefile
SRC_ROOT := src
BUILD_DIR := build

SOURCES := $(shell find $(SRC_ROOT) -name '*.cpp')

.PHONY: transpile
transpile:
	cpptoc --preserve-structure \
	       --source-root $(SRC_ROOT) \
	       --output-dir $(BUILD_DIR) \
	       $(SOURCES)
```

## Troubleshooting

**Error: --source-root is required when --preserve-structure is enabled**
- Solution: Add `--source-root <dir>` flag

**Warning: File ... is outside source root**
- Solution: Either include file in source root, or accept basename-only output

**Output directories not created**
- This is a bug - directories should be created automatically. Please report.

## FAQ

**Q: Can I use --source-root without --preserve-structure?**
A: No, --source-root is only used when --preserve-structure is enabled.

**Q: What if I don't specify --preserve-structure?**
A: The transpiler uses legacy behavior (flat output), maintaining backward compatibility.

**Q: Can I mix absolute and relative paths?**
A: Yes, the transpiler normalizes all paths before calculation.

**Q: Does this work on Windows?**
A: Yes, path handling is cross-platform using std::filesystem.
```

**Acceptance Criteria**:
- [ ] Comprehensive examples covering common scenarios
- [ ] Edge cases documented
- [ ] Integration with build systems shown
- [ ] Troubleshooting guide included

---

#### Priority 3: Update Help Text

**File**: `src/main.cpp`

Ensure help output is clear:

```bash
$ cpptoc --help

...

OPTIONS:
  --output-dir=<directory>
      Output directory for generated .c and .h files (default: current directory)

  --preserve-structure
      Preserve source directory structure in output (default: off)
      When enabled, the directory structure relative to --source-root is mirrored
      in the output directory. Example:
        Input:  src/math/Vector.cpp
        Root:   src/
        Output: build/math/Vector.h

  --source-root=<directory>
      Source root directory for calculating relative paths (required with --preserve-structure)
      All input files must be under this directory. Example: --source-root=src/

...
```

**Acceptance Criteria**:
- [ ] Help text is informative
- [ ] Examples clarify usage
- [ ] Requirements clearly stated

---

#### Priority 4: Add CHANGELOG Entry

**File**: `CHANGELOG.md` (create if doesn't exist)

```markdown
# Changelog

## [Unreleased]

### Added
- Directory structure preservation feature
  - New `--preserve-structure` flag to enable source directory mirroring
  - New `--source-root` flag to specify source root for path calculation
  - Automatic creation of nested output directories
  - Backward compatible: defaults to legacy flat output

### Technical Details
- Uses C++17 `std::filesystem` for cross-platform path handling
- Resolves symlinks via `fs::weakly_canonical()`
- Graceful fallback for files outside source root
- Comprehensive test coverage (unit + integration)

### Breaking Changes
- None (opt-in feature with backward compatibility)
```

**Acceptance Criteria**:
- [ ] CHANGELOG entry added
- [ ] Changes clearly described
- [ ] Backward compatibility noted

---

### Phase 4 Deliverables

- [ ] README updated with usage section
- [ ] Comprehensive guide in docs/DIRECTORY_STRUCTURE.md
- [ ] Help text enhanced
- [ ] CHANGELOG entry added
- [ ] Examples tested and verified

### Phase 4 Dependencies

- Phases 1-3 complete and tested

---

## Overall Success Criteria

### Functional Requirements
- [ ] User can transpile files with `--preserve-structure` flag and get mirrored directory structure
- [ ] Backward compatible: existing usage (without new flags) works unchanged
- [ ] All edge cases handled gracefully (files outside root, symlinks, etc.)
- [ ] Works cross-platform (Linux, macOS, Windows paths)

### Testing Requirements
- [ ] All existing tests pass (no regressions)
- [ ] New unit tests cover path calculation logic
- [ ] Integration tests validate end-to-end flow
- [ ] Real-world projects transpile successfully
- [ ] Edge cases tested and documented

### Documentation Requirements
- [ ] README has clear usage examples
- [ ] Comprehensive guide available
- [ ] Help text is informative
- [ ] CHANGELOG updated

### Code Quality
- [ ] Follows SOLID principles (SRP: path calc isolated; OCP: extensible)
- [ ] DRY: no duplication in path handling
- [ ] KISS: simple relative path algorithm
- [ ] Well-commented for maintainability

---

## Open Questions

### Design Decisions Needed

1. **Auto-detection of source root**: Should we implement auto-detection in Phase 1 or defer to future?
   - **Recommendation**: Defer - explicit flags are clearer for MVP

2. **Directory mode (--source-dir)**: Should we add a flag to transpile entire directories?
   - **Recommendation**: Defer to Phase 5 (future enhancement)

3. **Separate header/source output dirs**: Should .h and .c go to different directories?
   - **Recommendation**: No for MVP - same structure for both

4. **Symlink handling**: Follow symlinks or preserve them?
   - **Recommendation**: Follow symlinks (use `weakly_canonical()`)

### Questions for User

- **None** - research findings provide clear direction

---

## Assumptions

1. **C++17 available**: Project already uses `std::filesystem` (verified in research)
2. **Backward compatibility required**: Existing tests/users must not break
3. **TypeScript model preferred**: Users familiar with TypeScript will understand the design
4. **Opt-in is safer**: Default to legacy behavior, require explicit flag for new feature
5. **Build system integration**: Users will integrate into Make/CMake scripts

---

## Dependencies

### Code Dependencies
- C++17 standard library (`<filesystem>`)
- LLVM/Clang command line parsing (`llvm::cl`)
- Existing FileOutputManager class

### External Dependencies
- None (no new libraries)

### Tooling
- CMake for builds
- Google Test for unit tests
- Bash for integration test scripts

---

## Risks and Mitigation

### Risk: Platform-Specific Path Issues
**Probability**: Low
**Impact**: Medium
**Mitigation**: Use `std::filesystem` which is cross-platform; test on multiple platforms

### Risk: Performance Degradation
**Probability**: Very Low
**Impact**: Low
**Mitigation**: Path calculation is O(1) per file; negligible overhead

### Risk: Breaking Existing Users
**Probability**: Very Low (if backward compat maintained)
**Impact**: High
**Mitigation**: Opt-in design; comprehensive regression testing

### Risk: Incomplete Edge Case Handling
**Probability**: Medium
**Impact**: Low
**Mitigation**: Extensive testing in Phase 3; graceful fallbacks

---

## Future Enhancements (Not in This Plan)

1. **Auto-detection of source root** (find common parent of input files)
2. **Directory mode** (`--source-dir src/` to process all .cpp recursively)
3. **Glob pattern support** (`src/**/*.cpp` expansion by cpptoc itself)
4. **Separate header/source output directories**
5. **Custom path transformation rules**

---

## Implementation Timeline

| Phase | Duration | Cumulative |
|-------|----------|------------|
| Phase 1: Path Calculation | 2-3 hours | 2-3 hours |
| Phase 2: CLI Integration | 1-2 hours | 3-5 hours |
| Phase 3: Testing | 2-3 hours | 5-8 hours |
| Phase 4: Documentation | 1 hour | 6-9 hours |

**Total Estimated Effort**: 6-9 hours

---

## Confidence Assessment

### High Confidence
- Path calculation algorithm (well-understood, based on TypeScript model)
- Backward compatibility (opt-in design with defaults)
- Testing strategy (comprehensive coverage plan)

### Medium Confidence
- Cross-platform behavior (need to test on actual Windows/macOS)
- Real-world project edge cases (might discover new cases)

### Low Confidence
- User adoption (will users enable this feature?)

---

## Review Checklist

Before considering this plan complete:

- [x] All phases have clear goals and deliverables
- [x] Tasks are prioritized within each phase
- [x] Acceptance criteria defined for each task
- [x] Dependencies identified
- [x] Risks assessed and mitigated
- [x] Backward compatibility ensured
- [x] Testing strategy comprehensive
- [x] Documentation plan complete
- [x] Open questions addressed
- [x] Timeline estimated
- [x] Success criteria clear

---

## Appendix: Code Examples

### Complete Path Calculation Implementation

See Phase 1, Priority 2 for full implementation.

### CLI Flag Validation

See Phase 2, Priority 1 for complete validation logic.

### Integration Test Template

See Phase 3, Priority 2 for complete test cases.

---

**Plan Status**: Ready for Implementation
**Next Step**: Begin Phase 1 - Core Path Calculation Logic
**First Task**: Update FileOutputManager.h with new members

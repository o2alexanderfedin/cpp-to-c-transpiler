# Directory-Based Transpilation Implementation

<objective>
Implement directory-based transpilation with source directory structure preservation.

Purpose: Enable users to transpile entire projects while preserving directory structure (source-dir/dir1/dir2/file.cpp → target-dir/dir1/dir2/file.c)

Output: Modified FileOutputManager, CLI integration, comprehensive tests, updated documentation
</objective>

<context>
Research findings: @.prompts/035-dir-transpilation-research/dir-transpilation-research.md
Implementation plan: @.prompts/036-dir-transpilation-plan/dir-transpilation-plan.md

Existing code to modify:
@include/FileOutputManager.h
@src/FileOutputManager.cpp
@src/CppToCConsumer.cpp
@src/CppToCFrontendAction.cpp
@src/main.cpp
@tests/MultiFileTranspilationTest.cpp
</context>

<requirements>
**Functional Requirements:**
- Preserve source directory structure in output: `src/module/file.cpp` → `build/module/file.c`
- Add --source-dir CLI option to specify source root for path calculation
- Auto-detect source root if --source-dir not provided (common ancestor of input files)
- Create output subdirectories as needed
- Maintain backward compatibility (existing tests must pass)

**Quality Requirements:**
- Use std::filesystem::relative() for cross-platform path calculation (per research)
- Handle edge cases: files outside source root, absolute paths, symlinks
- Comprehensive test coverage (8+ new tests per plan)
- Follow existing code patterns and style
- Update all relevant documentation

**Constraints:**
- Must use C++17 filesystem library
- No breaking changes to existing API
- Follow SOLID principles (especially SRP for path calculation logic)
</requirements>

<implementation>
**Execute all 4 phases from plan:**

### Phase 1: Core Path Calculation
Modify FileOutputManager to calculate and preserve relative paths:

**Files to modify:**
- `include/FileOutputManager.h`:
  - Add `fs::path SourceRoot` private member
  - Add `sourceRoot` parameter to constructor
  - Add `fs::path calculateRelativePath(const fs::path& inputFile) const` private method
  - Add `void ensureOutputDirectories(const fs::path& outputPath) const` private method

- `src/FileOutputManager.cpp`:
  - Update constructor to accept and store source root
  - Implement `calculateRelativePath()` using `std::filesystem::relative()`
  - Implement `ensureOutputDirectories()` using `std::filesystem::create_directories()`
  - Modify `getFullPath()` to use `calculateRelativePath()` instead of `inputFile.filename()`
  - Handle edge case: if input file is outside source root, reject with error message

**Implementation notes:**
```cpp
// In FileOutputManager.cpp
fs::path FileOutputManager::calculateRelativePath(const fs::path& inputFile) const {
    if (SourceRoot.empty()) {
        // Backward compat: no source root = use basename only
        return inputFile.filename();
    }

    // Calculate relative path from source root
    fs::path absInput = fs::absolute(inputFile);
    fs::path absRoot = fs::absolute(SourceRoot);

    // Check if input is under source root
    auto relPath = fs::relative(absInput, absRoot);
    if (relPath.string().substr(0, 2) == "..") {
        // File is outside source root - reject
        throw std::runtime_error("Input file outside source root: " + inputFile.string());
    }

    return relPath;
}

fs::path FileOutputManager::getFullPath(const std::string& filename) const {
    fs::path inputFile(filename);
    fs::path relPath = calculateRelativePath(inputFile);

    // Construct output path preserving directory structure
    fs::path outputPath = OutputDir / relPath.parent_path() / (relPath.stem().string() + extension);

    // Ensure parent directories exist
    ensureOutputDirectories(outputPath);

    return outputPath;
}
```

### Phase 2: CLI Integration
Add --source-dir option and integrate with FileOutputManager:

**Files to modify:**
- `src/main.cpp`:
  - Add `static llvm::cl::opt<std::string> SourceDir(...)` following existing pattern
  - Add `std::string getSourceDir()` global accessor
  - Document in help text with examples

- `include/CppToCConsumer.h`:
  - Add `std::string SourceDir` member variable
  - Update constructor to accept source dir parameter

- `src/CppToCConsumer.cpp`:
  - Pass source dir to FileOutputManager constructor
  - If source dir empty, implement auto-detection: find common ancestor of all input files
  - Call `CodeGenerator::setOutputMode()` as before

- `src/CppToCFrontendAction.cpp`:
  - Pass `getSourceDir()` to CppToCConsumer constructor

**Implementation notes for auto-detection:**
```cpp
// In CppToCConsumer.cpp
std::string detectSourceRoot(const std::vector<std::string>& inputFiles) {
    if (inputFiles.empty()) return "";
    if (inputFiles.size() == 1) return fs::path(inputFiles[0]).parent_path().string();

    // Find common ancestor
    fs::path commonRoot = fs::path(inputFiles[0]).parent_path();
    for (size_t i = 1; i < inputFiles.size(); ++i) {
        fs::path filePath = fs::path(inputFiles[i]);
        while (!filePath.string().starts_with(commonRoot.string())) {
            commonRoot = commonRoot.parent_path();
            if (commonRoot.empty()) break;
        }
    }
    return commonRoot.string();
}
```

### Phase 3: Testing
Add comprehensive tests to MultiFileTranspilationTest:

**File to modify:**
- `tests/MultiFileTranspilationTest.cpp`

**New tests to add:**
1. **StructurePreservationBasic** - Simple 2-level nesting
2. **StructurePreservationDeep** - 4-level nesting
3. **StructurePreservationWithSourceDir** - Explicit --source-dir
4. **StructurePreservationAutoDetect** - No --source-dir (auto-detect)
5. **EdgeCaseFileOutsideRoot** - Verify rejection with clear error
6. **EdgeCaseAbsolutePaths** - Mix of absolute and relative input paths
7. **EdgeCaseEmptySourceDir** - Backward compat test (should use basename)
8. **MultipleProjectsPreserveStructure** - Multiple directories with same basenames

**Test implementation pattern:**
```cpp
TEST_F(MultiFileTranspilationTest, StructurePreservationBasic) {
    // Create test structure: temp/src/module1/file1.cpp, temp/src/module2/file2.cpp
    CreateTestFile(tempDir / "src/module1/file1.cpp", simpleCppContent);
    CreateTestFile(tempDir / "src/module2/file2.cpp", simpleCppContent);

    // Run transpiler with --source-dir
    RunTranspiler({
        tempDir / "src/module1/file1.cpp",
        tempDir / "src/module2/file2.cpp"
    }, {
        "--source-dir=" + (tempDir / "src").string(),
        "--output-dir=" + (tempDir / "output").string()
    });

    // Verify structure preserved
    ASSERT_TRUE(fs::exists(tempDir / "output/module1/file1.c"));
    ASSERT_TRUE(fs::exists(tempDir / "output/module1/file1.h"));
    ASSERT_TRUE(fs::exists(tempDir / "output/module2/file2.c"));
    ASSERT_TRUE(fs::exists(tempDir / "output/module2/file2.h"));
}
```

**Verification:**
- All new tests pass
- All existing tests pass (backward compatibility)
- Run full test suite: `cd build_working && ctest -V`

### Phase 4: Documentation
Update all relevant documentation:

**Files to modify:**
- `README.md`:
  - Add "Directory Structure Preservation" subsection in Multi-File section
  - Show before/after example with directory trees
  - Document --source-dir option with examples

- `docs/MULTI_FILE_TRANSPILATION.md`:
  - Add new section "Directory Structure Preservation"
  - Explain auto-detection vs explicit --source-dir
  - Document edge cases and their behavior
  - Add real-world example using tests/real-world/

- `docs/FAQ.md`:
  - Update Q10 about multi-file support to mention structure preservation
  - Add Q11: "How does cpptoc handle directory structures?"

- `docs/api-reference/cli-options.md`:
  - Add --source-dir option documentation
  - Update Example 3 to show structure preservation

- `transpile_all.sh`:
  - Update to use --source-dir=./tests/real-world

**Example documentation content:**
````markdown
### Directory Structure Preservation

By default, cpptoc preserves the source directory structure in the output:

```bash
cpptoc --source-dir=./src --output-dir=./build src/**/*.cpp
```

**Input structure:**
```
src/
├── core/
│   ├── engine.cpp
│   └── utils.cpp
└── ui/
    └── window.cpp
```

**Output structure:**
```
build/
├── core/
│   ├── engine.c
│   ├── engine.h
│   ├── utils.c
│   └── utils.h
└── ui/
    ├── window.c
    └── window.h
```

**Auto-detection:** If `--source-dir` is omitted, cpptoc automatically detects the common ancestor of all input files.
````

**What to avoid:**
- Do NOT change existing FileOutputManager behavior when source root is empty (backward compat)
- Do NOT use manual string manipulation for paths (use std::filesystem)
- Do NOT suppress errors for files outside source root (fail clearly)
- Do NOT skip creating output directories (ensure parent dirs exist)

**Integration points:**
- FileOutputManager integrates with existing CppToCConsumer workflow
- CLI option follows existing patterns from main.cpp
- Tests extend existing MultiFileTranspilationTest framework
- Documentation updates complement existing multi-file docs
</implementation>

<output>
**Modified files:**
Core implementation:
- `include/FileOutputManager.h` - Add source root support
- `src/FileOutputManager.cpp` - Implement path calculation
- `src/main.cpp` - Add --source-dir CLI option
- `include/CppToCConsumer.h` - Add source dir parameter
- `src/CppToCConsumer.cpp` - Pass source dir, implement auto-detect
- `src/CppToCFrontendAction.cpp` - Pass source dir to consumer

Testing:
- `tests/MultiFileTranspilationTest.cpp` - Add 8+ new tests

Documentation:
- `README.md` - Add structure preservation section
- `docs/MULTI_FILE_TRANSPILATION.md` - Add comprehensive guide section
- `docs/FAQ.md` - Add Q11 about directory handling
- `docs/api-reference/cli-options.md` - Document --source-dir
- `transpile_all.sh` - Update with --source-dir example
</output>

<verification>
**Before declaring complete:**

1. **Build verification:**
   ```bash
   cd build_working
   cmake --build . -j8
   # Should build without errors
   ```

2. **Test verification:**
   ```bash
   # Run new tests
   ./MultiFileTranspilationTest --gtest_filter="*StructurePreservation*"

   # Run all tests for backward compat
   ctest -V
   # All existing tests must pass
   ```

3. **Functional verification:**
   ```bash
   # Test with real-world directory
   ./cpptoc \
     --source-dir=../tests/real-world \
     --output-dir=../tests/real-world/transpiled-structured \
     ../tests/real-world/json-parser/src/*.cpp \
     -- -I../tests/real-world/json-parser/include -std=c++17

   # Verify structure preserved
   ls -R ../tests/real-world/transpiled-structured/
   # Should see: json-parser/src/*.c and *.h
   ```

4. **Edge case verification:**
   ```bash
   # Test auto-detection
   ./cpptoc \
     --output-dir=/tmp/test-output \
     ../tests/real-world/json-parser/src/JsonParser.cpp \
     ../tests/real-world/json-parser/src/JsonValue.cpp
   # Should auto-detect source root and preserve structure

   # Test file outside root (should fail gracefully)
   ./cpptoc \
     --source-dir=../tests/real-world/json-parser \
     --output-dir=/tmp/test \
     ../tests/real-world/logger/tests/examples.cpp
   # Should error: "Input file outside source root"
   ```

5. **Documentation verification:**
   - Verify README.md renders correctly in GitHub
   - Check all documentation examples are accurate
   - Ensure all cross-references are valid
</verification>

<summary_requirements>
Create `.prompts/037-dir-transpilation-implement/SUMMARY.md`:

```markdown
# Directory-Based Transpilation Implementation

**Complete directory structure preservation with --source-dir option**

## Files Created/Modified
**Core (6 files):**
- include/FileOutputManager.h - Added source root support
- src/FileOutputManager.cpp - Path calculation with fs::relative()
- src/main.cpp - Added --source-dir CLI option
- include/CppToCConsumer.h - Source dir parameter
- src/CppToCConsumer.cpp - Auto-detection logic
- src/CppToCFrontendAction.cpp - Integration

**Testing (1 file):**
- tests/MultiFileTranspilationTest.cpp - 8 new tests

**Documentation (5 files):**
- README.md - Structure preservation section
- docs/MULTI_FILE_TRANSPILATION.md - Comprehensive guide
- docs/FAQ.md - Q11 added
- docs/api-reference/cli-options.md - --source-dir docs
- transpile_all.sh - Updated example

## Test Results
- [X/X] All new tests passing
- [Y/Y] All existing tests passing (backward compat verified)
- Functional test: real-world transpilation preserves structure

## Decisions Needed
None - implementation complete per plan

## Blockers
None

## Next Step
Test with real user projects, gather feedback on auto-detection behavior
```
</summary_requirements>

<success_criteria>
**Implementation complete when:**
- All 4 phases from plan are implemented
- FileOutputManager preserves directory structure using fs::relative()
- --source-dir CLI option works (both explicit and auto-detect)
- All 8+ new tests pass
- All existing tests pass (backward compatibility)
- Build succeeds without warnings
- Real-world transpilation preserves structure correctly
- All documentation updated with examples
- Edge cases handled gracefully (files outside root rejected)
- SUMMARY.md created with file list and test results
- Code follows project conventions and SOLID principles
</success_criteria>

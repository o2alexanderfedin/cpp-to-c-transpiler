# Directory-Based Transpilation Research

## Metadata
- **Date**: 2025-12-23
- **Researcher**: Claude Code
- **Objective**: Research directory-based transpilation with source directory structure preservation for cpptoc
- **Status**: Complete

## Executive Summary

### Current State

The cpptoc transpiler currently **strips all directory structure** from input files, placing all output files (.h and .c) in a flat output directory. This is implemented in `FileOutputManager::getBaseName()` which extracts only the filename using `find_last_of("/\\")`.

**Problem**: When transpiling projects with organized directory structures (e.g., `src/math/algebra/Vector.cpp` and `src/math/geometry/Point.cpp`), all output files are placed directly in the output directory, losing the `math/algebra/` and `math/geometry/` structure. This can cause:
1. Name collisions (two `Vector.cpp` files in different directories)
2. Loss of logical organization
3. Incompatibility with build systems expecting mirrored directory structures

### Industry Standard

Both TypeScript and Babel transpilers **preserve source directory structure** in output:
- **TypeScript**: Uses `rootDir` (source root) and `outDir` (output directory) options. Path calculation: `outputPath = outDir + (sourcePath - rootDir)`
- **Babel**: Automatically preserves structure when transpiling directories with `babel src -d lib`

This is the expected behavior for transpilers (as opposed to compilers like GCC which rely on build systems for path management).

### Recommended Solution

**Implement opt-in directory structure preservation** with backward compatibility:

1. **Phase 1** (Minimum Viable): Add CLI flags:
   - `--preserve-structure`: Enable structure preservation (default: off for backward compatibility)
   - `--source-root <dir>`: Specify source root for relative path calculation (required when --preserve-structure is used)

2. **Implementation**: Use C++17 `<filesystem>` (already in codebase) for:
   - Relative path calculation: `fs::path::lexically_relative()`
   - Symlink resolution: `fs::weakly_canonical()`
   - Directory creation: `fs::create_directories()`

3. **Path Calculation Algorithm**:
   ```cpp
   // Input: /project/src/math/algebra/Vector.cpp
   // Source Root: /project/src
   // Output Dir: /project/build

   fs::path inputPath = fs::weakly_canonical(inputFilename);
   fs::path rootPath = fs::weakly_canonical(sourceRootDir);
   fs::path relPath = inputPath.lexically_relative(rootPath);  // math/algebra/Vector.cpp
   relPath.replace_extension(".h");  // math/algebra/Vector.h
   outputPath = outputDir / relPath;  // /project/build/math/algebra/Vector.h
   ```

4. **Benefits**:
   - Solves name collision problem (major benefit for real projects)
   - Matches user expectations from TypeScript/Babel
   - Enables transpiling entire project directories with preserved organization
   - Backward compatible (opt-in via flag)

### Key Findings

✓ Path stripping happens in `FileOutputManager::getBaseName()` line 30
✓ No existing tests verify directory structure (new feature)
✓ Real-world test projects (json-parser, logger) use `src/` and `tests/` subdirectories
✓ Structure preservation is essential for real-world C++ projects
✓ `std::filesystem` already available in codebase (C++17)
✓ Both / and \\ separators already handled correctly

### Implementation Complexity

**Low to Medium**:
- Core logic: ~100 lines of code in FileOutputManager
- CLI flags: ~20 lines in main.cpp
- Tests: ~200 lines for comprehensive coverage
- Estimated effort: 4-6 hours for complete implementation with tests

---

## Current Implementation Analysis

### FileOutputManager Path Handling

**File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/FileOutputManager.cpp`

#### Basename Extraction (Lines 21-44)

The critical path-stripping logic is in the `getBaseName()` method:

```cpp
std::string FileOutputManager::getBaseName() const {
    // Extract base name: "Point.cpp" → "Point"
    // KISS: Simple string manipulation
    size_t lastSlash = inputFilename.find_last_of("/\\");
    size_t lastDot = inputFilename.find_last_of('.');

    // Get filename without path
    std::string filename;
    if (lastSlash != std::string::npos) {
        filename = inputFilename.substr(lastSlash + 1);  // ⚠️ PATH STRIPPED HERE
    } else {
        filename = inputFilename;
    }

    // Remove extension
    if (lastDot != std::string::npos) {
        size_t dotPosition = filename.find_last_of('.');
        if (dotPosition != std::string::npos) {
            filename = filename.substr(0, dotPosition);
        }
    }

    return filename;
}
```

**Key Finding**: Line 30 strips ALL path information using `find_last_of("/\\")` and taking only the substring after the last slash. This means:
- Input: `src/math/algebra/Vector.cpp`
- Output: `Vector` (all directory structure lost)

#### Output Path Construction (Lines 46-81)

The `getFullPath()` method combines output directory with filename:

```cpp
std::string FileOutputManager::getFullPath(const std::string& filename) const {
    // If output directory is set, prepend it to the filename
    if (!outputDir.empty()) {
        // Ensure proper path separator
        if (outputDir.back() == '/' || outputDir.back() == '\\') {
            return outputDir + filename;
        } else {
            return outputDir + "/" + filename;
        }
    }
    return filename;
}
```

**Key Finding**: This method only prepends the output directory - it does NOT preserve any intermediate directory structure from the input path.

#### Call Chain

1. **CppToCConsumer.cpp** (Lines 95-102):
   ```cpp
   FileOutputManager outputMgr;
   outputMgr.setInputFilename(InputFilename);  // Full path passed here

   std::string outputDir = getOutputDir();
   if (!outputDir.empty()) {
       outputMgr.setOutputDir(outputDir);
   }
   ```

2. **FileOutputManager::getHeaderFilename()** (Lines 59-69):
   ```cpp
   std::string baseFilename;
   if (!outputHeader.empty()) {
       baseFilename = outputHeader;
   } else {
       baseFilename = getBaseName() + ".h";  // ⚠️ Path stripped here
   }

   return getFullPath(baseFilename);  // Only outputDir prepended
   ```

**Verified Behavior**:
- Input: `/path/to/src/geometry/shapes/Rectangle.cpp`
- Output Dir: `/path/to/build`
- Result: `/path/to/build/Rectangle.h` and `/path/to/build/Rectangle.c`
- **Lost**: `geometry/shapes/` directory structure

### Current CLI Interface

**File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/main.cpp` (Lines 24-28)

```cpp
// Command line option for output directory
static llvm::cl::opt<std::string> OutputDir(
    "output-dir",
    llvm::cl::desc("Output directory for generated .c and .h files (default: current directory)"),
    llvm::cl::value_desc("directory"),
    llvm::cl::cat(ToolCategory));
```

**Current Behavior**:
- User provides list of files: `cpptoc file1.cpp file2.cpp --output-dir build/`
- Each file is processed independently
- All output files are placed directly in `build/` with no subdirectories

### Test Expectations

**File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/MultiFileTranspilationTest.cpp`

All tests expect flat output directory:
- Test 1 (Lines 120-168): `Point.cpp` → `outputDir/Point.h` + `outputDir/Point.c`
- Test 2 (Lines 170-227): Multiple files → all in same `outputDir/`
- Test 5 (Lines 312-335): Relative paths → still flat output

**Key Finding**: No existing tests verify directory structure preservation - this is a new feature.

---

## Industry Standards Research

### TypeScript Compiler (tsc)

**Sources**:
- [TypeScript: TSConfig Option: rootDir](https://www.typescriptlang.org/tsconfig/rootDir.html)
- [TypeScript: TSConfig Option: outDir](https://www.typescriptlang.org/tsconfig/outDir.html)
- [Progress on TypeScript 7 - December 2025](https://devblogs.microsoft.com/typescript/progress-on-typescript-7-december-2025/)

#### Configuration Options

TypeScript uses two key options:

1. **`rootDir`**: Specifies the root directory of input files
   - Determines the structure to preserve
   - Does NOT affect which files are compiled (separate from include/exclude)
   - Defaults to directory containing tsconfig.json (as of TypeScript 7.0)

2. **`outDir`**: Specifies output directory
   - Files emitted here preserve directory structure from rootDir
   - Example: `rootDir: "./src"`, `outDir: "./dist"`

#### Example

```
Source structure:
  src/
    math/
      algebra/
        Vector.ts
      geometry/
        Point.ts
    utils/
      helpers.ts

With rootDir="./src" and outDir="./dist":

Output structure:
  dist/
    math/
      algebra/
        Vector.js
      geometry/
        Point.js
    utils/
      helpers.js
```

**Path Calculation**: `outputPath = outDir + (sourcePath - rootDir)`

#### TypeScript 7.0 Changes (December 2025)

- `rootDir` now defaults to current directory
- Using `outDir` requires either:
  - Explicit `rootDir` setting, OR
  - Top-level source files in same directory as tsconfig.json

**Design Rationale**: Prevents ambiguity about which directory structure to preserve.

### Babel Transpiler

**Sources**:
- [Output directory structure is not preserved in first compilation](https://github.com/babel/babel/issues/7849)
- [Using Babel.js · NodeJS Tutorials](https://xpepermint.gitbooks.io/nodejs-cheatsheet/content/using_babel.html)
- [BabelJS - Quick Guide](https://www.tutorialspoint.com/babeljs/babeljs_quick_guide.htm)

#### CLI Interface

Standard directory transpilation:

```bash
babel ./src -d ./lib
# or
babel ./src --out-dir ./dist --copy-files
```

- `-d` / `--out-dir`: Output directory
- Directory structure from `./src` is automatically preserved in output
- `--copy-files`: Also copies non-JS files (e.g., .json, .css)

#### Convention

- **Source dir**: `./src` (standard convention)
- **Output dir**: `./lib` or `./dist` (both common)
- **Structure**: Always preserved automatically when transpiling a directory

#### Example

```
Source:
  src/
    components/
      Button.jsx
      Input.jsx
    utils/
      format.js

Command: babel src -d lib

Output:
  lib/
    components/
      Button.js
      Input.js
    utils/
      format.js
```

**Key Finding**: Babel treats directory as implicit rootDir - structure relative to specified source directory is always preserved.

### GCC/Clang Compiler Behavior

**Observation**: GCC and Clang do NOT preserve directory structure by default:

```bash
gcc -c src/math/Vector.cpp -o build/
# Creates: build/Vector.o (not build/math/Vector.o)
```

**Rationale**: Compilers are typically invoked by build systems (Make, CMake, Ninja) which:
1. Explicitly control output paths per-file
2. Use target-specific rules
3. Handle directory creation

**Build System Example (CMake)**:

```cmake
# CMake preserves structure by mirroring directories
file(GLOB_RECURSE SOURCES "src/*.cpp")
foreach(SOURCE ${SOURCES})
    # Calculate relative path
    file(RELATIVE_PATH REL_PATH "${CMAKE_SOURCE_DIR}/src" "${SOURCE}")
    get_filename_component(REL_DIR "${REL_PATH}" DIRECTORY)

    # Create output directory
    set(OUTPUT_DIR "${CMAKE_BINARY_DIR}/${REL_DIR}")
    file(MAKE_DIRECTORY "${OUTPUT_DIR}")
endforeach()
```

**Key Finding**: Compilers are low-level tools; transpilers (TypeScript, Babel) are higher-level and provide directory preservation.

---

## Path Preservation Approaches

### Approach 1: Relative Path Calculation (TypeScript Style)

**Algorithm**:
```
1. Determine source root directory (rootDir)
2. For each input file:
   a. Calculate relative path: relPath = inputPath - rootDir
   b. Construct output path: outputPath = outDir + relPath
   c. Change extension: .cpp → .h/.c
```

**Example**:
```
rootDir:   /project/src
inputFile: /project/src/math/algebra/Vector.cpp
relPath:   math/algebra/Vector.cpp
outDir:    /project/build
outputH:   /project/build/math/algebra/Vector.h
outputC:   /project/build/math/algebra/Vector.c
```

**C++ Implementation** (pseudo-code):
```cpp
std::string FileOutputManager::calculateRelativePath(
    const std::string& filePath,
    const std::string& rootDir
) const {
    // Normalize both paths (resolve .., symlinks, etc.)
    fs::path normalizedFile = fs::weakly_canonical(filePath);
    fs::path normalizedRoot = fs::weakly_canonical(rootDir);

    // Calculate relative path
    fs::path relPath = normalizedFile.lexically_relative(normalizedRoot);

    return relPath.string();
}

std::string FileOutputManager::getHeaderFilename() const {
    if (!outputHeader.empty()) {
        return getFullPath(outputHeader);
    }

    if (sourceRootDir.empty()) {
        // Legacy behavior: strip path
        return getFullPath(getBaseName() + ".h");
    }

    // New behavior: preserve structure
    fs::path relPath = calculateRelativePath(inputFilename, sourceRootDir);
    relPath.replace_extension(".h");
    return getFullPath(relPath.string());
}
```

**Pros**:
- Industry standard (TypeScript, Babel)
- Clear semantics
- Handles complex paths correctly
- Cross-platform (std::filesystem)

**Cons**:
- Requires C++17 `<filesystem>` (already used in codebase - verified in MultiFileTranspilationTest.cpp)
- More complex than current implementation
- Requires new CLI option for source root

### Approach 2: Automatic Root Detection

**Algorithm**:
```
1. User provides multiple input files
2. Find common parent directory of all input files
3. Use that as implicit rootDir
4. Preserve structure relative to common parent
```

**Example**:
```
Input files:
  /project/src/math/Vector.cpp
  /project/src/utils/helpers.cpp
  /project/src/geometry/shapes/Rectangle.cpp

Common parent: /project/src
Auto-detected rootDir: /project/src
```

**C++ Implementation**:
```cpp
// In main.cpp or new DirectoryManager class
std::string findCommonParent(const std::vector<std::string>& files) {
    if (files.empty()) return "";
    if (files.size() == 1) {
        return fs::path(files[0]).parent_path().string();
    }

    fs::path common = fs::path(files[0]).parent_path();

    for (size_t i = 1; i < files.size(); ++i) {
        fs::path current = fs::path(files[i]).parent_path();

        // Find common prefix
        auto commonIt = common.begin();
        auto currentIt = current.begin();
        fs::path newCommon;

        while (commonIt != common.end() &&
               currentIt != current.end() &&
               *commonIt == *currentIt) {
            newCommon /= *commonIt;
            ++commonIt;
            ++currentIt;
        }

        common = newCommon;
    }

    return common.string();
}
```

**Pros**:
- No need for explicit rootDir option (user-friendly)
- Works with any file list
- Matches Babel's behavior

**Cons**:
- Ambiguous for single file (parent dir? current dir?)
- May surprise users if common parent is higher than expected
- Fails with absolute paths from different roots

### Approach 3: Hybrid Approach (Recommended)

**Algorithm**:
```
1. If --source-root specified → use it (explicit)
2. Else if multiple files → auto-detect common parent
3. Else (single file) → use parent directory
4. Always preserve structure relative to detected/specified root
```

**Pros**:
- Combines best of both approaches
- Backward compatible (can default to current behavior)
- Flexible for different use cases
- Clear fallback rules

**Cons**:
- Most complex to implement
- Requires careful testing of all cases

---

## Edge Cases Analysis

### 1. Absolute vs Relative Input Paths

**Scenario**:
```bash
# Mixed absolute and relative paths
cpptoc /home/user/project/src/math/Vector.cpp src/utils/helpers.cpp
```

**Issue**: Cannot calculate common parent of absolute and relative paths

**Solution**:
- Convert all input paths to absolute using `fs::absolute()`
- Then find common parent
- Or: require all inputs to be relative if using auto-detection

### 2. Symlinks in Source Tree

**Scenario**:
```
Real structure:
  src/math/Vector.cpp (real file)
  src/algebra/ → symlink to src/math/

Input: src/algebra/Vector.cpp
```

**Issue**: Should output be `build/algebra/Vector.h` or `build/math/Vector.h`?

**TypeScript Behavior**: Uses `fs::weakly_canonical()` to resolve symlinks before path calculation

**Recommendation**: Use `fs::weakly_canonical()` to resolve symlinks and use real paths

### 3. Files Outside Source Root (../)

**Scenario**:
```
rootDir: /project/src
Input: /project/vendor/external.cpp (outside rootDir)
```

**Issue**: Relative path would be `../vendor/external.cpp` - how to handle?

**TypeScript Behavior**: Error - files must be under rootDir

**Babel Behavior**: Ignores files outside source directory

**Recommendation**:
- Option A: Error - require all files under rootDir
- Option B: Fall back to basename for out-of-tree files (with warning)
- **Preferred**: Option A for safety

### 4. Name Collisions

**Scenario**:
```
src/
  frontend/Vector.cpp
  backend/Vector.cpp

Without structure preservation:
  build/Vector.h (collision!)
  build/Vector.c (collision!)

With structure preservation:
  build/frontend/Vector.h ✓
  build/frontend/Vector.c ✓
  build/backend/Vector.h ✓
  build/backend/Vector.c ✓
```

**Key Finding**: Structure preservation SOLVES the collision problem - this is a major benefit!

### 5. Output Directory Creation

**Current Code** (FileOutputManager.cpp lines 83-101):
```cpp
bool FileOutputManager::writeFile(const std::string& filename, const std::string& content) {
    std::ofstream outFile(filename);  // ⚠️ No directory creation!

    if (!outFile.is_open()) {
        std::cerr << "Error: Could not open file for writing: " << filename << std::endl;
        return false;
    }
    // ...
}
```

**Issue**: If output path is `build/math/algebra/Vector.h` and `build/math/algebra/` doesn't exist, write will fail

**Solution**: Create parent directories before writing:
```cpp
bool FileOutputManager::writeFile(const std::string& filename, const std::string& content) {
    // Create parent directories if they don't exist
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

    std::ofstream outFile(filename);
    // ...
}
```

**Permission Handling**: `create_directories()` uses parent directory permissions - should be safe in most cases

### 6. Windows vs Unix Paths

**Issue**:
- Unix: `/path/to/file` with `/` separator
- Windows: `C:\path\to\file` with `\` separator

**Current Code** (FileOutputManager.cpp line 24):
```cpp
size_t lastSlash = inputFilename.find_last_of("/\\");  // ✓ Already handles both!
```

**Solution**: Use `std::filesystem::path` which handles platform differences:
```cpp
fs::path inputPath(inputFilename);
fs::path baseName = inputPath.filename();  // Cross-platform
```

**Key Finding**: `std::filesystem` is already cross-platform - use it throughout for safety

---

## Command-Line Interface Design

### Option 1: Explicit Source Root (TypeScript Style)

```bash
cpptoc --source-root src/ --output-dir build/ src/**/*.cpp
```

**Flags**:
- `--source-root <dir>`: Source root directory for path calculation
- `--output-dir <dir>`: Output directory (existing flag)

**Pros**:
- Explicit and clear
- No ambiguity
- Matches TypeScript users' expectations

**Cons**:
- Extra flag to specify
- Not intuitive for Babel users

### Option 2: Implicit Detection (Babel Style)

```bash
cpptoc src/ --output-dir build/
```

**Behavior**:
- First argument is source directory
- All .cpp files found recursively
- Structure preserved automatically

**Pros**:
- Simple and intuitive
- Matches Babel users' expectations
- No extra flags

**Cons**:
- Can't specify individual files anymore
- Breaking change from current CLI
- What if user wants to process single file from deep directory?

### Option 3: Hybrid (Recommended)

```bash
# Explicit source root
cpptoc --source-root src/ --output-dir build/ src/math/*.cpp src/utils/*.cpp

# Implicit (auto-detect common parent)
cpptoc --output-dir build/ src/math/Vector.cpp src/utils/helpers.cpp

# Directory mode (new)
cpptoc --source-dir src/ --output-dir build/

# Single file (backward compatible - uses parent dir as root)
cpptoc --output-dir build/ Point.cpp
```

**Flags**:
- `--source-root <dir>`: Explicit source root (optional)
- `--source-dir <dir>`: Process all .cpp in directory recursively (new)
- `--output-dir <dir>`: Output directory (existing)
- If neither `--source-root` nor `--source-dir`: auto-detect from file list

**Pros**:
- Flexible - supports all use cases
- Backward compatible (single file still works)
- Can optimize later (add --source-dir for convenience)

**Cons**:
- Most complex to implement
- Need clear documentation of precedence rules

### Option 4: Minimal Addition (Backward Compatible)

```bash
# Current behavior (default)
cpptoc --output-dir build/ file1.cpp file2.cpp
# → build/file1.h, build/file1.c, build/file2.h, build/file2.c

# New flag to enable structure preservation
cpptoc --preserve-structure --source-root src/ --output-dir build/ src/**/*.cpp
# → build/math/Vector.h, build/math/Vector.c, etc.
```

**Flags**:
- `--preserve-structure`: Enable directory structure preservation (opt-in)
- `--source-root <dir>`: Required when --preserve-structure is used

**Pros**:
- 100% backward compatible (default behavior unchanged)
- Clear opt-in for new feature
- Safe migration path

**Cons**:
- Extra flag needed
- Less convenient than auto-detection

---

## Quality Assessment

### Verified Facts (High Confidence)

✓ Current implementation strips all path information in FileOutputManager::getBaseName() (line 30)
✓ No directory structure preservation in current implementation
✓ TypeScript uses rootDir + outDir for structure preservation
✓ Babel auto-detects source root and preserves structure
✓ std::filesystem is already used in codebase (MultiFileTranspilationTest.cpp)
✓ Current code handles both / and \ separators
✓ No existing tests for directory structure preservation
✓ Structure preservation solves name collision problem

### Research-Based (Medium Confidence)

◐ TypeScript 7.0 behavior changes (based on December 2025 dev blog)
◐ Babel common conventions (src/ → lib/ or dist/)
◐ GCC/Clang don't preserve structure (compilers vs transpilers difference)

### Assumptions (Low Confidence)

◯ Users want directory structure preserved (need to validate)
◯ Common parent auto-detection is intuitive
◯ Permission issues are rare with create_directories()

### Unknowns / Need More Research

? How does cpptoc handle multiple files currently in practice?
? Are users experiencing name collisions now?
✓ **What directory structures do real C++ projects use?** (answered below)
? Do users process files from multiple roots?
? Should .h and .c files go to same output dir or separate dirs?

### Real-World C++ Project Structures (Additional Research)

**Sources**:
- [How to Organize a C++ Project: Directory Structure and Best Practices](https://www.studyplan.dev/cmake/organizing-a-cpp-project)
- [Best Practices for Structuring C++ Projects (Industry Standards)](https://medium.com/@gtech.govind2000/best-practices-for-structuring-c-projects-industry-standards-71b82f6b145c)
- [Canonical Project Structure](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2018/p1204r0.html)

#### Common Directory Structure Patterns

**Standard Layout** (most common):
```
project/
  src/          # .cpp implementation files
  include/      # .h/.hpp public headers
  tests/        # Test files
  build/        # Build output (out-of-source builds)
  libs/         # External dependencies
  docs/         # Documentation
```

**Modular Layout** (for larger projects):
```
project/
  src/
    module1/
      submodule_a/
        File1.cpp
        File2.cpp
    module2/
      File3.cpp
  include/
    module1/
      submodule_a/
        File1.h
        File2.h
    module2/
      File3.h
```

**Unified Layout** (headers and source together):
```
project/
  src/
    module1/
      File1.h
      File1.cpp
    module2/
      File2.h
      File2.cpp
```

#### cpptoc Real-World Test Examples

Checked `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/`:

```
json-parser/
  src/
    JsonParser.cpp
    JsonValue.cpp
  tests/
    test_json_parser.cpp
    examples.cpp

logger/
  tests/
    test_logger.cpp
    examples.cpp

resource-manager/
  tests/
    test_resource_manager.cpp

string-formatter/
  tests/
    test_string_formatter.cpp

test-framework/
  tests/
    test_framework.cpp
    examples.cpp
```

**Key Finding**: Real projects use `src/` and `tests/` subdirectories. When transpiling, users would expect:
- `src/JsonParser.cpp` → `build/src/JsonParser.h` + `build/src/JsonParser.c`
- `tests/test_json_parser.cpp` → `build/tests/test_json_parser.h` + `build/tests/test_json_parser.c`

This confirms the need for structure preservation!

---

## Recommendations

### Primary Recommendation: Hybrid Approach with Opt-In

**Implementation Strategy**:

1. **Add new optional flags** (Phase 1 - backward compatible):
   ```cpp
   // In main.cpp
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

2. **Update FileOutputManager** to support both modes:
   ```cpp
   class FileOutputManager {
   public:
       void setInputFilename(const std::string& filename);
       void setOutputDir(const std::string& dir);
       void setSourceRoot(const std::string& root);  // NEW
       void setPreserveStructure(bool preserve);      // NEW
       // ... existing methods

   private:
       std::string sourceRootDir;                     // NEW
       bool preserveStructure = false;                // NEW

       // NEW: Calculate output path with structure preservation
       std::string calculateOutputPath(const std::string& extension) const;
   };
   ```

3. **Implement relative path calculation**:
   ```cpp
   std::string FileOutputManager::calculateOutputPath(const std::string& extension) const {
       if (!preserveStructure || sourceRootDir.empty()) {
           // Legacy behavior
           return getFullPath(getBaseName() + extension);
       }

       // New behavior: preserve structure
       fs::path inputPath = fs::weakly_canonical(inputFilename);
       fs::path rootPath = fs::weakly_canonical(sourceRootDir);
       fs::path relPath = inputPath.lexically_relative(rootPath);

       // Check if file is under source root
       if (relPath.string().starts_with("..")) {
           std::cerr << "Warning: File " << inputFilename
                     << " is outside source root " << sourceRootDir
                     << ", using basename only" << std::endl;
           return getFullPath(getBaseName() + extension);
       }

       // Replace extension
       relPath.replace_extension(extension);

       return getFullPath(relPath.string());
   }
   ```

4. **Add directory creation** in writeFile():
   ```cpp
   bool FileOutputManager::writeFile(const std::string& filename,
                                      const std::string& content) {
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

       // ... existing write logic
   }
   ```

5. **Wire up in CppToCConsumer**:
   ```cpp
   // In HandleTranslationUnit
   FileOutputManager outputMgr;
   outputMgr.setInputFilename(InputFilename);

   if (!outputDir.empty()) {
       outputMgr.setOutputDir(outputDir);
   }

   if (shouldPreserveStructure()) {                    // NEW
       outputMgr.setPreserveStructure(true);            // NEW
       outputMgr.setSourceRoot(getSourceRoot());        // NEW
   }
   ```

### Secondary Recommendation: Auto-Detection Enhancement (Phase 2)

After Phase 1 is stable, add auto-detection:

```cpp
// In main.cpp after parsing all files
if (PreserveStructure && SourceRoot.empty() && files.size() > 1) {
    // Auto-detect common parent
    std::string commonParent = findCommonParent(files);
    llvm::outs() << "Auto-detected source root: " << commonParent << "\n";
    SourceRoot.setValue(commonParent);
}
```

### Alternative: Directory Mode (Future Enhancement)

Add `--source-dir` for full directory processing:

```cpp
static llvm::cl::opt<std::string> SourceDir(
    "source-dir",
    llvm::cl::desc("Process all .cpp files in directory recursively"),
    llvm::cl::value_desc("directory"),
    llvm::cl::cat(ToolCategory));

// If SourceDir is set:
// 1. Find all .cpp files recursively
// 2. Use SourceDir as source root automatically
// 3. Enable preserve-structure automatically
```

---

## Next Steps

### For Planning Phase

1. **Design Decisions Needed**:
   - [ ] Choose CLI flag names (--preserve-structure vs --mirror-structure vs auto)
   - [ ] Decide on auto-detection: always, never, or opt-in?
   - [ ] Determine error handling for files outside source root
   - [ ] Decide if --preserve-structure should default to true or false

2. **API Design**:
   - [ ] Should TranspilerAPI support directory mode?
   - [ ] Add sourceRoot to TranspileOptions struct?
   - [ ] How to pass sourceRoot in WASM bindings?

3. **Testing Strategy**:
   - [ ] Unit tests for path calculation
   - [ ] Integration tests for directory preservation
   - [ ] Cross-platform tests (Unix and Windows paths)
   - [ ] Edge case tests (symlinks, .., absolute paths)

### For Implementation Phase

1. **Code Changes** (in order):
   - [ ] Add CLI flags to main.cpp
   - [ ] Add sourceRoot + preserveStructure to FileOutputManager
   - [ ] Implement calculateOutputPath() with relative path logic
   - [ ] Add directory creation to writeFile()
   - [ ] Wire up in CppToCConsumer
   - [ ] Update TranspilerAPI if needed

2. **Testing**:
   - [ ] Add MultiFileTranspilationTest cases for structure preservation
   - [ ] Test with real-world directory structures
   - [ ] Verify backward compatibility (default behavior unchanged)

3. **Documentation**:
   - [ ] Update README with new flags
   - [ ] Add examples of directory-based transpilation
   - [ ] Document structure preservation behavior

---

## Sources

### TypeScript Research
- [TypeScript: TSConfig Option: rootDir](https://www.typescriptlang.org/tsconfig/rootDir.html)
- [TypeScript: TSConfig Option: outDir](https://www.typescriptlang.org/tsconfig/outDir.html)
- [Progress on TypeScript 7 - December 2025](https://devblogs.microsoft.com/typescript/progress-on-typescript-7-december-2025/)

### Babel Research
- [Output directory structure is not preserved in first compilation](https://github.com/babel/babel/issues/7849)
- [Using Babel.js · NodeJS Tutorials](https://xpepermint.gitbooks.io/nodejs-cheatsheet/content/using_babel.html)
- [BabelJS - Quick Guide](https://www.tutorialspoint.com/babeljs/babeljs_quick_guide.htm)

### Code Analysis
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/FileOutputManager.cpp` - Current path handling implementation
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/FileOutputManager.h` - FileOutputManager API
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCConsumer.cpp` - Consumer integration
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/main.cpp` - CLI argument parsing
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/MultiFileTranspilationTest.cpp` - Current test expectations
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/TranspilerAPI.cpp` - Library API
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/TranspilerAPI.h` - API interface

### C++ Project Structure Research
- [How to Organize a C++ Project: Directory Structure and Best Practices](https://www.studyplan.dev/cmake/organizing-a-cpp-project)
- [Best Practices for Structuring C++ Projects (Industry Standards)](https://medium.com/@gtech.govind2000/best-practices-for-structuring-c-projects-industry-standards-71b82f6b145c)
- [Canonical Project Structure](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2018/p1204r0.html)

### Real-World Examples
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/json-parser/` - Example with src/ and tests/ subdirectories
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/logger/` - Example with tests/ subdirectory
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/resource-manager/` - Example project structure


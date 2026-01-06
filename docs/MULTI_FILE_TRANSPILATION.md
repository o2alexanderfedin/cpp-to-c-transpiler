# Multi-File Transpilation Guide

**Version:** 1.0
**Last Updated:** December 2025
**Status:** Complete

Complete guide for transpiling multiple C++ files with the cpptoc transpiler.

---

## Table of Contents

1. [Overview](#overview)
2. [Basic Usage](#basic-usage)
3. [Automatic File Discovery](#automatic-file-discovery)
4. [Output File Naming](#output-file-naming)
5. [Output Directory Management](#output-directory-management)
6. [Cross-File Dependencies](#cross-file-dependencies)
7. [Include Path Configuration](#include-path-configuration)
8. [Build Integration](#build-integration)
9. [Best Practices](#best-practices)
10. [Troubleshooting](#troubleshooting)
11. [Examples](#examples)

---

## Overview

The cpptoc transpiler operates **exclusively in project-based mode**, automatically discovering and transpiling all C++ source files in a directory tree. The `--source-dir` option is **REQUIRED** for all transpilation operations.

### Key Features

- **Project-Based Transpilation**: Automatically discovers all `.cpp`/`.cxx`/`.cc` files in a directory tree
- **Required Source Directory**: `--source-dir` must be specified for all operations
- **Independent Transpilation**: Each file gets its own AST and translation
- **Automatic Separation**: Each input generates both header and implementation
- **Directory Structure Preservation**: Output mirrors source directory structure
- **Smart Exclusions**: Automatically skips build directories and version control
- **Include Path Support**: Use `-I` flags for header dependencies
- **Compilation Database**: Integration with CMake and other build systems

### Architecture

```
Source Directory              Auto-Discovery & Transpilation      Output Directory
────────────────              ──────────────────────────────      ────────────────
src/
  core/
    Engine.cpp    ──┐
    Logger.cpp    ──┼──→  Discover Files  ──→  Parse AST  ──→  build/
  ui/                │                                            core/
    Window.cpp    ──┘                                              Engine.h + Engine.c
                                                                   Logger.h + Logger.c
                                                                 ui/
                                                                   Window.h + Window.c
```

All files are discovered automatically with directory structure preserved.

---

## Basic Usage

### Command-Line Syntax

```bash
cpptoc --source-dir <directory> --output-dir <directory> -- [clang-options]
```

**Note:** `--source-dir` is **REQUIRED**. Individual file arguments are silently ignored.

### Project Transpilation

```bash
# Transpile entire project (REQUIRED usage)
./build/cpptoc --source-dir src/ --output-dir build/

# Auto-discovers all .cpp/.cxx/.cc files recursively
# Output: Preserves directory structure in build/
```

### With Include Paths

```bash
# Add header search directories
./build/cpptoc --source-dir src/ --output-dir build/ -- -I./include -I./third_party

# Enables: #include <myheader.h> from ./include or ./third_party
```

### With Clang Options

```bash
# Pass standard Clang options after --
./build/cpptoc --source-dir src/ --output-dir build/ -- -std=c++20 -I./include
```

---

## Automatic File Discovery

cpptoc operates **exclusively in auto-discovery mode**. You must always specify `--source-dir`, and the transpiler automatically finds all C++ source files in the directory tree.

### Overview

When you run cpptoc with `--source-dir`, it:

1. Recursively scans the specified directory
2. Collects all files with C++ source extensions (`.cpp`, `.cxx`, `.cc`)
3. Excludes common build artifacts and version control directories
4. Transpiles all discovered files while preserving directory structure

### Project Transpilation

```bash
# Transpile entire project (REQUIRED usage)
./build/cpptoc --source-dir src/ --output-dir build/

# Output:
# Auto-discovering C++ source files in: src/
# Discovered 12 file(s) for transpilation
# [Transpilation proceeds...]
```

**Note:** Individual file arguments on the command line are silently ignored - the transpiler always uses auto-discovery.

### How It Works

**Discovery Process:**
```
src/
├── core/
│   ├── Engine.cpp        ✓ Discovered
│   ├── Logger.cpp        ✓ Discovered
│   └── Utils.cxx         ✓ Discovered (.cxx extension)
├── ui/
│   ├── Window.cpp        ✓ Discovered
│   └── Button.cc         ✓ Discovered (.cc extension)
├── build/
│   └── generated.cpp     ✗ Excluded (build directory)
├── .git/
│   └── hooks.cpp         ✗ Excluded (hidden directory)
└── tests/
    └── test.cpp          ✓ Discovered
```

**Resulting Output:**
```
build/
├── core/
│   ├── Engine.h, Engine.c
│   ├── Logger.h, Logger.c
│   └── Utils.h, Utils.c
├── ui/
│   ├── Window.h, Window.c
│   └── Button.h, Button.c
└── tests/
    └── test.h, test.c
```

### Supported Extensions

Auto-discovery recognizes these C++ source file extensions:

- `.cpp` - Standard C++ source extension
- `.cxx` - Alternative C++ extension (common in older projects)
- `.cc` - Alternative C++ extension (common in Google-style projects)

**Note:** Header files (`.h`, `.hpp`, `.hxx`) are **not** discovered as they are inputs, not transpilation targets.

### Excluded Directories

The following directory patterns are **automatically excluded** from discovery:

| Pattern | Description | Examples |
|---------|-------------|----------|
| `.git`, `.svn`, `.hg` | Version control | `.git/hooks.cpp` |
| `build*` | Build directories | `build/`, `build-debug/`, `build-release/` |
| `cmake-build-*` | CMake build dirs | `cmake-build-debug/`, `cmake-build-release/` |
| `node_modules` | Node.js dependencies | `node_modules/package/index.cpp` |
| `vendor` | Third-party code | `vendor/library/lib.cpp` |
| `.*` (hidden dirs) | Hidden directories | `.cache/`, `.vscode/`, `.idea/` |

**Rationale:** These directories typically contain:
- Generated/compiled code (not source)
- Third-party dependencies (shouldn't be transpiled)
- Version control metadata (not code)

### Advantages

1. **No Build Script Updates**: Adding new `.cpp` files doesn't require updating transpiler invocations
2. **Handles Nested Structures**: Automatically traverses subdirectories
3. **Clean Commands**: Simple, consistent command-line invocations
4. **Less Error-Prone**: Eliminates manual file enumeration errors
5. **Build System Friendly**: Integrates naturally with CMake, Make, etc.
6. **Project-Level Consistency**: Always transpiles entire project, never partial

### Empty Directory Handling

If no C++ source files are found, cpptoc exits with a warning:

```bash
$ ./build/cpptoc --source-dir empty_dir/ --output-dir build/

Auto-discovering C++ source files in: empty_dir/
Warning: No C++ source files (.cpp, .cxx, .cc) found in empty_dir/
```

**Exit Code:** 1 (non-fatal error)

**This is treated as an error** to prevent accidental transpilation of the wrong directory.

### Usage Examples

**Example 1: Simple Project**
```bash
# Project structure:
# src/
#   main.cpp
#   utils.cpp
#   math.cpp

./build/cpptoc --source-dir src/ --output-dir build/

# Discovers 3 files, generates:
# build/main.h, build/main.c
# build/utils.h, build/utils.c
# build/math.h, build/math.c
```

**Example 2: Multi-Module Project**
```bash
# Project structure:
# src/
#   engine/
#     core.cpp
#     physics.cpp
#   graphics/
#     renderer.cpp
#     shader.cpp

./build/cpptoc --source-dir src/ --output-dir build/

# Discovers 4 files, preserves structure:
# build/engine/core.h, build/engine/core.c
# build/engine/physics.h, build/engine/physics.c
# build/graphics/renderer.h, build/graphics/renderer.c
# build/graphics/shader.h, build/graphics/shader.c
```

**Example 3: Mixed Extensions**
```bash
# Project structure:
# src/
#   modern.cpp      (C++ source)
#   legacy.cxx      (C++ source, old style)
#   google_style.cc (C++ source, Google convention)
#   header.h        (Header - not discovered)

./build/cpptoc --source-dir src/ --output-dir build/

# Discovers 3 files (all C++ sources, ignores .h):
# build/modern.h, build/modern.c
# build/legacy.h, build/legacy.c
# build/google_style.h, build/google_style.c
```

**Example 4: Large Project with Exclusions**
```bash
# Project structure:
# project/
#   src/          ✓ Transpiled
#   tests/        ✓ Transpiled
#   build/        ✗ Excluded
#   .git/         ✗ Excluded
#   node_modules/ ✗ Excluded

./build/cpptoc --source-dir project/ --output-dir output/

# Only discovers files from src/ and tests/
```

### Best Practices

**✅ DO:**
- Organize source files in a dedicated `src/` or `source/` directory
- Keep build artifacts separate (e.g., `build/`, `bin/`)
- Use consistent file extensions (prefer `.cpp`)
- Always specify `--source-dir` pointing to project root

**❌ DON'T:**
- Mix source files with build outputs in the same directory
- Place `.cpp` files in version control directories (`.git/`, `.svn/`)
- Point `--source-dir` at directories with third-party code you don't want transpiled

### Integration with Build Systems

**CMake Example:**
```cmake
# CMakeLists.txt
add_custom_target(transpile_all
    COMMAND cpptoc --source-dir ${CMAKE_SOURCE_DIR}/src
                   --output-dir ${CMAKE_BINARY_DIR}/transpiled
    COMMENT "Auto-transpiling all C++ files"
)
```

**Makefile Example:**
```makefile
# Makefile
.PHONY: transpile
transpile:
\t./build/cpptoc --source-dir src/ --output-dir build/transpiled/
```

**Bash Script Example:**
```bash
#!/bin/bash
# scripts/transpile-all.sh

SOURCE_DIR="src"
OUTPUT_DIR="build/transpiled"

echo "Transpiling all files in ${SOURCE_DIR}..."
./build/cpptoc --source-dir "${SOURCE_DIR}" --output-dir "${OUTPUT_DIR}"

if [ $? -eq 0 ]; then
    echo "Transpilation completed successfully!"
else
    echo "Transpilation failed!"
    exit 1
fi
```

---

## Output File Naming

### Naming Convention

The transpiler preserves the base name of each input file and generates two outputs:

```
Input Filename       →   Header File      Implementation File
────────────────         ───────────      ───────────────────
Point.cpp            →   Point.h          Point.c
Circle.cpp           →   Circle.h         Circle.c
MyClass.cpp          →   MyClass.h        MyClass.c
my_class.cpp         →   my_class.h       my_class.c
test-file.cpp        →   test-file.h      test-file.c
```

### Base Name Extraction

- Extension `.cpp`, `.cc`, `.cxx`, `.C` is removed
- Remaining name becomes the base
- `.h` and `.c` extensions are added

### Header File Contents

```c
#ifndef POINT_H
#define POINT_H

// Forward declarations (if needed)
struct Circle;

// Struct/class definitions
struct Point {
    int x;
    int y;
};

// Function declarations
int distance(struct Point* p1, struct Point* p2);
void print_point(struct Point* p);

#endif // POINT_H
```

### Implementation File Contents

```c
#include "Point.h"

// Function implementations
int distance(struct Point* p1, struct Point* p2) {
    int dx = p1->x - p2->x;
    int dy = p1->y - p2->y;
    return dx * dx + dy * dy;
}

void print_point(struct Point* p) {
    printf("Point(%d, %d)\n", p->x, p->y);
}
```

---

## Output Directory Management

### Default Behavior

Without `--output-dir`, files are generated in the current working directory:

```bash
$ pwd
/home/user/project

$ ./build/cpptoc src/Point.cpp --
# Creates: /home/user/project/Point.h
#          /home/user/project/Point.c
```

### Relative Paths

```bash
# Relative to current directory
./build/cpptoc Point.cpp --output-dir ./build/generated

# Directory structure:
# ./build/generated/Point.h
# ./build/generated/Point.c
```

### Absolute Paths

```bash
# Absolute path
./build/cpptoc Point.cpp --output-dir /tmp/transpiled

# Directory structure:
# /tmp/transpiled/Point.h
# /tmp/transpiled/Point.c
```

### Automatic Directory Creation

The transpiler automatically creates the output directory if it doesn't exist:

```bash
# Creates ./new_output if missing
./build/cpptoc Point.cpp --output-dir ./new_output

# No need for: mkdir -p ./new_output
```

### Multiple Files, One Directory

All generated files from multiple inputs go to the same output directory:

```bash
./build/cpptoc Point.cpp Circle.cpp --output-dir ./output

# Directory structure:
# ./output/
#   ├── Point.h
#   ├── Point.c
#   ├── Circle.h
#   └── Circle.c
```

### Directory Structure Preservation

The transpiler **automatically preserves the source directory structure** in the output directory.

#### Why Structure Preservation?

1. **Prevents Name Collisions**: Files with the same name in different source directories won't overwrite each other
2. **Maintains Project Organization**: Logical grouping of related files is preserved
3. **Build System Compatibility**: Many build systems expect mirrored directory structures
4. **Familiar Layout**: Generated code mirrors your source code organization

#### Structure Preservation in Action

```bash
# Transpile entire project with structure preservation
./build/cpptoc --source-dir src/ --output-dir build/

# Discovers all files and preserves structure:
# src/math/Vector.cpp → build/math/Vector.h, build/math/Vector.c
# src/utils/helpers.cpp → build/utils/helpers.h, build/utils/helpers.c
```

#### Nested Directory Structures

The transpiler preserves arbitrarily deep directory nesting:

```bash
# Deeply nested source files
./build/cpptoc --source-dir src/ --output-dir build/

# Discovers: src/math/algebra/linear/Vector.cpp
# Output preserves full nesting: build/math/algebra/linear/Vector.h, build/math/algebra/linear/Vector.c
```

#### Files at Source Root

Files directly in the source root appear directly in the output root:

```bash
# Source root contains main.cpp
./build/cpptoc --source-dir src/ --output-dir build/

# Discovers: src/main.cpp
# Output at output root: build/main.h, build/main.c
```

#### Name Collision Resolution

Structure preservation automatically resolves name collisions:

```bash
# Two files named Vector.cpp in different directories
./build/cpptoc --source-dir src/ --output-dir build/

# Discovers:
#   src/frontend/Vector.cpp
#   src/backend/Vector.cpp
#
# No collision - structure preserved:
#   build/frontend/Vector.h, build/frontend/Vector.c
#   build/backend/Vector.h, build/backend/Vector.c
```

#### Real-World Example

Transpiling an entire project while preserving structure:

```bash
# Project structure:
# src/
#   core/
#     Engine.cpp
#     Config.cpp
#   math/
#     Vector.cpp
#     Matrix.cpp
#   ui/
#     Window.cpp
#     Button.cpp

# Transpile entire project (auto-discovers all files)
./build/cpptoc --source-dir src/ --output-dir build/transpiled/

# Output (mirrors source structure):
# build/transpiled/
#   core/
#     Engine.h, Engine.c
#     Config.h, Config.c
#   math/
#     Vector.h, Vector.c
#     Matrix.h, Matrix.c
#   ui/
#     Window.h, Window.c
#     Button.h, Button.c
```

---

## Cross-File Dependencies

### Independent Processing

Each discovered file is transpiled independently with its own AST:

- **No shared state** between files during transpilation
- **No automatic dependency analysis** across files
- **Each file must be self-contained** or use `#include` for dependencies

### Using Functions from Other Files

If `utils.cpp` uses functions from `math.cpp` (both discovered automatically):

**math.cpp** (Input):
```cpp
int add(int a, int b) {
    return a + b;
}
```

**utils.cpp** (Input):
```cpp
// Declare function from math module
extern int add(int a, int b);

int addTen(int x) {
    return add(x, 10);
}
```

After transpilation:

**math.h** (Generated):
```c
#ifndef MATH_H
#define MATH_H

int add(int a, int b);

#endif
```

**utils.c** (Generated):
```c
#include "utils.h"

// User can manually add:
// #include "math.h"

int addTen(int x) {
    return add(x, 10);
}
```

### Struct Dependencies

If one file uses a struct from another, use forward declarations or `#include`:

**Point.h** (Generated):
```c
struct Point {
    int x, y;
};
```

**Circle.cpp** (Input):
```cpp
// Include the header where Point is defined
#include "Point.h"

struct Circle {
    Point center;
    double radius;
};
```

**Circle.h** (Generated):
```c
#ifndef CIRCLE_H
#define CIRCLE_H

#include "Point.h"

struct Circle {
    struct Point center;
    double radius;
};

#endif
```

### Compilation Order

When compiling generated C files, no special order is needed (C compiler handles includes):

```bash
# Any order works
gcc Point.c Circle.c Rectangle.c -o program

# Or
gcc Circle.c Point.c Rectangle.c -o program
```

---

## Include Path Configuration

### Purpose

Include paths (`-I` flags) tell Clang where to find header files during transpilation.

### Command-Line Syntax

```bash
# After the -- separator, add -I flags
cpptoc --source-dir src/ -- -I/path/to/headers
```

### Single Include Directory

```bash
./build/cpptoc --source-dir src/ -- -I./include

# Enables:
# #include <myheader.h>  → searches in ./include/myheader.h
```

### Multiple Include Directories

```bash
./build/cpptoc --source-dir src/ -- -I./include -I./third_party -I/usr/local/include

# Search order:
# 1. ./include/
# 2. ./third_party/
# 3. /usr/local/include/
# 4. System paths
```

### Relative vs Absolute Paths

```bash
# Relative to current directory
./build/cpptoc --source-dir src/ -- -I./include

# Absolute path
./build/cpptoc --source-dir src/ -- -I/usr/local/include

# Multiple (mixed)
./build/cpptoc --source-dir src/ -- -I./local -I/usr/include
```

### Include Syntax in C++ Code

```cpp
// Angle brackets: searches in -I directories
#include <myheader.h>

// Quotes: searches current directory first, then -I directories
#include "localheader.h"
```

### Example: Multi-File Project with Includes

**Project Structure:**
```
project/
├── include/
│   └── common.h
├── src/
│   ├── main.cpp
│   └── utils.cpp
└── build/
```

**common.h:**
```cpp
#define VERSION 100
int helper(int x);
```

**utils.cpp:**
```cpp
#include <common.h>

int helper(int x) {
    return x * VERSION;
}
```

**main.cpp:**
```cpp
#include <common.h>

int main() {
    return helper(42);
}
```

**Transpilation:**
```bash
./build/cpptoc --source-dir src/ \
    --output-dir ./build/generated \
    -- -I./include

# Auto-discovers src/main.cpp and src/utils.cpp
# Output:
# ./build/generated/main.h
# ./build/generated/main.c
# ./build/generated/utils.h
# ./build/generated/utils.c
```

---

## Build Integration

### CMake Integration

**Generate compile_commands.json:**
```cmake
# CMakeLists.txt
cmake_minimum_required(VERSION 3.20)
project(MyProject CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_executable(myapp
    src/main.cpp
    src/utils.cpp
)

target_include_directories(myapp PRIVATE include)
```

**Build and use:**
```bash
cmake -B build
./build/cpptoc --source-dir src/ -- -p ./build
```

### Makefile Integration

**Makefile:**
```makefile
CXX = g++
CPPTOC = ./build/cpptoc
INCLUDES = -I./include
SOURCE_DIR = src
OUTPUT_DIR = ./generated

all: transpile program

transpile:
	$(CPPTOC) --source-dir $(SOURCE_DIR) --output-dir $(OUTPUT_DIR) -- $(INCLUDES)

program: transpile
	$(CXX) $(OUTPUT_DIR)/*.c -o $@

clean:
	rm -rf $(OUTPUT_DIR) program

.PHONY: transpile all clean
```

### Compilation Database Usage

```bash
# Use existing compilation database
./build/cpptoc --source-dir src/ -- -p ./build

# Transpiler reads:
# ./build/compile_commands.json
```

---

## Best Practices

### 1. Organize Source Files

```
project/
├── include/          # Header files
├── src/              # Source files
│   ├── math.cpp
│   ├── utils.cpp
│   └── main.cpp
└── generated/        # Transpiled output
    ├── math.h
    ├── math.c
    ├── utils.h
    ├── utils.c
    ├── main.h
    └── main.c
```

### 2. Use Output Directory

Always specify `--output-dir` to separate generated files from source:

```bash
# Good
./build/cpptoc --source-dir src/ --output-dir ./generated

# Avoid
./build/cpptoc --source-dir src/ --  # May pollute current directory
```

### 3. Consistent Include Paths

Specify all necessary `-I` flags in one command:

```bash
# Good: all include paths specified
./build/cpptoc --source-dir src/ -- -I./include -I./third_party

# Avoid: missing paths might cause errors
./build/cpptoc --source-dir src/ --  # No include paths
```

### 4. One Module Per File

Design each `.cpp` as a self-contained module:

- **Good**: `math.cpp` contains all math functions
- **Avoid**: Splitting a single class across multiple files

### 5. Use Forward Declarations

Minimize header dependencies with forward declarations:

```cpp
// circle.h
struct Point;  // Forward declaration

struct Circle {
    Point* center;  // Pointer allows forward decl
    double radius;
};
```

### 6. Include Generated Headers

Manually include generated headers when needed:

```c
// utils.c (after transpilation)
#include "utils.h"
#include "math.h"  // If utils depends on math
```

### 7. Verify Output

Always check generated files before compiling:

```bash
# Transpile
./build/cpptoc src/*.cpp --output-dir ./gen

# Inspect
ls -la ./gen/
cat ./gen/main.c
```

---

## Troubleshooting

### Issue: Header Not Found

**Error:**
```
fatal error: 'myheader.h' file not found
#include <myheader.h>
         ^~~~~~~~~~~~
```

**Solution:**
```bash
# Add include directory
./build/cpptoc --source-dir src/ -- -I./path/to/headers
```

### Issue: Files Generated in Wrong Location

**Problem:** Output files appear in unexpected directory

**Solution:**
```bash
# Specify absolute path
./build/cpptoc --source-dir src/ --output-dir /absolute/path/to/output

# Or verify relative path is correct
pwd  # Check current directory
./build/cpptoc --source-dir src/ --output-dir ./relative/path
```

### Issue: No Files Discovered

**Problem:** Transpiler reports "No C++ source files found"

**Solution:**
```bash
# Verify --source-dir points to correct directory
ls src/  # Should see .cpp/.cxx/.cc files

# Check for excluded directories
./build/cpptoc --source-dir src/ --output-dir build/
```

### Issue: Duplicate Struct Definitions

**Problem:** Same struct defined in multiple generated headers

**Cause:** Each file has independent AST; no cross-file deduplication

**Solution:** Extract shared structs to a common header:

```cpp
// common.h (manually created)
#ifndef COMMON_H
#define COMMON_H

struct Point {
    int x, y;
};

#endif
```

```cpp
// circle.cpp
#include "common.h"  // Use shared Point definition
```

### Issue: Cross-File Function Dependencies

**Problem:** Function defined in `math.cpp` used in `utils.cpp`, but transpiler doesn't know about it

**Solution:** Use `extern` declarations or include generated headers:

```cpp
// utils.cpp
extern int add(int, int);  // Declare function from math.cpp

int addTen(int x) {
    return add(x, 10);
}
```

After transpilation, include the header:

```c
// utils.c (manually edit)
#include "utils.h"
#include "math.h"  // Now has declaration for add()
```

### Issue: Compilation Order Matters

**Problem:** C compiler complains about undefined symbols

**Cause:** Header not included

**Solution:**
```bash
# Ensure all .c files include their .h files
gcc -c math.c     # Includes math.h
gcc -c utils.c    # Includes utils.h and math.h
gcc math.o utils.o -o program
```

### Issue: Include Path Not Resolved

**Problem:** Include path specified but still not found

**Debugging:**
```bash
# Verify path exists
ls -la ./include

# Use absolute path to test
./build/cpptoc main.cpp -- -I$(pwd)/include

# Check for typos
./build/cpptoc main.cpp -- -I./inclde  # Wrong
./build/cpptoc main.cpp -- -I./include # Correct
```

---

## Examples

### Example 1: Simple Multi-Module Project

**Structure:**
```
src/
  math.cpp
  utils.cpp
  main.cpp
```

**Command:**
```bash
./build/cpptoc --source-dir src/ --output-dir ./generated

# Auto-discovers all files
# Output:
# ./generated/math.h
# ./generated/math.c
# ./generated/utils.h
# ./generated/utils.c
# ./generated/main.h
# ./generated/main.c
```

### Example 2: Project with Shared Headers

**Structure:**
```
include/common.h
src/
  module1.cpp
  module2.cpp
```

**Command:**
```bash
./build/cpptoc --source-dir src/ \
    --output-dir ./build/gen \
    -- -I./include

# Both modules can #include <common.h>
```

### Example 3: Multiple Include Directories

**Structure:**
```
include/mylib/
third_party/external/
src/
  main.cpp
```

**Command:**
```bash
./build/cpptoc --source-dir src/ \
    --output-dir ./build \
    -- -I./include -I./third_party/external -std=c++20
```

### Example 4: With Compilation Database

**Setup:**
```bash
# Generate compilation database
cmake -B build -DCMAKE_EXPORT_COMPILE_COMMANDS=ON
```

**Command:**
```bash
# Transpile using compilation database
./build/cpptoc --source-dir src/ -- -p ./build
```

### Example 5: Real-World Logger Library

**Structure:**
```
logger/
├── include/
│   └── logger.h
├── src/
│   ├── logger.cpp
│   └── file_logger.cpp
└── tests/
    └── test_logger.cpp
```

**Command:**
```bash
./build/cpptoc \
    --source-dir logger/src/ \
    --output-dir ./logger/generated \
    -- -I./logger/include -std=c++17

# Compile generated C code
gcc -c logger/generated/logger.c -I./logger/generated
gcc -c logger/generated/file_logger.c -I./logger/generated
gcc logger.o file_logger.o -o liblogger.a
```

### Example 6: Nested Project Structure

**Structure:**
```
project/
  src/
    core/
      engine.cpp
    utils/
      helper.cpp
```

**Command:**
```bash
# Auto-discovers all files, preserves structure
./build/cpptoc --source-dir project/src/ --output-dir build/ -- -I./include

# Output:
# build/core/engine.h, build/core/engine.c
# build/utils/helper.h, build/utils/helper.c
```

---

## Summary

Project-based transpilation with cpptoc is straightforward:

1. **Specify source directory** with `--source-dir` (REQUIRED)
2. **Specify output directory** with `--output-dir`
3. **Add include paths** with `-I` flags after `--` (if needed)
4. **Auto-discovery** finds all `.cpp`/`.cxx`/`.cc` files recursively
5. **Directory structure** is automatically preserved in output
6. **Check generated files** before compiling
7. **Compile C files** with standard C compiler

The transpiler automatically discovers all files and handles each independently, generating clean header/implementation pairs that integrate seamlessly with C build systems.

---

## See Also

- [CLI Options Reference](api-reference/cli-options.md)
- [Build Integration Guide](CI_CD_GUIDE.md)
- [Header/Implementation Separation](README.md#header-implementation-separation-phase-28-01)
- [Virtual File System Support](README.md#virtual-file-system-support-phase-27-01)

---

*Generated with [Claude Code](https://claude.com/claude-code) | December 2025*

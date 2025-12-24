# Multi-File Transpilation Guide

**Version:** 1.0
**Last Updated:** December 2025
**Status:** Complete

Complete guide for transpiling multiple C++ files with the cpptoc transpiler.

---

## Table of Contents

1. [Overview](#overview)
2. [Basic Usage](#basic-usage)
3. [Output File Naming](#output-file-naming)
4. [Output Directory Management](#output-directory-management)
5. [Cross-File Dependencies](#cross-file-dependencies)
6. [Include Path Configuration](#include-path-configuration)
7. [Build Integration](#build-integration)
8. [Best Practices](#best-practices)
9. [Troubleshooting](#troubleshooting)
10. [Examples](#examples)

---

## Overview

The cpptoc transpiler supports processing multiple C++ source files in a single invocation. Each file is transpiled independently, generating separate `.h` and `.c` files with automatic header/implementation separation.

### Key Features

- **Multiple Input Files**: Process any number of `.cpp` files in one command
- **Independent Transpilation**: Each file gets its own AST and translation
- **Automatic Separation**: Each input generates both header and implementation
- **Output Directory Control**: Place generated files in custom locations
- **Include Path Support**: Use `-I` flags for header dependencies
- **Compilation Database**: Integration with CMake and other build systems

### Architecture

```
Input Files                  Transpilation Process              Output Files
───────────                  ─────────────────────              ────────────
Point.cpp      ──┐
                 ├──→  Parse AST  ──→  Translate  ──→  Point.h + Point.c
Circle.cpp     ──┤
                 ├──→  Parse AST  ──→  Translate  ──→  Circle.h + Circle.c
Rectangle.cpp  ──┘
                 └──→  Parse AST  ──→  Translate  ──→  Rectangle.h + Rectangle.c
```

Each file is processed independently with its own Clang AST.

---

## Basic Usage

### Command-Line Syntax

```bash
cpptoc [options] <file1.cpp> [file2.cpp ...] -- [clang-options]
```

### Single File (Baseline)

```bash
# Transpile one file
./build/cpptoc Point.cpp --

# Output: Point.h + Point.c (in current directory)
```

### Multiple Files

```bash
# Transpile multiple files
./build/cpptoc Point.cpp Circle.cpp Rectangle.cpp --

# Output:
#   Point.h + Point.c
#   Circle.h + Circle.c
#   Rectangle.h + Rectangle.c
```

### With Output Directory

```bash
# Place generated files in specific directory
./build/cpptoc Point.cpp Circle.cpp --output-dir ./generated

# Output:
#   ./generated/Point.h + ./generated/Point.c
#   ./generated/Circle.h + ./generated/Circle.c
```

### With Include Paths

```bash
# Add header search directories
./build/cpptoc main.cpp utils.cpp -- -I./include -I./third_party

# Enables: #include <myheader.h> from ./include or ./third_party
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

---

## Cross-File Dependencies

### Independent Processing

Each file is transpiled independently with its own AST:

- **No shared state** between files during transpilation
- **No automatic dependency analysis** across files
- **Each file must be self-contained** or use `#include` for dependencies

### Using Functions from Other Files

If `utils.cpp` uses functions from `math.cpp`:

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
cpptoc main.cpp -- -I/path/to/headers
```

### Single Include Directory

```bash
./build/cpptoc main.cpp -- -I./include

# Enables:
# #include <myheader.h>  → searches in ./include/myheader.h
```

### Multiple Include Directories

```bash
./build/cpptoc main.cpp -- -I./include -I./third_party -I/usr/local/include

# Search order:
# 1. ./include/
# 2. ./third_party/
# 3. /usr/local/include/
# 4. System paths
```

### Relative vs Absolute Paths

```bash
# Relative to current directory
./build/cpptoc main.cpp -- -I./include

# Absolute path
./build/cpptoc main.cpp -- -I/usr/local/include

# Multiple (mixed)
./build/cpptoc main.cpp -- -I./local -I/usr/include
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
./build/cpptoc src/main.cpp src/utils.cpp \
    --output-dir ./build/generated \
    -- -I./include

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
./build/cpptoc src/main.cpp src/utils.cpp -- -p ./build
```

### Makefile Integration

**Makefile:**
```makefile
CXX = g++
CPPTOC = ./build/cpptoc
INCLUDES = -I./include
OUTPUT_DIR = ./generated

SOURCES = src/main.cpp src/utils.cpp
GENERATED_C = $(patsubst src/%.cpp,$(OUTPUT_DIR)/%.c,$(SOURCES))

all: program

$(OUTPUT_DIR)/%.c: src/%.cpp
	$(CPPTOC) $< --output-dir $(OUTPUT_DIR) -- $(INCLUDES)

program: $(GENERATED_C)
	$(CXX) $(GENERATED_C) -o $@

clean:
	rm -rf $(OUTPUT_DIR) program
```

### Compilation Database Usage

```bash
# Use existing compilation database
./build/cpptoc src/main.cpp -- -p ./build

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
./build/cpptoc src/*.cpp --output-dir ./generated

# Avoid
./build/cpptoc src/*.cpp --  # Pollutes current directory
```

### 3. Consistent Include Paths

Use the same `-I` flags across all files:

```bash
# Good: consistent paths
./build/cpptoc file1.cpp file2.cpp -- -I./include -I./third_party

# Avoid: missing paths might cause errors
./build/cpptoc file1.cpp -- -I./include
./build/cpptoc file2.cpp --  # Missing -I./include
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
./build/cpptoc main.cpp -- -I./path/to/headers
```

### Issue: Files Generated in Wrong Location

**Problem:** Output files appear in unexpected directory

**Solution:**
```bash
# Specify absolute path
./build/cpptoc main.cpp --output-dir /absolute/path/to/output

# Or verify relative path is correct
pwd  # Check current directory
./build/cpptoc main.cpp --output-dir ./relative/path
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

**Files:**
```
src/math.cpp
src/utils.cpp
src/main.cpp
```

**Command:**
```bash
./build/cpptoc src/math.cpp src/utils.cpp src/main.cpp \
    --output-dir ./generated \
    --

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
src/module1.cpp
src/module2.cpp
```

**Command:**
```bash
./build/cpptoc src/module1.cpp src/module2.cpp \
    --output-dir ./build/gen \
    -- -I./include

# Both modules can #include <common.h>
```

### Example 3: Multiple Include Directories

**Structure:**
```
include/mylib/
third_party/external/
src/main.cpp
```

**Command:**
```bash
./build/cpptoc src/main.cpp \
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
./build/cpptoc src/main.cpp src/utils.cpp -- -p ./build
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
    logger/src/logger.cpp \
    logger/src/file_logger.cpp \
    --output-dir ./logger/generated \
    -- -I./logger/include -std=c++17

# Compile generated C code
gcc -c logger/generated/logger.c -I./logger/generated
gcc -c logger/generated/file_logger.c -I./logger/generated
gcc logger.o file_logger.o -o liblogger.a
```

### Example 6: Wildcard Input Files

**Command:**
```bash
# Transpile all .cpp files in directory
./build/cpptoc src/*.cpp \
    --output-dir ./generated \
    -- -I./include

# Be careful with shell expansion
echo src/*.cpp  # Verify files before running
```

### Example 7: Incremental Transpilation

**Script (Makefile pattern):**
```bash
# Transpile only changed files
for file in src/*.cpp; do
    base=$(basename "$file" .cpp)
    if [ "$file" -nt "generated/$base.c" ]; then
        ./build/cpptoc "$file" \
            --output-dir ./generated \
            -- -I./include
    fi
done
```

---

## Summary

Multi-file transpilation with cpptoc is straightforward:

1. **List all input files** on command line
2. **Specify output directory** with `--output-dir`
3. **Add include paths** with `-I` flags after `--`
4. **Check generated files** before compiling
5. **Compile C files** with standard C compiler

The transpiler handles each file independently, generating clean header/implementation pairs that integrate seamlessly with C build systems.

---

## See Also

- [CLI Options Reference](api-reference/cli-options.md)
- [Build Integration Guide](CI_CD_GUIDE.md)
- [Header/Implementation Separation](README.md#header-implementation-separation-phase-28-01)
- [Virtual File System Support](README.md#virtual-file-system-support-phase-27-01)

---

*Generated with [Claude Code](https://claude.com/claude-code) | December 2025*

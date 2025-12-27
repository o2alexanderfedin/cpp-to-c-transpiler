# Command-Line Interface Reference

**Version:** 1.5.1
**Last Updated:** December 2025

Complete reference for cpptoc command-line options and flags.

---

## Table of Contents

1. [Basic Usage](#basic-usage)
2. [Common Options](#common-options)
3. [Runtime Configuration](#runtime-configuration)
4. [Output Control](#output-control)
5. [Build Integration Options](#build-integration-options)
6. [Debugging and Diagnostics](#debugging-and-diagnostics)
7. [Advanced Options](#advanced-options)
8. [Clang-Specific Options](#clang-specific-options)
9. [Examples](#examples)

---

## Basic Usage

### Syntax

```bash
cpptoc [options] <source-files> -- [clang-options]
```

### Minimal Example

```bash
# Transpile a single file
cpptoc input.cpp --

# Transpile multiple files
cpptoc file1.cpp file2.cpp file3.cpp --

# With output directory
cpptoc input.cpp -- -o output.c
```

### The Double Dash (`--`)

The `--` separator is **required** and separates cpptoc options from Clang compiler options:

```bash
cpptoc [cpptoc-options] source.cpp -- [clang-options]
       ├─────────────┘              └──────────────┘
       cpptoc flags                 Clang flags
```

---

## Common Options

### Help and Version

```bash
# Display help message
cpptoc --help
cpptoc -h

# Show version information
cpptoc --version
cpptoc -v
```

**Output Example:**
```
cpptoc version 1.5.1
C++ to C Transpiler using Clang LibTooling
LLVM version: 18.1.0
Built: December 2025

Usage: cpptoc [options] <source-files> -- [clang-options]

Options:
  --help                Display this help message
  --version             Show version information
  --runtime-mode=MODE   Runtime mode: inline or library (default: inline)
  --runtime=FEATURES    Enable runtime features: exceptions,rtti,coroutines,vinherit,all,none
  ...
```

### Output Control

```bash
# Specify output file
cpptoc input.cpp -- -o output.c

# Specify output directory
cpptoc input.cpp -- -output-dir=generated/

# Generate alongside source (input.cpp -> input.c)
cpptoc input.cpp -- -output-same-dir
```

---

## Runtime Configuration

### Runtime Mode Selection

```bash
# Inline mode (default) - embed runtime in each file
cpptoc --runtime-mode=inline input.cpp --

# Library mode - link against runtime library
cpptoc --runtime-mode=library input.cpp --
```

**When to Use:**
- **Inline**: Small projects (< 20 files), embedded systems, safety certification
- **Library**: Large projects (20+ files), faster compilation, smaller binaries

### Runtime Feature Flags

```bash
# Enable specific features
cpptoc --runtime=exceptions input.cpp --          # Exceptions only
cpptoc --runtime=rtti input.cpp --                # RTTI only
cpptoc --runtime=exceptions,rtti input.cpp --     # Multiple features

# All features (default)
cpptoc --runtime=all input.cpp --

# No runtime features
cpptoc --runtime=none input.cpp --
```

**Available Features:**
- `exceptions`: Exception handling (try/catch/throw)
- `rtti`: Runtime type information (dynamic_cast, typeid)
- `coroutines`: C++20 coroutines support
- `vinherit`: Virtual inheritance
- `all`: All features enabled (default)
- `none`: Disable all runtime features

**Feature Sizes:**
| Feature | Size (Inline) | Use Case |
|---------|--------------|----------|
| `exceptions` | 800-1200 bytes | Error handling |
| `rtti` | 600-1000 bytes | Type introspection |
| `coroutines` | 400-800 bytes | Async programming |
| `vinherit` | 500-900 bytes | Diamond inheritance |
| `all` | 2300-3900 bytes | Full C++ support |
| `none` | 0 bytes | Pure C code |

### Disable Specific Features

```bash
# Disable RTTI
cpptoc --no-rtti input.cpp --

# Disable exceptions
cpptoc --no-exceptions input.cpp --

# Disable coroutines
cpptoc --no-coroutines input.cpp --

# Combine with enabled features
cpptoc --runtime=all --no-coroutines input.cpp --
# Enables exceptions, RTTI, vinherit but NOT coroutines
```

---

## Output Control

### Output Format

```bash
# C99 output (default)
cpptoc --std=c99 input.cpp --

# C11 output
cpptoc --std=c11 input.cpp --

# Generate header files
cpptoc --generate-headers input.cpp --

# Generate both .c and .h files
cpptoc --separate-headers input.cpp --
```

### Code Style Options

```bash
# Indentation style
cpptoc --indent=spaces input.cpp --    # Use spaces (default)
cpptoc --indent=tabs input.cpp --      # Use tabs

# Indentation width
cpptoc --indent-width=4 input.cpp --   # 4 spaces (default)
cpptoc --indent-width=2 input.cpp --   # 2 spaces

# Line directives
cpptoc --line-directives input.cpp --      # Include #line directives (default)
cpptoc --no-line-directives input.cpp --   # Omit #line directives
```

### Include Runtime Library

```bash
# Generate runtime library source
cpptoc --generate-runtime -o cpptoc_runtime.c cpptoc_runtime.h

# Specify runtime library location
cpptoc --runtime-lib=/path/to/cpptoc_runtime.h input.cpp --
```

---

## Build Integration Options

### CMake Integration

```bash
# Generate CMakeLists.txt for generated code
cpptoc --generate-cmake input.cpp --

# Specify CMake project name
cpptoc --cmake-project=MyProject input.cpp --
```

**Generated `CMakeLists.txt` Example:**
```cmake
cmake_minimum_required(VERSION 3.20)
project(MyProject C)

# Link runtime library (if library mode)
find_library(CPPTOC_RUNTIME cpptoc_runtime)

add_executable(myapp
    generated_input.c
)

target_link_libraries(myapp PRIVATE ${CPPTOC_RUNTIME})
```

### Makefile Generation

```bash
# Generate Makefile
cpptoc --generate-makefile input.cpp --

# Specify compiler
cpptoc --makefile-cc=gcc input.cpp --
cpptoc --makefile-cc=clang input.cpp --
```

---

## Debugging and Diagnostics

### Verbose Output

```bash
# Verbose mode
cpptoc --verbose input.cpp --
cpptoc -v input.cpp --

# Extra verbose (debug)
cpptoc -vv input.cpp --

# Show AST
cpptoc --dump-ast input.cpp --

# Show generated IR
cpptoc --dump-ir input.cpp --
```

### Warnings and Errors

```bash
# Treat warnings as errors
cpptoc --Werror input.cpp --

# Disable warnings
cpptoc --no-warnings input.cpp --
cpptoc -w input.cpp --

# Specific warning control
cpptoc --Wno-unused-variable input.cpp --
```

### Diagnostic Output

```bash
# Print diagnostic information
cpptoc --print-stats input.cpp --

# Show translation progress
cpptoc --progress input.cpp --

# Dry run (parse only, no output)
cpptoc --dry-run input.cpp --
```

---

## Advanced Options

### Optimization Hints

```bash
# Optimize for size
cpptoc --optimize-size input.cpp --

# Optimize for speed
cpptoc --optimize-speed input.cpp --

# Enable inlining hints
cpptoc --enable-inlining input.cpp --

# Disable vtable optimization
cpptoc --no-vtable-optimization input.cpp --
```

### Name Mangling

```bash
# Name mangling style
cpptoc --mangle=itanium input.cpp --    # Itanium ABI (default)
cpptoc --mangle=simple input.cpp --     # Simple mangling (Class_method_type)

# Mangling prefix
cpptoc --mangle-prefix=my_ input.cpp -- # Prefix: my_Class_method

# No mangling (may cause conflicts)
cpptoc --no-mangle input.cpp --
```

### Memory Management

```bash
# Use custom allocator
cpptoc --allocator=malloc input.cpp --       # malloc/free (default)
cpptoc --allocator=custom input.cpp --       # User-provided allocator

# Stack allocation for small objects
cpptoc --stack-alloc-threshold=256 input.cpp --
```

---

## Clang-Specific Options

Options after `--` are passed directly to Clang:

### Include Paths

```bash
# Add include directory
cpptoc input.cpp -- -I/usr/local/include

# System include directory
cpptoc input.cpp -- -isystem /usr/include/mylib

# Multiple includes
cpptoc input.cpp -- -I./include -I./third_party
```

### Preprocessor Definitions

```bash
# Define macro
cpptoc input.cpp -- -DDEBUG

# Define with value
cpptoc input.cpp -- -DVERSION=1.0

# Undefine macro
cpptoc input.cpp -- -UDEBUG
```

### C++ Standard

```bash
# C++17 (default)
cpptoc input.cpp -- -std=c++17

# C++20
cpptoc input.cpp -- -std=c++20

# C++14
cpptoc input.cpp -- -std=c++14
```

### Compilation Database

```bash
# Use compilation database
cpptoc input.cpp -- -p build/

# Specify compile_commands.json
cpptoc input.cpp -- -p=/path/to/compile_commands.json
```

---

## Examples

### Example 1: Basic Transpilation

```bash
# Simplest usage
cpptoc hello.cpp --
```

### Example 2: Library Mode with Exceptions

```bash
# Library mode, exceptions only
cpptoc --runtime-mode=library \
       --runtime=exceptions \
       input.cpp -- \
       -o output.c
```

### Example 3: Multiple Files with Custom Include

```bash
# Transpile multiple files with include path
cpptoc file1.cpp file2.cpp file3.cpp -- \
       -I./include \
       -I./third_party \
       -std=c++20

# Each file generates separate .h and .c files:
# file1.h + file1.c
# file2.h + file2.c
# file3.h + file3.c
```

### Example 3a: Multiple Files with Output Directory

```bash
# Transpile multiple files to specific directory
cpptoc Point.cpp Circle.cpp Rectangle.cpp \
       --output-dir ./generated \
       --

# Output structure:
# ./generated/Point.h
# ./generated/Point.c
# ./generated/Circle.h
# ./generated/Circle.c
# ./generated/Rectangle.h
# ./generated/Rectangle.c
```

### Example 3b: Multi-Module Project

```bash
# Transpile complete multi-module project
cpptoc src/math.cpp src/utils.cpp src/main.cpp \
       --output-dir ./build/generated \
       -- -I./include -I./third_party -std=c++20

# Then compile the generated C code
gcc -c build/generated/math.c -I./build/generated
gcc -c build/generated/utils.c -I./build/generated
gcc -c build/generated/main.c -I./build/generated
gcc math.o utils.o main.o -o program
```

### Example 4: Safety-Critical Inline Mode

```bash
# Inline mode, exceptions only, with line directives
cpptoc --runtime-mode=inline \
       --runtime=exceptions \
       --line-directives \
       safety_critical.cpp -- \
       -o safety_critical.c
```

### Example 5: Full Feature Set with Optimization

```bash
# All features, library mode, optimized
cpptoc --runtime-mode=library \
       --runtime=all \
       --optimize-size \
       --generate-cmake \
       application.cpp -- \
       -std=c++20 \
       -I./include \
       -o application.c
```

### Example 6: Template-Heavy Code with STL

```bash
# STL and templates (self-bootstrapping)
cpptoc --runtime-mode=library \
       --runtime=exceptions,rtti \
       templates.cpp -- \
       -std=c++20 \
       -I/usr/include/c++/11 \
       -o templates.c
```

### Example 7: Generate Runtime Library

```bash
# Generate runtime library source
cpptoc --generate-runtime \
       --runtime=exceptions,rtti,coroutines \
       -o cpptoc_runtime.c cpptoc_runtime.h

# Then use it
cpptoc --runtime-mode=library \
       --runtime-lib=./cpptoc_runtime.h \
       input.cpp -- -o input.c
```

### Example 8: Dry Run for Testing

```bash
# Parse and validate without generating output
cpptoc --dry-run \
       --verbose \
       --print-stats \
       input.cpp --
```

---

## Option Reference Table

### cpptoc Options

| Option | Short | Argument | Default | Description |
|--------|-------|----------|---------|-------------|
| `--help` | `-h` | None | - | Display help message |
| `--version` | `-v` | None | - | Show version |
| `--runtime-mode` | - | `inline\|library` | `inline` | Runtime mode |
| `--runtime` | - | Feature list | `all` | Enable features |
| `--no-rtti` | - | None | - | Disable RTTI |
| `--no-exceptions` | - | None | - | Disable exceptions |
| `--no-coroutines` | - | None | - | Disable coroutines |
| `--std` | - | `c99\|c11` | `c99` | C standard |
| `--generate-headers` | - | None | - | Generate .h files |
| `--separate-headers` | - | None | - | Separate .c/.h |
| `--indent` | - | `spaces\|tabs` | `spaces` | Indentation |
| `--indent-width` | - | Number | `4` | Indent size |
| `--line-directives` | - | None | On | #line directives |
| `--verbose` | `-v` | None | - | Verbose output |
| `--dump-ast` | - | None | - | Show AST |
| `--dry-run` | - | None | - | Parse only |
| `--optimize-size` | - | None | - | Size optimization |
| `--mangle` | - | Style | `itanium` | Name mangling |

### Clang Options (After `--`)

| Option | Argument | Description |
|--------|----------|-------------|
| `-I` | Directory | Include path |
| `-D` | Macro | Define macro |
| `-std` | Standard | C++ standard (c++17, c++20) |
| `-o` | File | Output file |
| `-p` | Path | Compilation database |

---

## Environment Variables

### CPPTOC_RUNTIME_PATH

Path to runtime library headers:

```bash
export CPPTOC_RUNTIME_PATH=/usr/local/include/cpptoc
cpptoc input.cpp --
```

### CPPTOC_DEFAULT_MODE

Default runtime mode:

```bash
export CPPTOC_DEFAULT_MODE=library
cpptoc input.cpp --  # Uses library mode
```

### LLVM_DIR

LLVM installation directory (for building cpptoc):

```bash
export LLVM_DIR=/opt/llvm-18
cmake -B build
```

---

## Exit Codes

| Code | Meaning |
|------|---------|
| `0` | Success |
| `1` | Parse error |
| `2` | Code generation error |
| `3` | File I/O error |
| `4` | Invalid arguments |
| `5` | Clang error |

---

## Next Steps

- **Configuration Files**: See [configuration.md](configuration.md)
- **Build Integration**: See [build-integration.md](build-integration.md)
- **Troubleshooting**: See [../troubleshooting/common-issues.md](../troubleshooting/common-issues.md)

---

*Generated with [Claude Code](https://claude.com/claude-code) | December 2025*

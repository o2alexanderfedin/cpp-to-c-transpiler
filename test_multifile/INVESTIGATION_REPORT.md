# cpptoc Multiple Input Files Investigation Report

## Executive Summary

**Does it work?** **Partially** - cpptoc accepts multiple files and processes them sequentially, but **crashes when processing files with cross-file dependencies** (i.e., when one file includes a header that defines a class).

**Key Finding:** The tool works correctly for multiple **independent** files but fails with a segmentation fault (exit code 139) when processing files that reference types defined in other files.

## Current Architecture

### File Processing Flow

1. **main.cpp** (lines 207-212):
   - Uses Clang's `CommonOptionsParser` to parse command-line arguments
   - Creates `ClangTool` with source file list from `getSourcePathList()`
   - Calls `Tool.run()` which processes files **sequentially**

2. **CppToCFrontendAction** (per-file):
   - Creates a new `CppToCConsumer` for each input file
   - Each file gets its own AST context

3. **CppToCConsumer** (per-file):
   - Processes one translation unit at a time
   - Outputs results to stdout (no file output currently implemented)
   - **State is NOT shared between files**

### Output Handling

- **Current Implementation:** All output goes to stdout
- **FileOutputManager:** Exists but is not currently used by the main pipeline
- **Real-world usage:** The `transpiler-api-cli` tool processes files **one at a time** (see `scripts/transpile-real-world.sh` line 178)

## Test Results

### Test 1: Single Standalone File
```bash
cpptoc Point.cpp -- -std=c++17
```
**Result:** ✅ SUCCESS (exit code 0, 129 lines of output)

### Test 2: Two Independent Files
```bash
cpptoc Point.cpp Circle.cpp -- -std=c++17
```
**Result:** ✅ SUCCESS (exit code 0)
- Processes Point.cpp completely
- Processes Circle.cpp completely
- Both files have no cross-file dependencies

### Test 3: Two Files with Dependencies
```bash
cpptoc Point.cpp Rectangle.cpp -- -std=c++17
```
**Result:** ❌ CRASH (exit code 139 - segmentation fault)
- Successfully processes Point.cpp (108 lines of output)
- Starts processing Rectangle.cpp
- **Crashes immediately** when processing Rectangle.cpp
- Rectangle.cpp includes "Point.h" and uses the Point class

### Test 4: Single File with External Dependency
```bash
cpptoc Rectangle.cpp -- -std=c++17 -I.
```
**Result:** ❌ CRASH (exit code 139 - segmentation fault)
- Crashes immediately with no output
- Rectangle.h includes Point.h (external class definition)
- The crash happens before any translation output

## Root Cause Analysis

### The Problem

When processing a file that **includes** another file (e.g., Rectangle.cpp includes Point.h):
1. Clang parses the included header and adds Point class to the AST
2. CppToCVisitor encounters the Point class definition from the header
3. **The translator attempts to process the Point class again**
4. This causes a crash, likely due to:
   - Attempting to translate the same class multiple times with fresh state
   - Missing type information for referenced types
   - State corruption from processing header-defined classes

### Why Independent Files Work

Point.cpp and Circle.cpp each define their own complete, self-contained classes with no external dependencies. Each file can be processed in complete isolation.

### Why Dependent Files Fail

Rectangle.cpp depends on Point.h:
- Rectangle.h includes Point.h (declares dependency on Point class)
- Rectangle.cpp includes Rectangle.h
- When Clang parses Rectangle.cpp, it sees Point class definition from Point.h
- The translator sees this "foreign" class definition and crashes

## Current Design Limitations

1. **No Cross-File Type Registry:** Each file is processed independently with no shared type information
2. **No Header/Implementation Separation:** The tool doesn't distinguish between:
   - Classes defined in the current .cpp file (should be translated)
   - Classes defined in included headers (should be referenced, not translated)
3. **No Output File Management:** All output goes to stdout, making multi-file projects impractical
4. **No Compilation Database Support:** While ClangTool supports it, there's no guidance on using it

## Test Files Created

Location: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/test_multifile/`

- **Point.h / Point.cpp** - Simple class with getters/setters (works standalone)
- **Circle.cpp** - Self-contained class (works standalone)
- **Rectangle.h / Rectangle.cpp** - Depends on Point class (crashes)
- **main.cpp** - Uses both Point and Rectangle (not tested with cpptoc)

## Comparison with Clang

Clang handles multiple files by:
1. Processing each file as a separate translation unit
2. Using a compilation database to specify include paths and dependencies
3. Generating one object file (.o) per source file
4. Letting the linker resolve cross-file references

cpptoc currently mimics step 1 and 2, but lacks:
- Mechanism to handle forward declarations and external type references
- Output file management (one .c/.h pair per input .cpp)
- Cross-translation-unit type registry

## Recommendations

### What Needs to be Fixed

1. **Header Detection Logic**
   - Add logic to detect if a class definition comes from:
     - The main source file being processed → **translate it**
     - An included header → **reference it only**
   - Use Clang's SourceManager to check if declaration is in main file

2. **Output File Management**
   - Implement FileOutputManager integration
   - Generate one .c/.h pair per input .cpp file
   - Add command-line options for output directory

3. **Type Registry / Cross-File Context**
   - Maintain a shared registry of translated types across files
   - Track which types have been translated vs. which are external references
   - Generate appropriate `#include` directives in output

4. **Better Error Handling**
   - Catch segmentation faults and provide meaningful error messages
   - Validate that referenced types are available before translation

### Immediate Workaround

For now, users must:
1. Process files **one at a time** (like `transpiler-api-cli` does)
2. Ensure each file is self-contained OR
3. Manually provide all type definitions needed

## Usage Documentation

### Current Working Usage

```bash
# Single file
cpptoc MyClass.cpp -- -std=c++17

# Multiple independent files (no cross-references)
cpptoc File1.cpp File2.cpp -- -std=c++17

# Redirect output
cpptoc MyClass.cpp -- -std=c++17 > output.c
```

### What Doesn't Work

```bash
# Files with dependencies - CRASHES
cpptoc Point.cpp Rectangle.cpp -- -std=c++17

# Single file with external type dependencies - CRASHES  
cpptoc Rectangle.cpp -- -std=c++17 -I.
```

## Related Files

- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/main.cpp` - Entry point, ClangTool setup
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCFrontendAction.cpp` - Creates ASTConsumer per file
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCConsumer.cpp` - Handles translation unit
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/FileOutputManager.h` - File output (not integrated)
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/scripts/transpile-real-world.sh` - Processes files one-by-one

## Conclusion

cpptoc **does support multiple input files** at the command-line level (similar to Clang), but the implementation is **incomplete and buggy**:

- ✅ Accepts multiple files on command line
- ✅ Processes them sequentially via ClangTool
- ✅ Works for independent files
- ❌ Crashes on files with cross-file type dependencies
- ❌ No output file management (everything to stdout)
- ❌ No mechanism to handle external type references

**Priority Fix:** Add source location checking to skip translating classes from included headers (only translate classes defined in the main .cpp file being processed).

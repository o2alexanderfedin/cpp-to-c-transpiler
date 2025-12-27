# Warning Reference

**Version**: 3.0.0-rc
**Date**: 2025-12-27
**Status**: CURRENT

---

## Overview

This document catalogs all warning and error messages emitted by the C++ to C transpiler. Each warning includes an explanation, cause, solution, and example to help you understand and resolve issues during transpilation.

**Philosophy**: Warnings are actionable guidance, not noise. Each warning indicates a potential issue that may require attention or a known limitation of the transpiler.

---

## Warning Severity Levels

- **ERROR**: Transpilation cannot proceed; requires immediate fix
- **WARNING**: Transpilation proceeds but output may be incorrect or incomplete
- **INFO**: Informational message about transpilation decisions

---

## Warning Catalog

### W001: Unsupported STL Container

**Severity**: ERROR
**Message**: `Unsupported STL container: std::vector`

**Cause**: The transpiler does not yet support STL containers (std::string, std::vector, std::map, etc.) in v3.0.0.

**Solution**:
1. Refactor code to use C-style arrays or custom containers
2. See `docs/TRANSPILABLE_CPP.md` for workarounds
3. Wait for v4.0.0 release (Q2-Q3 2026) which will include STL support

**Example**:
```cpp
// ❌ NOT SUPPORTED (triggers warning)
std::vector<int> numbers;
numbers.push_back(42);

// ✅ WORKAROUND: Use custom container
class DynamicArray {
    int* data_;
    size_t size_;
    // ...
};
```

**Related**:
- `docs/CPP23_LIMITATIONS.md` (STL Limitations section)
- `docs/TRANSPILABLE_CPP.md` (Workarounds section)

---

### W002: No C++ Source Files Found

**Severity**: WARNING
**Message**: `Warning: No C++ source files (.cpp, .cxx, .cc) found in <directory>`

**Cause**: The `--source-dir` argument points to a directory with no C++ source files, or the files have non-standard extensions.

**Solution**:
1. Verify the directory path is correct
2. Ensure C++ files use standard extensions: `.cpp`, `.cxx`, or `.cc`
3. Use `--` to pass individual files if directory is not applicable

**Example**:
```bash
# ❌ Wrong directory
./transpiler --source-dir /path/to/empty/dir

# ✅ Correct usage
./transpiler --source-dir /path/to/src
# or
./transpiler -- file1.cpp file2.cpp
```

**Related**: CLI option `--source-dir`

---

### W003: [[assume]] Condition Extraction Failed

**Severity**: WARNING
**Message**: `Warning: Could not extract condition from [[assume]] attribute`

**Cause**: The `[[assume]]` attribute's condition expression is too complex or malformed for the transpiler to analyze.

**Solution**:
1. Simplify the assumption condition
2. Use explicit conditions (e.g., `ptr != nullptr` instead of `ptr`)
3. Check for typos or syntax errors in the assumption

**Example**:
```cpp
// ⚠️ May trigger warning if condition is complex
[[assume(ptr && ptr->value > 0 && ptr->next != nullptr)]];

// ✅ Better: Simple, clear condition
[[assume(ptr != nullptr)]];
[[assume(ptr->value > 0)]];
```

**Related**: `docs/CPP23_LIMITATIONS.md` ([[assume]] attribute section)

---

### W004: [[assume]] Condition Has Side Effects

**Severity**: WARNING
**Message**: `Warning: [[assume]] condition has side effects, transpilation may not preserve semantics`

**Cause**: The `[[assume]]` attribute condition contains expressions with side effects (function calls, assignments, etc.). C `__builtin_assume()` may not preserve these semantics.

**Solution**:
1. Remove side effects from assumption conditions
2. Extract side-effect operations before the `[[assume]]` statement
3. Use assertions instead if side effects are intentional

**Example**:
```cpp
// ❌ Side effect in condition
[[assume(++counter > 0)]];

// ✅ Extract side effect first
++counter;
[[assume(counter > 0)]];

// ✅ Or use assertion if side effect is required
assert(++counter > 0);
```

**Related**: C++23 [[assume]] attribute semantics

---

### W005: Failed to Create __builtin_assume() Call

**Severity**: WARNING
**Message**: `Warning: Failed to create __builtin_assume() call, assumption discarded`

**Cause**: The transpiler could not generate a C `__builtin_assume()` call due to internal AST construction issues.

**Solution**:
1. Report this as a bug (unexpected internal error)
2. Verify Clang version compatibility (requires Clang 17+)
3. Try simplifying the assumption condition

**Example**:
```cpp
// If this triggers W005, it's likely a transpiler bug
[[assume(x > 0)]];
```

**Related**: File a bug report with minimal reproduction case

---

### W006: operator&& Loses Short-Circuit Evaluation

**Severity**: WARNING
**Message**: `WARNING: operator&& loses short-circuit evaluation`

**Cause**: When translating operator&& to a C function call, short-circuit evaluation (early exit) semantics may be lost. The C version evaluates both operands before calling the function.

**Solution**:
1. Accept the semantic difference (rare impact in practice)
2. Refactor to use built-in && operator instead of overloaded version
3. Document this behavior in your codebase

**Example**:
```cpp
// C++ (short-circuits)
class Bool {
    bool operator&&(const Bool& other) const;
};
Bool a, b;
if (a && b) { /* b not evaluated if a is false */ }

// C translation (both evaluated)
// Bool_and(&a, &b) evaluates both a and b
```

**Related**: Phase 51 (Comparison Operators) documentation

---

### W007: operator|| Loses Short-Circuit Evaluation

**Severity**: WARNING
**Message**: `WARNING: operator|| loses short-circuit evaluation`

**Cause**: Similar to W006, operator|| translation to a C function call loses short-circuit semantics.

**Solution**:
1. Accept the semantic difference
2. Refactor to use built-in || operator
3. Document this behavior

**Example**:
```cpp
// C++ (short-circuits)
class Bool {
    bool operator||(const Bool& other) const;
};
Bool a, b;
if (a || b) { /* b not evaluated if a is true */ }

// C translation (both evaluated)
// Bool_or(&a, &b) evaluates both a and b
```

**Related**: Phase 51 (Comparison Operators) documentation

---

### W008: C Function Not Found for Comparison Operator

**Severity**: WARNING
**Message**: `Warning: C function not found for comparison operator call`

**Cause**: The transpiler expected to find a generated C function for an overloaded comparison operator but couldn't locate it in the symbol table.

**Solution**:
1. Ensure the operator is defined in a transpiled class
2. Check for name mangling issues
3. Verify operator signature matches expected pattern

**Example**:
```cpp
// Operator should be defined
class Point {
    bool operator==(const Point& other) const;
};

// If warning occurs, check:
// - Is operator== declared and defined?
// - Is the class fully transpiled?
```

**Related**: Operator overloading (Phase 51)

---

### W009: C Function Not Found for Unary Logical Operator

**Severity**: WARNING
**Message**: `Warning: C function not found for unary logical operator call`

**Cause**: Similar to W008, but for unary operators (!, etc.).

**Solution**:
1. Ensure unary operator is defined in class
2. Check operator signature matches pattern
3. Verify symbol table has correct entry

**Example**:
```cpp
class Bool {
    bool operator!() const;
};

// Ensure operator! is properly defined
```

**Related**: Operator overloading (Phase 51)

---

### W010: No C AST Nodes Generated

**Severity**: WARNING
**Message**: `Warning: No C AST nodes generated. Input file may contain no transpilable declarations, or all declarations were filtered out.`

**Cause**: The transpiler processed the C++ file but generated no C AST output. Possible reasons:
- File contains only declarations not supported by the transpiler
- All declarations were filtered out (e.g., from system headers)
- File is empty or contains only comments/preprocessing directives

**Solution**:
1. Check if the input file contains transpilable C++ code
2. Verify declarations are not all from system headers (which are skipped)
3. Review FileOriginTracker configuration

**Example**:
```cpp
// File with only system includes → triggers warning
#include <iostream>  // Skipped (system header)

// Add transpilable code
class MyClass {  // This will generate C AST
    int x;
};
```

**Related**: Multi-file transpilation (Phase 34)

---

### W011: Failed to Write Output Files

**Severity**: ERROR
**Message**: `Error: Failed to write output files`

**Cause**: File I/O error when writing generated C code to disk. Possible reasons:
- Insufficient permissions
- Disk full
- Invalid output path
- File locked by another process

**Solution**:
1. Check write permissions on output directory
2. Verify sufficient disk space
3. Ensure output path is valid
4. Close any programs that may have the output files open

**Example**:
```bash
# Check permissions
ls -la /output/dir

# Ensure directory exists
mkdir -p /output/dir

# Run transpiler
./transpiler --source-dir src --output-dir /output/dir
```

**Related**: CLI option `--output-dir`

---

### W012: Skipping Orphaned Top-Level VarDecl

**Severity**: INFO
**Message**: `[Bug #35] Skipping orphaned top-level VarDecl: <variable name>`

**Cause**: The transpiler encountered a global variable declaration that couldn't be properly categorized for output (header vs implementation file).

**Solution**:
This is usually informational and not an error. The variable may be:
1. A static variable (kept in implementation file)
2. An extern variable (declared in header)
3. A system library variable (skipped)

If this variable should be transpiled, report as a bug.

**Example**:
```cpp
// May trigger info message
extern int globalVar;  // Extern declaration

static int fileLocalVar;  // File-local variable
```

**Related**: Multi-file transpilation, global variables

---

### W013: if consteval Warning

**Severity**: WARNING
**Message**: `Warning: if consteval runtime branch only (compile-time branch omitted)`

**Cause**: The transpiler translates `if consteval` by emitting only the runtime branch, omitting the compile-time branch.

**Solution**:
1. Accept this limitation (v3.0.0 behavior)
2. Refactor code to avoid relying on compile-time branch
3. Wait for Phase 58 full implementation (v3.1+)

**Example**:
```cpp
int compute(int x) {
    if consteval {
        return x * 2;  // ⚠️ NOT emitted in C
    } else {
        return x + x;  // ✅ Emitted in C
    }
}

// C output: only runtime branch
```

**Related**: `docs/CPP23_LIMITATIONS.md` (if consteval section)

---

### W014: Source Directory Does Not Exist

**Severity**: ERROR
**Message**: `Error: Source directory does not exist: <path>`

**Cause**: The `--source-dir` argument points to a non-existent directory.

**Solution**:
1. Verify the path is correct
2. Check for typos
3. Ensure the directory exists before running the transpiler

**Example**:
```bash
# ❌ Wrong path
./transpiler --source-dir /nonexistent/path

# ✅ Verify first
ls /path/to/src
./transpiler --source-dir /path/to/src
```

**Related**: CLI option `--source-dir`

---

### W015: Not a Directory

**Severity**: ERROR
**Message**: `Error: Not a directory: <path>`

**Cause**: The `--source-dir` argument points to a file instead of a directory.

**Solution**:
1. Use `--` to pass individual files instead
2. Point `--source-dir` to the containing directory

**Example**:
```bash
# ❌ Pointing to a file
./transpiler --source-dir /path/to/file.cpp

# ✅ Point to directory
./transpiler --source-dir /path/to/src

# ✅ Or pass file directly
./transpiler -- /path/to/file.cpp
```

**Related**: CLI option `--source-dir`

---

### W016: ACSL Level Requires --generate-acsl

**Severity**: ERROR
**Message**: `Error: --acsl-level requires --generate-acsl to be enabled`

**Cause**: The `--acsl-level` option was used without enabling ACSL generation via `--generate-acsl`.

**Solution**:
Add `--generate-acsl` flag when using `--acsl-level`.

**Example**:
```bash
# ❌ Missing --generate-acsl
./transpiler --acsl-level 2 -- file.cpp

# ✅ Enable ACSL generation first
./transpiler --generate-acsl --acsl-level 2 -- file.cpp
```

**Related**: ACSL annotation features (Phase 1-7)

---

### W017: ACSL Output Requires --generate-acsl

**Severity**: ERROR
**Message**: `Error: --acsl-output requires --generate-acsl to be enabled`

**Cause**: The `--acsl-output` option was used without enabling ACSL generation.

**Solution**:
Add `--generate-acsl` flag when using `--acsl-output`.

**Example**:
```bash
# ❌ Missing --generate-acsl
./transpiler --acsl-output annotations.txt -- file.cpp

# ✅ Enable ACSL generation first
./transpiler --generate-acsl --acsl-output annotations.txt -- file.cpp
```

**Related**: ACSL annotation features

---

### W018: --source-dir Required for Project Transpilation

**Severity**: ERROR
**Message**: `Error: --source-dir is required for project-based transpilation`

**Cause**: Attempting multi-file transpilation without specifying the source directory.

**Solution**:
Provide `--source-dir` argument pointing to the project's source code directory.

**Example**:
```bash
# ❌ Missing --source-dir
./transpiler

# ✅ Specify source directory
./transpiler --source-dir /path/to/project/src
```

**Related**: Multi-file transpilation (Phase 34)

---

### W019: Segfault Caught

**Severity**: CRITICAL
**Message**: `!!! SEGFAULT CAUGHT (signal <sig>) !!!`

**Cause**: The transpiler crashed due to a segmentation fault. This is a critical internal error.

**Solution**:
1. **Report this as a bug immediately** with:
   - Input file(s) that caused the crash
   - Command-line arguments used
   - Backtrace information (printed by the transpiler)
2. Try reducing the input file to a minimal reproduction case
3. Check for known issues in the issue tracker

**Example**:
```
!!! SEGFAULT CAUGHT (signal 11) !!!
Last operation before crash:
Backtrace:
  [frames listed here]
!!! CRITICAL: Exiting due to segfault !!!
```

**Related**: File a critical bug report with reproduction steps

---

## Warning Suppression

### Command-Line Flags

**Suppress all warnings** (not recommended):
```bash
./transpiler --no-warnings -- file.cpp
```

**Verbose output** (show all info messages):
```bash
./transpiler --verbose -- file.cpp
```

**Redirect warnings to file**:
```bash
./transpiler -- file.cpp 2> warnings.txt
```

### Programmatic Suppression

Currently, the transpiler does not support per-warning suppression. All warnings are enabled by default.

**Future enhancement** (v3.1+): Per-warning control with `-Wno-<warning-id>` flags.

---

## Common Warning Patterns

### STL-Related Warnings

**Pattern**: Multiple W001 warnings for std::string, std::vector, std::map

**Diagnosis**: Your codebase uses STL containers heavily

**Solution**:
1. Wait for v4.0.0 (STL support)
2. Refactor to custom containers (see `docs/TRANSPILABLE_CPP.md`)

**Example**:
```cpp
// Triggers multiple W001
std::vector<std::string> names;
std::map<int, std::string> idToName;

// Refactor to custom containers
DynamicArray<String> names;
HashMap<int, String> idToName;
```

---

### Operator Overloading Warnings

**Pattern**: W006, W007 (short-circuit warnings)

**Diagnosis**: You're overloading operator&& or operator||

**Solution**:
1. Accept semantic difference (usually safe)
2. Document this behavior
3. Avoid complex logic in overloaded boolean operators

**Example**:
```cpp
// Acceptable: simple boolean wrapper
class Bool {
    bool value_;
    bool operator&&(const Bool& other) const {
        return value_ && other.value_;
    }
};

// Risky: complex logic with side effects
class Bool {
    bool operator&&(const Bool& other) const {
        logEvaluation();  // Side effect
        return complexCheck() && other.complexCheck();
    }
};
```

---

### ACSL Configuration Warnings

**Pattern**: W016, W017 (missing --generate-acsl)

**Diagnosis**: ACSL options specified without enabling ACSL generation

**Solution**: Add `--generate-acsl` flag

**Example**:
```bash
# ❌ Multiple configuration errors
./transpiler --acsl-level 2 --acsl-output out.txt -- file.cpp

# ✅ Enable ACSL generation
./transpiler --generate-acsl --acsl-level 2 --acsl-output out.txt -- file.cpp
```

---

## Debugging Tips

### Enabling Debug Output

**See parsed files**:
```bash
./transpiler --verbose --source-dir src
# Look for: "Parsed file: <filename>"
```

**See generated C AST nodes**:
```bash
./transpiler --verbose --source-dir src
# Look for: "C TranslationUnit has N declarations"
```

**See generated files**:
```bash
./transpiler --source-dir src
# Look for: "Generated files: <header>, <impl>"
```

### Common Debugging Steps

1. **Start with verbose output**: `--verbose` flag
2. **Isolate the issue**: Reduce input to minimal reproduction case
3. **Check CLI arguments**: Ensure all required flags are present
4. **Verify input files**: Ensure C++ code is valid and transpilable
5. **Check output directory**: Ensure write permissions and sufficient space
6. **Review warnings**: Each warning is actionable guidance

### Reporting Bugs

When reporting a warning as a potential bug:

1. **Provide minimal reproduction case** (smallest C++ file that triggers warning)
2. **Include full command-line** (all arguments used)
3. **Include full warning message** (copy-paste exact text)
4. **Include transpiler version**: `./transpiler --version`
5. **Include Clang version**: `clang --version`
6. **Describe expected behavior** vs actual behavior

---

## Summary

**Total Warnings**: 19 documented
**Severity Breakdown**:
- CRITICAL: 1 (segfault)
- ERROR: 6 (CLI argument errors, file I/O)
- WARNING: 10 (semantic limitations, operator overloading)
- INFO: 2 (debugging information)

**Most Common Warnings**:
1. W001: Unsupported STL Container (STL usage)
2. W006/W007: Short-circuit evaluation loss (operator overloading)
3. W016/W017: ACSL configuration errors (CLI usage)
4. W014/W015: Source directory errors (CLI usage)

**Key Takeaways**:
- All warnings are actionable (provide solution)
- Most warnings indicate known limitations (STL, Clang version)
- Some warnings are informational (debug output)
- Critical warnings (segfaults) should be reported immediately

---

## Resources

- [CPP23_LIMITATIONS.md](CPP23_LIMITATIONS.md) - Known limitations and workarounds
- [TRANSPILABLE_CPP.md](TRANSPILABLE_CPP.md) - Supported C++ subset
- [MIGRATION_GUIDE.md](MIGRATION_GUIDE.md) - Practical transpilation guide
- [docs/api-reference/cli-options.md](api-reference/cli-options.md) - CLI flags reference
- [CHANGELOG.md](CHANGELOG.md) - Version history and bug fixes

---

**Generated**: 2025-12-27
**Version**: v3.0.0-rc
**Status**: CURRENT

**All warnings cataloged from codebase grep analysis**

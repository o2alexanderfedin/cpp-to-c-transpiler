# Multi-File cpptoc Test Suite

This directory contains test files to investigate cpptoc's support for multiple input files.

## Test Files

### Standalone Classes (No Dependencies)
- **Point.h / Point.cpp** - Simple Point class with x, y coordinates
- **Circle.cpp** - Self-contained Circle class with radius

### Files with Dependencies
- **Rectangle.h / Rectangle.cpp** - Rectangle class that depends on Point class
- **main.cpp** - Main program using both Point and Rectangle

## Test Results Summary

| Test | Command | Result | Exit Code |
|------|---------|--------|-----------|
| Single file | `cpptoc Point.cpp -- -std=c++17` | ✅ Success | 0 |
| Two independent | `cpptoc Point.cpp Circle.cpp -- -std=c++17` | ✅ Success | 0 |
| Two with deps | `cpptoc Point.cpp Rectangle.cpp -- -std=c++17` | ❌ Crash | 139 |
| Single with deps | `cpptoc Rectangle.cpp -- -std=c++17 -I.` | ❌ Crash | 139 |

## Output Files

- `Point_output.txt` - Successful transpilation of Point.cpp (4.7KB)
- `Circle_output.txt` - Successful transpilation of Circle.cpp (2.9KB)
- `PointCircle_output.txt` - Successful transpilation of both independent files (7.8KB)
- `Multi_output.txt` - Partial output before crash with Rectangle.cpp (4.2KB)
- `Rectangle_solo.txt` - Empty (crashed immediately)

## Key Findings

1. **Works:** Multiple files with no cross-file dependencies
2. **Crashes:** Any file that includes a header defining a class
3. **Root Cause:** No distinction between classes defined in current file vs. included headers
4. **Workaround:** Process files one at a time (like `transpiler-api-cli` does)

See `INVESTIGATION_REPORT.md` for full analysis.

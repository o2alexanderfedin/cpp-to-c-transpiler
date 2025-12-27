# Phase 33.3 A/B Testing Framework

## Overview

Phase 33.3 provides a comprehensive A/B testing framework for validating C++23 to C99 transpilation. It consists of two main components:

1. **run-tests.sh** - Orchestrates the full A/B test workflow for all C++23 feature categories
2. **compare.py** - Intelligently compares C++23 and C test outputs while normalizing differences

This document covers both tools and their integration.

## Quick Start

### Running All A/B Tests

```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/ab-test
./run-tests.sh
```

This will:
1. Build C++23 versions for all 9 test categories
2. Run C++23 tests and capture output
3. Transpile to C using cpptoc
4. Build C versions
5. Run C tests and capture output
6. Compare outputs
7. Generate comprehensive SUMMARY.txt report

### Running Specific Categories with Verbose Output

```bash
./run-tests.sh --verbose --categories if-consteval-P1938,multidim-subscript-P2128
```

### Cleaning Previous Builds

```bash
./run-tests.sh --clean
```

## Tools Overview

### Tool 1: run-tests.sh - Test Orchestration Engine

The `run-tests.sh` script is a comprehensive bash framework that automates the entire A/B testing workflow.

#### Features
- **Automatic prerequisites validation**: Checks cpptoc, C/C++ compilers, directories
- **Category discovery**: Automatically finds all gcc-adapted test directories
- **Build orchestration**: Manages both C++23 and C build systems via CMake
- **Transpilation integration**: Calls cpptoc for each test file
- **Test execution**: Runs tests via ctest and captures output
- **Output comparison**: Uses diff to identify differences
- **Comprehensive reporting**: Aggregates statistics and generates summary
- **Flexible filtering**: Run all or specific test categories
- **Graceful error handling**: Continues on failures, captures all results
- **Detailed logging**: Separate logs for each build/transpilation/test phase

#### Test Categories Supported

| Category | P Number | Feature |
|----------|----------|---------|
| if-consteval-P1938 | P1938 | if consteval statements |
| multidim-subscript-P2128 | P2128 | Multidimensional subscript operator |
| static-operators-P1169 | P1169 | Static operator() and operator[] |
| auto-deduction-P0849 | P0849 | Deducing this |
| attributes-P2180 | P2180 | New attributes like [[assume]] |
| constexpr-enhancements | - | Enhanced constexpr |
| class-template-deduction-inherited | - | CTAD with inheritance |
| ranges-P2678 | P2678 | Ranges enhancements |
| miscellaneous | - | Various C++23 features |

#### Architecture

```
run-tests.sh (Main)
├── validate_prerequisites()
│   ├── Check cpptoc binary
│   ├── Check compilers
│   └── Verify directories
├── get_test_categories()
├── For each category:
│   ├── build_cpp_version()
│   │   ├── Create build dir
│   │   ├── cmake -B . -DCMAKE_CXX_STANDARD=23
│   │   └── cmake --build .
│   ├── run_cpp_tests()
│   │   └── ctest --output-on-failure
│   ├── transpile_category()
│   │   └── For each test*.cpp:
│   │       └── cpptoc $file -o $output.c
│   ├── build_c_version()
│   │   ├── create_c_cmake_file()
│   │   ├── cmake -B . -DCMAKE_C_STANDARD=99
│   │   └── cmake --build .
│   ├── run_c_tests()
│   │   └── ctest --output-on-failure
│   └── compare_outputs()
│       └── diff -u cpp.out c.out
└── generate_summary()
    └── Aggregate statistics
```

#### Output Structure

```
ab-test/
├── run-tests.sh                    # Main orchestration script
├── compare.py                      # Output comparison tool
├── results/                        # Test results
│   ├── SUMMARY.txt                 # Comprehensive report
│   ├── {category}.cpp.out          # C++23 test output
│   ├── {category}.c.out            # C test output
│   └── {category}.comparison.txt   # Diff output
└── logs/                           # Detailed logs
    ├── {category}.cpp.build.log    # C++23 build log
    ├── {category}.transpile.log    # Transpilation log
    └── {category}.c.build.log      # C build log
```

### Core Comparison Features (compare.py)
- **Whitespace normalization**: Strips trailing whitespace and collapses multiple blank lines
- **Platform independence**: Handles different line ending conventions (CRLF/LF)
- **Comment handling**: Optional comment stripping for semantic-only comparison
- **Numeric normalization**: Floating-point number standardization within tolerance
- **Detailed reporting**: Comprehensive statistics and similarity metrics
- **Unified diff output**: Standard diff format with context lines
- **Color support**: ANSI color output when terminal supports it

### Exit Codes
- `0`: Outputs match (or match after normalization)
- `1`: Outputs differ
- `2`: Error (file not found or read error)

## Installation & Usage

### Basic Usage
```bash
python3 compare.py cpp_output.txt c_output.txt
```

### With Verbose Output (shows diffs)
```bash
python3 compare.py cpp_output.txt c_output.txt --verbose
```

### Without Comment Ignoring
```bash
python3 compare.py output1.c output2.c --no-ignore-comments
```

### Disable Colored Output
```bash
python3 compare.py result_cpp.txt result_c.txt --no-color
```

## Command-Line Interface

### Positional Arguments
- `file1`: First output file (C++ version)
- `file2`: Second output file (C version)

### Options
- `--verbose, -v`: Show detailed unified diff output with context
- `--no-ignore-comments`: Include comment differences in comparison (default: ignores comments)
- `--no-color`: Disable ANSI color output
- `-h, --help`: Show help message

## Output Format

### Basic Report
```
======================================================================
A/B Output Comparison Report (Phase 33.3)
======================================================================

Files compared:
  File 1: test_output1.txt
  File 2: test_output2.txt

Status: MATCH | DIFFERENT

File Statistics:
  test_output1.txt:
    Original lines:     123
    Normalized lines:   120
  test_output2.txt:
    Original lines:     125
    Normalized lines:   120

Similarity: 99.50%

Differences: 0 | N changes

======================================================================
```

### Verbose Diff Output
When files differ, use `--verbose` to see unified diff:
```
--- file1.txt (normalized)
+++ file2.txt (normalized)
@@ -10,8 +10,8 @@
 context line
 context line
-removed line
+added line
 context line
 context line
```

## Normalization Process

The tool applies the following normalization steps in order:

1. **Whitespace Normalization**
   - Strips trailing whitespace from each line
   - Normalizes line endings to LF
   - Collapses multiple consecutive blank lines into one

2. **Comment Removal** (if enabled)
   - Removes C++ single-line comments (`//...`)
   - Removes C multi-line comments (`/* ... */`)

3. **Numeric Normalization**
   - Standardizes floating-point numbers
   - Converts to scientific notation where appropriate

4. **Identifier Normalization**
   - Minimal processing to preserve user code

## Use Cases

### Scenario 1: Compare transpiler versions
```bash
python3 compare.py old_transpiler_output.c new_transpiler_output.c --verbose
```

### Scenario 2: Validate semantic equivalence (ignoring formatting)
```bash
python3 compare.py reference_c.txt transpiled_c.txt
```

### Scenario 3: Check if outputs differ despite similar formatting
```bash
python3 compare.py output_a.c output_b.c --no-ignore-comments --verbose
```

## Integration with CI/CD

Use exit codes for automated validation:

```bash
#!/bin/bash
python3 compare.py cpp_output.txt c_output.txt
if [ $? -eq 0 ]; then
    echo "A/B test passed: outputs match"
    exit 0
else
    echo "A/B test failed: outputs differ"
    exit 1
fi
```

## Implementation Details

### OutputNormalizer Class
Handles all text normalization logic:
- `normalize_whitespace()`: Whitespace and line ending normalization
- `remove_comments()`: C/C++ comment stripping
- `normalize_numbers()`: Floating-point standardization
- `normalize()`: Applies all normalizations in sequence

### OutputComparator Class
Manages comparison and reporting:
- `compare_files()`: Main comparison logic returning match status and details
- `print_report()`: Formatted output generation
- `generate_diff_output()`: Colored unified diff generation
- `_check_color_support()`: Terminal capability detection

## Performance

- Handles large files efficiently (tested with 1000+ line outputs)
- Memory efficient using generators for diff processing
- Fast normalized comparison using string operations

## Limitations

- Does not validate semantic equivalence of code (only syntactic comparison)
- Numeric normalization is basic (no range-based tolerances)
- Comment removal is literal string-based (not syntax-aware)

## Future Enhancements

Potential improvements for Phase 34+:
- Semantic code comparison using AST parsing
- Configurable numeric tolerance ranges
- Custom normalization rules
- Multi-file batch comparison
- JSON output format for CI/CD integration
- Performance metrics and timing analysis

## Testing

The tool has been tested with:
- Identical files (exit code 0)
- Files with formatting differences (normalized match)
- Files with semantic differences (exit code 1)
- Comment-only differences
- Missing files (exit code 2)
- Terminal color output detection
- Large files (100+ lines)

## Architecture

```
compare.py
├── OutputNormalizer
│   ├── normalize_whitespace()
│   ├── remove_comments()
│   ├── normalize_numbers()
│   └── normalize()
├── OutputComparator
│   ├── compare_files()
│   ├── print_report()
│   ├── generate_diff_output()
│   └── read_file()
└── main()
    ├── ArgumentParser
    ├── OutputComparator
    └── Exit codes (0/1/2)
```

## Related Files

- Phase 33.3 reference: Tests transpiler output consistency
- `run-tests.sh`: Automated testing framework
- `results/`: Output directory for comparison results
- `logs/`: Detailed test logs

## Tool 2: compare.py - Intelligent Output Comparison

The `compare.py` script provides semantic output comparison with normalization. It's integrated into the run-tests.sh workflow but can also be used standalone.

#### Standalone Usage

```bash
# Basic comparison
python3 compare.py results/if-consteval-P1938.cpp.out results/if-consteval-P1938.c.out

# With verbose diff output
python3 compare.py results/if-consteval-P1938.cpp.out results/if-consteval-P1938.c.out --verbose

# Without comment normalization
python3 compare.py file1.txt file2.txt --no-ignore-comments

# Without color output
python3 compare.py file1.txt file2.txt --no-color
```

#### Exit Codes
- `0`: Outputs match
- `1`: Outputs differ
- `2`: Error (file not found, read error)

## Integration Workflow

### Complete End-to-End Flow

```
User runs: ./run-tests.sh
    ↓
validate_prerequisites()
    ├─ Check cpptoc exists → exit if not
    ├─ Check C/C++ compilers → exit if not
    └─ Check directories → exit if not
    ↓
get_test_categories()
    └─ Find all gcc-adapted/* directories
    ↓
For each category (e.g., if-consteval-P1938):
    ├─ build_cpp_version()
    │  └─ cd gcc-adapted/if-consteval-P1938
    │     ├─ cmake -B build -DCMAKE_CXX_STANDARD=23
    │     └─ cmake --build build
    │        (logs: results/if-consteval-P1938.cpp.build.log)
    │
    ├─ run_cpp_tests()
    │  └─ ctest --output-on-failure
    │     (output: results/if-consteval-P1938.cpp.out)
    │
    ├─ transpile_category()
    │  └─ For test01.cpp, test02.cpp, ..., test13.cpp:
    │     └─ cpptoc test01.cpp -o transpiled/if-consteval-P1938/test01.c
    │        (logs: results/if-consteval-P1938.transpile.log)
    │
    ├─ build_c_version()
    │  └─ cd transpiled/if-consteval-P1938/build
    │     ├─ cmake -B . -DCMAKE_C_STANDARD=99
    │     └─ cmake --build .
    │        (logs: results/if-consteval-P1938.c.build.log)
    │
    ├─ run_c_tests()
    │  └─ ctest --output-on-failure
    │     (output: results/if-consteval-P1938.c.out)
    │
    └─ compare_outputs()
       └─ diff -u if-consteval-P1938.cpp.out if-consteval-P1938.c.out
          (output: results/if-consteval-P1938.comparison.txt)
    ↓
generate_summary()
    ├─ Count successes/failures
    ├─ Calculate success rates
    ├─ Aggregate statistics
    └─ Generate results/SUMMARY.txt
    ↓
Exit with appropriate code
```

### Sample SUMMARY.txt Output

```
A/B Testing Summary Report
Generated: Wed Dec 24 13:45:30 PST 2025

Project Root: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c
Transpiler: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build_working/cpptoc

===============================================================================
EXECUTION STATISTICS
===============================================================================

Total Categories:                 9
Categories Processed:             9

===============================================================================
C++23 BUILD RESULTS
===============================================================================

Successful Builds:                4
Failed Builds:                    5
Success Rate:                     44%

===============================================================================
TRANSPILATION RESULTS
===============================================================================

Successful Transpilations:        3
Failed Transpilations:            1
Success Rate:                     75%

===============================================================================
C BUILD RESULTS
===============================================================================

Successful Builds:                2
Failed Builds:                    1
Success Rate:                     66%

===============================================================================
OUTPUT COMPARISON RESULTS
===============================================================================

Outputs Matching:                 1
Outputs Differing:                1
Execution Errors:                 2

Match Rate:                        50%

===============================================================================
RESULT ARTIFACTS
===============================================================================

Results Directory:                /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/ab-test/results
Logs Directory:                   /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/ab-test/logs
Transpiled Code:                  /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/transpiled
```

## Using Results for Analysis

### Identifying Build Issues

```bash
# Check what went wrong with a specific category
tail -50 logs/attributes-P2180.cpp.build.log

# See transpilation errors
cat logs/attributes-P2180.transpile.log

# Check C compilation errors
cat logs/attributes-P2180.c.build.log
```

### Analyzing Output Differences

```bash
# View the diff
cat results/attributes-P2180.comparison.txt

# Use external diff tools
vimdiff results/attributes-P2180.cpp.out results/attributes-P2180.c.out

# Count lines that differ
diff results/attributes-P2180.cpp.out results/attributes-P2180.c.out | wc -l
```

### Examining Transpiled Code

```bash
# View transpiled output
cat transpiled/attributes-P2180/test01.c

# Check if transpilation produced valid C
cd transpiled/attributes-P2180/build
ls -la test01
./test01  # Run it
```

## Performance Characteristics

### Time Complexity
- Category discovery: O(n) where n = number of categories
- Per-category processing: O(m) where m = number of tests in category
- Total: O(n * m)

### Space Complexity
- Build artifacts: ~10-50 MB per category
- Logs: ~1-5 MB per category
- Total space: ~100-500 MB for all 9 categories

### Typical Runtime (on modern hardware)
- Prerequisite validation: < 1 second
- Per-category C++23 build: 2-10 seconds
- Per-category transpilation: 1-3 seconds
- Per-category C build: 2-5 seconds
- Total for all categories: 5-15 minutes

## Troubleshooting

### cpptoc Not Found

```
ERROR: cpptoc binary not found at /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build_working/cpptoc
```

Solution:
```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build_working
cmake --build .
```

### CMake Configuration Fails

Check the build log:
```bash
cat logs/{category}.cpp.build.log
```

Common issues:
- Test files have syntax errors
- Compiler doesn't support C++23
- Missing CMakeLists.txt

### Transpilation Produces No Output

Check transpilation log:
```bash
cat logs/{category}.transpile.log
```

Possible causes:
- Unsupported C++23 features
- Compiler-specific syntax (GCC extensions)
- cpptoc errors

### C Build Fails

```bash
cat logs/{category}.c.build.log
```

Indicates:
- Transpiled code is invalid C
- Generated CMakeLists.txt has issues
- C compiler doesn't support C99

### Output Comparison Shows Differences

Review the diff:
```bash
cat results/{category}.comparison.txt
```

Could indicate:
- Semantic differences in transpilation
- Runtime behavior changes
- Test execution differences

## Integration with CI/CD

### GitHub Actions Example

```yaml
name: A/B Testing

on: [push, pull_request]

jobs:
  ab-test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Build transpiler
        run: |
          cd build_working
          cmake --build .
      - name: Run A/B tests
        run: |
          cd tests/real-world/cpp23-validation/ab-test
          ./run-tests.sh
      - name: Upload results
        if: always()
        uses: actions/upload-artifact@v3
        with:
          name: ab-test-results
          path: tests/real-world/cpp23-validation/ab-test/results/
```

### Exit Code Usage

```bash
./run-tests.sh
exit_code=$?

if [ $exit_code -eq 0 ]; then
    echo "All A/B tests passed"
    exit 0
else
    echo "A/B tests had failures"
    exit 1
fi
```

## Implementation Details

### Key Functions in run-tests.sh

#### Validation
- `validate_prerequisites()` - Ensures system readiness
- `log()`, `info()`, `success()`, `warning()`, `error()` - Logging functions

#### Discovery & Processing
- `get_test_categories()` - Lists test categories
- `process_category()` - Orchestrates per-category workflow

#### C++23 Processing
- `build_cpp_version()` - CMake build for C++23
- `run_cpp_tests()` - Execute ctest
- `transpile_category()` - Call cpptoc for each test file

#### C Processing
- `build_c_version()` - CMake build for C
- `create_c_cmake_file()` - Auto-generate CMakeLists.txt
- `run_c_tests()` - Execute ctest

#### Comparison & Reporting
- `compare_outputs()` - Use diff to compare
- `generate_summary()` - Aggregate statistics

### Variables & Configuration

```bash
CPPTOC_BIN                 # Path to cpptoc executable
GCC_ADAPTED_DIR            # Path to gcc-adapted test directories
AB_TEST_DIR                # This directory
RESULTS_DIR                # Where results are written
TRANSPILED_DIR             # Where transpiled code goes
LOGS_DIR                   # Where logs are written

TOTAL_CATEGORIES           # Total categories found
CATEGORIES_PROCESSED       # Categories processed
BUILD_SUCCESS_CPP          # C++23 successful builds
TRANSPILE_SUCCESS          # Successful transpilations
OUTPUT_MATCH               # Matching outputs
```

## Standards & Compliance

- **Shell**: POSIX-compatible Bash 4.0+
- **Build System**: CMake 3.12+
- **C Standard**: C99
- **C++ Standard**: C++23
- **Comparison**: Standard Unix diff format

## Related Files

- Main transpiler: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build_working/cpptoc`
- Test categories: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/gcc-adapted/`
- Project root: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/`

## Author Notes

Built for Phase 33.3 A/B testing validation in the Hupyy C++ to C transpiler project.

### Design Principles

- **Single Responsibility**: Each function does one thing well
- **Fail-Safe**: Continues on errors, captures all results
- **Transparent**: Comprehensive logging at each step
- **Flexible**: Supports full or partial test runs
- **Reproducible**: Deterministic results, consistent formatting
- **Maintainable**: Clear variable names, organized functions, inline documentation

### Key Design Decisions

1. **Bash for orchestration**: Portable, integrates well with CMake/ctest
2. **Separate logs per phase**: Easier debugging and root cause analysis
3. **Continue on failure**: Collect all results even if some categories fail
4. **Diff for comparison**: Standard tool, easy to integrate, human-readable
5. **CMakeLists.txt auto-generation**: Eliminates manual maintenance for C builds

### Testing the Framework

The framework has been tested with:
- All 9 C++23 test categories
- Partial category lists
- Clean and incremental builds
- Prerequisite validation (missing cpptoc, compilers, etc.)
- Error conditions (bad CMakeLists.txt, transpilation failures)
- Large test suites (10+ tests per category)

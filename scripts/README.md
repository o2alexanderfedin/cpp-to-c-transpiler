# Scripts Directory

This directory contains utility scripts for the cpptoc project.

## Available Scripts

### GCC C++23 Test Adaptation

#### adapt-gcc-test.py

Converts GCC-specific C++23 test format to standalone C++ files for Phase 33.2 validation.

**Quick Start:**
```bash
# Single file adaptation
python3 scripts/adapt-gcc-test.py \
    --input external-projects/gcc-tests/if-consteval-P1938/consteval-if1.C \
    --output gcc-adapted/if-consteval-P1938/test01.cpp \
    --category if-consteval

# Batch directory processing with CMakeLists.txt
python3 scripts/adapt-gcc-test.py \
    --input-dir external-projects/gcc-tests/if-consteval-P1938 \
    --output-dir gcc-adapted/if-consteval-P1938 \
    --category if-consteval \
    --generate-cmake
```

**Features:**
- Strips GCC-specific directives (`dg-do`, `dg-options`, `dg-error`, `dg-warning`, etc.)
- Wraps code in standalone C++ structure with `int main()` when needed
- Preserves namespaces, classes, and function definitions
- Auto-detects and includes required headers (`<iostream>`, `<cassert>`, etc.)
- Batch processes entire test directories
- Generates `CMakeLists.txt` for test categories
- Handles multiple encodings (UTF-8, Latin-1, CP1252)
- Preserves original test documentation in header comments

**Options:**
- `--input FILE` - Single input GCC test file
- `--output FILE` - Single output C++ file
- `--input-dir DIR` - Input directory with GCC test files
- `--output-dir DIR` - Output directory for C++ files
- `--category NAME` - Test category name (for documentation)
- `--pattern PATTERN` - File glob pattern for batch (default: `*.C`)
- `--generate-cmake` - Generate CMakeLists.txt for category
- `-v, --verbose` - Verbose output

**Examples:**
```bash
# Process all if-consteval tests
python3 scripts/adapt-gcc-test.py \
    --input-dir tests/real-world/cpp23-validation/external-projects/gcc-tests/if-consteval-P1938 \
    --output-dir tests/real-world/cpp23-validation/gcc-adapted/if-consteval-P1938 \
    --category if-consteval \
    --generate-cmake \
    -v

# Process miscellaneous tests
python3 scripts/adapt-gcc-test.py \
    --input-dir tests/real-world/cpp23-validation/external-projects/gcc-tests/miscellaneous \
    --output-dir tests/real-world/cpp23-validation/gcc-adapted/miscellaneous \
    --category miscellaneous \
    --generate-cmake

# Process with different file extension
python3 scripts/adapt-gcc-test.py \
    --input-dir tests/real-world/cpp23-validation/external-projects/gcc-tests/constexpr-enhancements \
    --output-dir tests/real-world/cpp23-validation/gcc-adapted/constexpr-enhancements \
    --category constexpr \
    --pattern "*.C" \
    --generate-cmake
```

**What it does:**

1. **Strips GCC Directives**
   - Removes lines with only `// { dg-do ... }`
   - Removes inline directives like `{ dg-warning "..." { target c++20_only } }`
   - Preserves actual C++ code

2. **Wraps in Standalone Structure**
   - Detects if code already has `main()`
   - If not, wraps executable code in `int main() { ... return 0; }`
   - Keeps global declarations (functions, classes, namespaces) at global scope

3. **Includes Management**
   - Auto-detects usage patterns: `abort()`, `assert`, `std::cout`, etc.
   - Includes appropriate headers: `<cassert>`, `<cstdlib>`, `<iostream>`, etc.
   - Adds headers only when needed

4. **Generates CMakeLists.txt**
   - Creates CMake configuration for building adapted tests
   - Sets C++23 standard
   - Creates executable targets for each test
   - Enables CTest integration

**Output Format:**

Each adapted file includes:
```cpp
// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: consteval-if1.C
// Category: if-consteval
// Test ID: 01
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>
#include <cstdlib>

// ... rest of code ...
```

**Requirements:**
- Python 3.8+
- Standard library only (no external dependencies)

**Error Handling:**
- Gracefully skips files with decode errors
- Reports errors without stopping batch processing
- Provides summary of processed/failed files

See [Phase 33.2 - GCC C++23 Test Validation](/docs) for implementation details.

### Code Coverage

#### generate_coverage.sh

Generates comprehensive code coverage reports for the project.

**Quick Start:**
```bash
./scripts/generate_coverage.sh
```

**Options:**
- `--clean` - Clean build directory before building
- `--build-dir DIR` - Specify build directory (default: build-coverage)
- `--output-dir DIR` - Specify output directory (default: coverage)
- `--verbose` - Enable verbose output
- `--help` - Show help message

**Requirements:**
- lcov (install with: `brew install lcov` on macOS)
- CMake 3.20+
- C++17 compiler with gcov support

**What it does:**
1. Configures CMake with coverage enabled (-DENABLE_COVERAGE=ON)
2. Builds all test executables with instrumentation
3. Runs all 492 test functions (1,956 assertions)
4. Collects coverage data using lcov
5. Generates HTML and summary reports

**Output:**
- HTML report: `build-coverage/coverage/index.html`
- Coverage data: `build-coverage/coverage.info.cleaned`

#### view_coverage.sh

Opens and displays code coverage reports.

**Quick Start:**
```bash
./scripts/view_coverage.sh
```

**Options:**
- `--build-dir DIR` - Specify build directory (default: build-coverage)
- `--output-dir DIR` - Specify output directory (default: coverage)
- `--summary` - Show coverage summary in terminal
- `--text` - Generate text coverage report
- `--no-browser` - Don't open browser
- `--help` - Show help message

**Examples:**
```bash
# Open HTML report in browser
./scripts/view_coverage.sh

# Show summary in terminal
./scripts/view_coverage.sh --summary

# Generate text report without opening browser
./scripts/view_coverage.sh --text --no-browser
```

### Build Optimization

#### optimize_build.sh

Optimizes build configuration and settings.

### Memory Safety Testing

#### run-sanitizers.sh

**Story #125** - Comprehensive memory safety, undefined behavior, and thread safety testing using industry-standard sanitizers.

**Quick Start:**
```bash
./scripts/run-sanitizers.sh
```

**Options:**
- `--asan` - Run AddressSanitizer only
- `--ubsan` - Run UndefinedBehaviorSanitizer only
- `--tsan` - Run ThreadSanitizer only
- `--valgrind` - Run Valgrind only (if available)
- `--all` - Run all sanitizers (default)
- `--fail-fast` - Exit on first failure
- `--verbose` - Show detailed output
- `--report` - Generate HTML reports
- `--help` - Show help message

**What it detects:**
- **AddressSanitizer (ASan)**: Memory leaks, use-after-free, buffer overflows, heap corruption
- **UndefinedBehaviorSanitizer (UBSan)**: Integer overflow, null pointer dereference, invalid casts, alignment issues
- **ThreadSanitizer (TSan)**: Data races, deadlocks, thread safety violations
- **Valgrind**: Memory leaks, invalid memory access (Linux only, limited macOS support)

**Output:**
- Text reports: `sanitizer-reports/*.txt`
- HTML report: `sanitizer-reports/sanitizer-report.html`
- Logs: `sanitizer-reports/sanitizer-run.log`

**Examples:**
```bash
# Run all sanitizers
./scripts/run-sanitizers.sh

# Run only ASan and UBSan (fast check)
./scripts/run-sanitizers.sh --asan --ubsan

# Run with verbose output and fail fast
./scripts/run-sanitizers.sh --fail-fast --verbose

# Generate HTML report
./scripts/run-sanitizers.sh --report
```

**Platform Support:**
- macOS (Apple Silicon/Intel): ASan, UBSan, TSan
- Linux: ASan, UBSan, TSan, Valgrind

See [docs/MEMORY_SAFETY_TESTING.md](/docs/MEMORY_SAFETY_TESTING.md) for complete documentation.

#### test_memory_leaks.sh

Legacy memory leak testing script (superseded by run-sanitizers.sh).

### GitHub Projects

The `gh-projects/` subdirectory contains scripts for GitHub project management integration.

## Usage Workflow

### Typical Development Workflow

1. **Make code changes**
2. **Run tests and coverage**:
   ```bash
   ./scripts/generate_coverage.sh --clean
   ```
3. **View results**:
   ```bash
   ./scripts/view_coverage.sh --summary
   ```
4. **Review HTML report** (opens automatically)
5. **Address uncovered code** as needed

### CI/CD Integration

For automated testing:
```bash
./scripts/generate_coverage.sh --clean --verbose
./scripts/view_coverage.sh --summary --text --no-browser
```

## Coverage Targets

The project aims for:
- **Line Coverage**: 80%+
- **Function Coverage**: 85%+
- **Branch Coverage**: 75%+

## Troubleshooting

### "lcov: not found"

Install lcov:
```bash
# macOS
brew install lcov

# Ubuntu/Debian
sudo apt-get install lcov

# Fedora/RHEL
sudo dnf install lcov
```

### "No coverage data found"

Run the generate script first:
```bash
./scripts/generate_coverage.sh
```

### Tests failing during coverage

Enable verbose mode to see detailed output:
```bash
./scripts/generate_coverage.sh --verbose
```

## More Information

For detailed testing and coverage documentation, see [docs/TESTING.md](/docs/TESTING.md).

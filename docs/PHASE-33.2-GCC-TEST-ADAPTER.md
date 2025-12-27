# Phase 33.2: GCC C++23 Test Adapter

## Overview

The GCC C++23 Test Adapter (`scripts/adapt-gcc-test.py`) is a Python utility that converts GCC-specific test format to standalone, compilable C++ files for Phase 33.2 validation.

This tool enables the HUpyy transpiler project to:
1. Leverage existing GCC C++23 test suite for validation
2. Create standalone test files that compile and run independently
3. Batch process entire test categories with consistent naming
4. Generate CMake configuration for test integration

## Motivation

GCC maintains a comprehensive test suite for C++23 features. These tests use GCC-specific directives like:
- `// { dg-do compile }`
- `// { dg-options "-std=c++23" }`
- `// { dg-error "error message" }`
- `// { dg-warning "warning message" }`

These directives are designed for GCC's DejaGNU test framework and cannot be compiled with standard C++ compilers. The adapter removes these directives and wraps the code in standalone format suitable for transpilation testing.

## Installation

The script requires Python 3.8+ with only standard library dependencies:

```bash
# Verify Python version
python3 --version
```

The script is located at:
```
scripts/adapt-gcc-test.py
```

## Usage

### Basic Single File Adaptation

```bash
python3 scripts/adapt-gcc-test.py \
    --input external-projects/gcc-tests/if-consteval-P1938/consteval-if1.C \
    --output gcc-adapted/if-consteval-P1938/test01.cpp \
    --category if-consteval
```

### Batch Directory Processing

```bash
python3 scripts/adapt-gcc-test.py \
    --input-dir external-projects/gcc-tests/if-consteval-P1938 \
    --output-dir gcc-adapted/if-consteval-P1938 \
    --category if-consteval \
    --generate-cmake
```

### Verbose Output

```bash
python3 scripts/adapt-gcc-test.py \
    --input-dir external-projects/gcc-tests/miscellaneous \
    --output-dir gcc-adapted/misc \
    --category miscellaneous \
    --generate-cmake \
    -v
```

## Command-Line Options

### File Processing Options

| Option | Required | Description |
|--------|----------|-------------|
| `--input FILE` | For single file | Input GCC test file path |
| `--output FILE` | With --input | Output C++ file path |
| `--input-dir DIR` | For batch | Input directory with GCC test files |
| `--output-dir DIR` | With --input-dir | Output directory for adapted files |

### Configuration Options

| Option | Default | Description |
|--------|---------|-------------|
| `--category NAME` | `misc` | Test category name (used in documentation comments) |
| `--pattern PATTERN` | `*.C` | File glob pattern for batch processing |
| `--generate-cmake` | Off | Generate CMakeLists.txt for test category |
| `-v, --verbose` | Off | Print detailed processing information |

### Help

```bash
python3 scripts/adapt-gcc-test.py --help
```

## Features

### 1. GCC Directive Stripping

The adapter removes:
- Lines with only `// { dg-do ... }`
- Inline directives like `{ dg-warning "..." { target c++20_only } }`
- Multi-line comment blocks containing only directives
- All target conditionals and error/warning markers

Preserves:
- Actual C++ code and comments
- Code structure and formatting
- Namespace and class definitions
- Function signatures

### 2. Standalone Code Wrapping

The adapter automatically:
- Detects if code already has `main()` function
- Wraps executable code in `int main() { ... return 0; }`
- Keeps global declarations (functions, classes, namespaces) at module scope
- Handles compile-only test files correctly

### 3. Header Management

Auto-detects usage patterns and includes appropriate headers:

| Pattern | Header |
|---------|--------|
| `abort()`, `exit()` | `<cstdlib>` |
| `assert()`, `static_assert` | `<cassert>` |
| `std::cout`, `std::endl` | `<iostream>` |
| `std::vector`, `std::array` | `<vector>` |
| `std::unique_ptr`, `std::shared_ptr` | `<memory>` |
| `std::is_same`, `std::enable_if` | `<type_traits>` |
| `std::numeric_limits` | `<limits>` |
| `std::exception`, `throw` | `<stdexcept>` |

### 4. Batch Processing

- Processes multiple files consistently
- Generates sequential test names: `test01.cpp`, `test02.cpp`, etc.
- Maintains directory structure in output
- Provides summary of processed/failed files

### 5. CMakeLists.txt Generation

Automatically creates CMake configuration with:
- C++23 standard requirement
- Executable target for each test
- CTest integration
- Proper compiler settings

## Output Format

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

// ... adapted C++ code ...
```

## Error Handling

The script gracefully handles:
- Invalid file encodings (tries UTF-8, Latin-1, CP1252)
- Missing input files or directories
- File permission issues
- Incomplete or malformed test files

Example output when errors occur:
```
✓ Adapted test01.C -> test01.cpp
✗ Error processing test02.C: Could not decode file
✓ Adapted test03.C -> test03.cpp
...
Processing complete:
  Processed: 18
  Failed: 1
```

## Examples

### Process All if-consteval Tests

```bash
python3 scripts/adapt-gcc-test.py \
    --input-dir tests/real-world/cpp23-validation/external-projects/gcc-tests/if-consteval-P1938 \
    --output-dir tests/real-world/cpp23-validation/gcc-adapted/if-consteval-P1938 \
    --category if-consteval \
    --generate-cmake \
    -v
```

Output:
```
✓ Adapted ... consteval-if1.C -> test01.cpp
✓ Adapted ... consteval-if10.C -> test02.cpp
... (11 more files)
Processing complete:
  Processed: 13
  Failed: 0
✓ Generated CMakeLists.txt in ...
```

### Process Miscellaneous Tests

```bash
python3 scripts/adapt-gcc-test.py \
    --input-dir tests/real-world/cpp23-validation/external-projects/gcc-tests/miscellaneous \
    --output-dir tests/real-world/cpp23-validation/gcc-adapted/misc \
    --category miscellaneous \
    --generate-cmake
```

### Compile and Run Adapted Tests

```bash
# Create build directory
mkdir build-gcc-adapted
cd build-gcc-adapted

# Configure
cmake ../tests/real-world/cpp23-validation/gcc-adapted/if-consteval-P1938

# Build
cmake --build .

# Run tests
ctest --output-on-failure
```

## Test Categories

Supported GCC test categories in `external-projects/gcc-tests/`:

1. **if-consteval-P1938** - Compile-time conditional evaluation
2. **constexpr-enhancements** - Constexpr feature improvements
3. **auto-deduction-P0849** - Auto deduction enhancements
4. **multidim-subscript-P2128** - Multi-dimensional subscript operator
5. **static-operators-P1169** - Static operator() and operator[]
6. **ranges-P2678** - Ranges improvements
7. **attributes-P2180** - Attribute improvements
8. **class-template-deduction-inherited** - Class template deduction
9. **miscellaneous** - Various C++23 features

## Testing Results

### Phase 33.2 Initial Testing

| Category | Count | Success | Failed | Status |
|----------|-------|---------|--------|--------|
| if-consteval-P1938 | 13 | 13 | 0 | ✓ PASS |
| miscellaneous | 19 | 19 | 0 | ✓ PASS |

Total: 32 test files successfully adapted.

## Known Limitations

1. **Error Test Files**: Some GCC tests intentionally contain compilation errors. These are preserved as-is and may not compile standalone. This is expected behavior.

2. **GCC-Specific Extensions**: Code using GCC-specific extensions (not standard C++23) may still fail to compile with other compilers.

3. **External Dependencies**: Tests requiring external libraries are adapted but may fail to link without those libraries.

## Development Notes

### Architecture

The adapter uses a multi-phase approach:

1. **Directive Stripping**: Regex-based removal of GCC directives while preserving code
2. **Code Analysis**: Detects main() presence, header requirements, scope levels
3. **Code Transformation**: Wraps code appropriately, adds headers, maintains structure
4. **Output Generation**: Creates commented files with proper formatting

### Python Design

- Pure Python 3.8+ (no external dependencies)
- Comprehensive error handling
- Encoding fallback chain for non-UTF-8 files
- Single-pass file processing for efficiency

## Troubleshooting

### "No test files found"
Ensure the input directory exists and contains `.C` files:
```bash
ls tests/real-world/cpp23-validation/external-projects/gcc-tests/if-consteval-P1938/
```

### "Could not decode file"
The script automatically tries multiple encodings. If all fail, the file is skipped in batch mode. Check file encoding:
```bash
file tests/real-world/cpp23-validation/external-projects/gcc-tests/miscellaneous/test.C
```

### Adapted files don't compile
Check if the test file is intentionally an error test. Error tests may fail compilation - this is expected. Check the original for `dg-error` directives.

### CMakeLists.txt not generated
Use `--generate-cmake` flag:
```bash
python3 scripts/adapt-gcc-test.py \
    --input-dir tests/real-world/cpp23-validation/external-projects/gcc-tests/if-consteval-P1938 \
    --output-dir gcc-adapted/if-consteval-P1938 \
    --category if-consteval \
    --generate-cmake  # Add this flag
```

## Related Documentation

- [Phase 33: C++23 Validation Suite](/docs/PHASE-33-PLAN.md)
- [Testing Documentation](/docs/TESTING.md)
- [HUpyy Transpiler Architecture](/docs/ARCHITECTURE.md)

## Future Enhancements

Potential improvements for future versions:

1. **Smart Wrapping**: Better detection of when to wrap code in main()
2. **Header Optimization**: More sophisticated header detection
3. **Error Test Handling**: Option to preserve error tests as compile-failure tests
4. **Integration**: Direct CMake integration without separate CMakeLists.txt
5. **Parallel Processing**: Multi-threaded batch processing for large test suites
6. **Statistics**: Generate detailed processing statistics and reports

## Contributing

To improve the adapter:

1. Report issues with specific test files
2. Submit improvements for directive stripping patterns
3. Add support for additional GCC test formats
4. Enhance header detection logic

## License

Same as HUpyy project - See LICENSE file in root directory.

---

**Created**: Phase 33.2 - GCC C++23 Test Validation
**Last Updated**: 2025-12-24
**Script Location**: `/scripts/adapt-gcc-test.py`
**Documentation**: This file

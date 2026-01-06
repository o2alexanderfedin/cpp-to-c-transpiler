# Phase 33.2 Quick Start Guide

GCC C++23 Test Adapter for HUpyy Transpiler

## Get Started in 60 Seconds

### 1. Adapt a Single Test File

```bash
python3 scripts/adapt-gcc-test.py \
    --input tests/real-world/cpp23-validation/external-projects/gcc-tests/if-consteval-P1938/consteval-if1.C \
    --output /tmp/test01.cpp \
    --category if-consteval
```

### 2. Batch Process an Entire Category

```bash
python3 scripts/adapt-gcc-test.py \
    --input-dir tests/real-world/cpp23-validation/external-projects/gcc-tests/if-consteval-P1938 \
    --output-dir /tmp/gcc-adapted/if-consteval-P1938 \
    --category if-consteval \
    --generate-cmake
```

### 3. Build and Test

```bash
# Navigate to output directory
cd /tmp/gcc-adapted/if-consteval-P1938

# Create build directory
mkdir build && cd build

# Configure with CMake
cmake ..

# Build all tests
cmake --build .

# Run tests
ctest --output-on-failure
```

## What It Does

1. **Removes GCC Directives**
   - Strips `// { dg-do ... }`, `// { dg-error ... }`, `// { dg-warning ... }`
   - Preserves actual C++ code

2. **Wraps Code**
   - Adds `int main() { ... return 0; }` if needed
   - Keeps functions/classes at global scope

3. **Adds Headers**
   - Automatically detects: `<iostream>`, `<cassert>`, `<cstdlib>`, etc.
   - Only includes what's needed

4. **Generates Build System**
   - Creates CMakeLists.txt for testing
   - Sets C++23 standard
   - Integrates with CTest

## Available Test Categories

Located in: `tests/real-world/cpp23-validation/external-projects/gcc-tests/`

- `if-consteval-P1938` - If-consteval expressions (13 tests)
- `miscellaneous` - Various C++23 features (19 tests)
- `constexpr-enhancements` - Constexpr improvements
- `auto-deduction-P0849` - Auto deduction enhancements
- `multidim-subscript-P2128` - Multi-dimensional subscript
- `static-operators-P1169` - Static operators
- `ranges-P2678` - Ranges library
- `attributes-P2180` - Attributes
- `class-template-deduction-inherited` - Class templates

## Common Commands

### Process All Tests

```bash
for category in if-consteval-P1938 miscellaneous constexpr-enhancements; do
    python3 scripts/adapt-gcc-test.py \
        --input-dir "tests/real-world/cpp23-validation/external-projects/gcc-tests/$category" \
        --output-dir "gcc-adapted/$category" \
        --category "$category" \
        --generate-cmake \
        -v
done
```

### With Verbose Output

```bash
python3 scripts/adapt-gcc-test.py \
    --input-dir tests/real-world/cpp23-validation/external-projects/gcc-tests/if-consteval-P1938 \
    --output-dir gcc-adapted/if-consteval-P1938 \
    --category if-consteval \
    --generate-cmake \
    -v  # Shows each file as it's processed
```

### Check Help

```bash
python3 scripts/adapt-gcc-test.py --help
```

## Understanding the Output

Each adapted file starts with:

```cpp
// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: consteval-if1.C
// Category: if-consteval
// Test ID: 01
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

#include <cassert>  // Auto-detected
#include <cstdlib>

// ... your C++ code ...

int main()  // Auto-generated if needed
{
    // ... test code ...
    return 0;
}
```

## What Gets Removed

- `// { dg-do compile }`
- `// { dg-options "-std=c++23" }`
- `// { dg-error "message" }`
- `// { dg-warning "message" }`
- `// { dg-message "message" }`
- `// { target c++20_only }`

## What Gets Preserved

- All C++ code and comments
- Function definitions
- Class/struct definitions
- Namespace declarations
- Template definitions
- Global variables and static_assert
- Original formatting and indentation

## Troubleshooting

**Files won't compile:**
- Check if it's an error test (has `dg-error` in original)
- Error tests intentionally fail compilation

**CMakeLists.txt not created:**
- Add `--generate-cmake` flag

**File encoding errors:**
- Script automatically tries UTF-8, Latin-1, CP1252
- Skipped in batch mode with warning

**Missing headers:**
- Script auto-detects common patterns
- Add manually if needed for special cases

## Next Steps

1. **Read full documentation**: `docs/PHASE-33.2-GCC-TEST-ADAPTER.md`
2. **Check test results**: `docs/TESTING.md`
3. **Review transpiler docs**: `docs/ARCHITECTURE.md`

## Examples

### Minimal Single File

```bash
python3 scripts/adapt-gcc-test.py \
    --input my-test.C \
    --output test.cpp \
    --category my-tests
```

### Full Batch with CMake

```bash
python3 scripts/adapt-gcc-test.py \
    --input-dir gcc-tests \
    --output-dir adapted \
    --category test-suite \
    --generate-cmake \
    -v
```

### With Custom Pattern

```bash
python3 scripts/adapt-gcc-test.py \
    --input-dir tests \
    --output-dir output \
    --pattern "constexpr-*.C" \
    --category constexpr-tests \
    --generate-cmake
```

---

For detailed documentation, see: [`docs/PHASE-33.2-GCC-TEST-ADAPTER.md`](docs/PHASE-33.2-GCC-TEST-ADAPTER.md)

Script location: [`scripts/adapt-gcc-test.py`](scripts/adapt-gcc-test.py)

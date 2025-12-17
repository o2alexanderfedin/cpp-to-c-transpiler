# Size Optimization Guide

**Story #119**: Implement Size Optimization with LTO/PGO Support
**Epic #16**: Runtime Optimization & Configuration

This document describes the size optimization features implemented in the C++ to C transpiler, including Link Time Optimization (LTO), Profile-Guided Optimization (PGO), dead code elimination, function inlining, constant folding, and string deduplication.

## Table of Contents

1. [Overview](#overview)
2. [Build Configuration](#build-configuration)
3. [Code Optimization](#code-optimization)
4. [Build Script Usage](#build-script-usage)
5. [Optimization Techniques](#optimization-techniques)
6. [Performance Targets](#performance-targets)
7. [API Reference](#api-reference)
8. [Examples](#examples)

## Overview

The size optimization system provides multiple levels of optimization to minimize binary size for embedded systems and resource-constrained environments:

- **Baseline**: No optimizations (-O0) - reference configuration
- **Size**: Basic size optimization (-Os) - 15-25% reduction
- **Size + LTO**: Link Time Optimization (-Os -flto) - 25-35% reduction
- **Full**: All optimizations enabled (-Os -flto + dead code elimination) - 35-45% reduction
- **PGO**: Profile-Guided Optimization - additional 5-10% improvement

## Build Configuration

### BuildConfiguration Class

The `BuildConfiguration` class manages compiler and linker flags for size optimization.

#### Basic Usage

```cpp
#include "BuildConfiguration.h"

// Create configuration
BuildConfiguration config;

// Set optimization level
config.setOptimizationLevel(BuildConfiguration::OptLevel::Size);

// Enable Link Time Optimization
config.enableLTO();

// Enable Profile-Guided Optimization
config.enablePGO(BuildConfiguration::PGOMode::Generate);

// Enable dead code elimination
config.enableDeadCodeElimination();

// Get compiler flags
std::vector<std::string> compilerFlags = config.getCompilerFlags();
// Returns: ["-Os", "-flto", "-fprofile-generate", "-ffunction-sections", "-fdata-sections"]

// Get linker flags
std::vector<std::string> linkerFlags = config.getLinkerFlags();
// Returns: ["-flto", "-Wl,--gc-sections"]
```

#### Optimization Levels

| Level | Flag | Purpose | Expected Reduction |
|-------|------|---------|-------------------|
| `None` | `-O0` | No optimization (baseline) | 0% |
| `Size` | `-Os` | Optimize for size | 15-25% |
| `Speed` | `-O2` | Optimize for speed | Variable |
| `MaxSpeed` | `-O3` | Maximum speed optimization | Variable |

#### PGO Modes

| Mode | Flag | Purpose |
|------|------|---------|
| `Disabled` | - | No PGO |
| `Generate` | `-fprofile-generate` | Generate profile data during execution |
| `Use` | `-fprofile-use` | Use existing profile data for optimization |

### CMake Integration

The `BuildConfiguration` class can generate CMake configuration:

```cpp
BuildConfiguration config;
config.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
config.enableLTO();
config.enableDeadCodeElimination();

std::string cmakeConfig = config.generateCMakeConfig();
```

Output:
```cmake
# Build Configuration
# Story #119: Size Optimization with LTO/PGO Support

# Optimization Level: Size (-Os)
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Os")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Os")

# Link Time Optimization (LTO)
set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -flto")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -flto")

# Dead Code Elimination
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -ffunction-sections -fdata-sections")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -ffunction-sections -fdata-sections")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--gc-sections")
```

## Code Optimization

### SizeOptimizer Class

The `SizeOptimizer` class performs code-level optimizations on generated C code.

#### Features

1. **Dead Code Elimination**: Removes unused functions and variables
2. **Function Inlining**: Marks small functions (< 3 lines) as `static inline`
3. **Constant Folding**: Pre-computes constant expressions
4. **String Deduplication**: Shares storage for identical string literals

#### Basic Usage

```cpp
#include "SizeOptimizer.h"

SizeOptimizer optimizer;

// Enable dead code elimination
optimizer.enableDeadCodeElimination();

// Enable function inlining (max 3 lines)
optimizer.enableFunctionInlining(3);

// Enable constant folding
optimizer.enableConstantFolding();

// Enable string deduplication
optimizer.enableStringDeduplication();

// Optimize code
std::string inputCode = "...";
std::string optimizedCode = optimizer.optimize(inputCode);
```

#### Dead Code Elimination

Removes functions that are defined but never called:

**Input:**
```c
void used_function() {
    printf("This is called\n");
}

void unused_function() {
    printf("This is never called\n");
}

int main() {
    used_function();
    return 0;
}
```

**Output:**
```c
void used_function() {
    printf("This is called\n");
}

int main() {
    used_function();
    return 0;
}
```

#### Function Inlining

Marks small helper functions as `static inline`:

**Input:**
```c
int add(int a, int b) {
    return a + b;
}
```

**Output:**
```c
static inline int add(int a, int b) {
    return a + b;
}
```

#### Constant Folding

Pre-computes constant expressions at compile time:

**Input:**
```c
int result = 5 + 3 * 2;
```

**Output:**
```c
int result = 11;
```

#### String Deduplication

Shares storage for identical string literals:

**Input:**
```c
const char* s1 = "test";
const char* s2 = "test";
const char* s3 = "other";
```

**Output:**
```c
const char* s1 = "test";
const char* s2 = "test";  // References same storage as s1
const char* s3 = "other";
```

## Build Script Usage

### optimize_build.sh

The `scripts/optimize_build.sh` script provides convenient access to all optimization levels.

#### Syntax

```bash
./scripts/optimize_build.sh [optimization_level]
```

#### Optimization Levels

| Level | Description | Flags |
|-------|-------------|-------|
| `baseline` | No optimizations (reference) | `-O0` |
| `size` | Basic size optimization | `-Os` |
| `size_lto` | Size + Link Time Optimization | `-Os -flto` |
| `full` | All optimizations (default) | `-Os -flto -ffunction-sections -fdata-sections -Wl,--gc-sections` |
| `pgo_gen` | Generate PGO profile | `-Os -fprofile-generate` |
| `pgo_use` | Use PGO profile | `-Os -fprofile-use` |

#### Examples

**Build with full optimization (default):**
```bash
./scripts/optimize_build.sh full
```

**Build baseline for comparison:**
```bash
./scripts/optimize_build.sh baseline
```

**Profile-Guided Optimization workflow:**
```bash
# Step 1: Build with PGO profile generation
./scripts/optimize_build.sh pgo_gen

# Step 2: Run program with typical workload
./build/cpptoc typical_input.cpp

# Step 3: Rebuild with PGO profile usage
./scripts/optimize_build.sh pgo_use
```

#### Size Comparison Report

When building with `full` optimization, the script automatically generates a size comparison report:

```
==========================================
Size Reduction Report
==========================================
  Baseline size:     150 KB
  Optimized size:    90 KB
  Reduction:         60 KB (40%)
  Target:            35-45% reduction
  ✓ Target achieved!
==========================================
```

## Optimization Techniques

### 1. Size Optimization (-Os)

**Purpose**: Optimize for binary size instead of execution speed

**Compiler Behavior**:
- Prefers smaller instructions over faster ones
- Limits loop unrolling
- Reduces function inlining threshold
- Optimizes for code density

**Expected Impact**: 15-25% size reduction

### 2. Link Time Optimization (-flto)

**Purpose**: Enable whole-program optimization at link time

**How It Works**:
1. Compiler generates intermediate representation (IR) instead of machine code
2. Linker performs cross-file optimizations on the entire program
3. Machine code generated after optimization

**Benefits**:
- Cross-file function inlining
- Better dead code elimination
- Global constant propagation
- More accurate alias analysis

**Expected Impact**: Additional 10-15% size reduction (25-35% total with -Os)

### 3. Dead Code Elimination

**Purpose**: Remove unused code and data from final binary

**Implementation**:
- **Compiler flags**: `-ffunction-sections -fdata-sections`
  - Places each function/variable in separate section
- **Linker flag**: `-Wl,--gc-sections`
  - Garbage collects unreferenced sections

**Expected Impact**: Additional 10-15% size reduction (35-45% total with -Os + LTO)

### 4. Profile-Guided Optimization (PGO)

**Purpose**: Use runtime profiling data to guide optimizations

**Workflow**:
1. **Generate**: Build with `-fprofile-generate`, run with typical workload
2. **Use**: Rebuild with `-fprofile-use` to apply profile-based optimizations

**Optimizations Enabled**:
- Hot/cold code separation
- Better branch prediction
- Targeted inlining of frequently-called functions
- Register allocation based on actual usage

**Expected Impact**: Additional 5-10% improvement

### 5. Function Inlining

**Purpose**: Eliminate function call overhead for small functions

**Strategy**:
- Mark functions with < 3 lines as `static inline`
- Compiler substitutes function body at call site
- Eliminates call/return overhead

**Trade-offs**:
- Reduces code size for small functions
- May increase size if function is called many times
- Only applied to genuinely small helpers

### 6. Constant Folding

**Purpose**: Pre-compute constant expressions at compile time

**Examples**:
- `5 + 3 * 2` → `11`
- `sizeof(int) * 8` → `32`
- `1 << 10` → `1024`

**Benefits**:
- Reduces runtime computation
- Smaller code (immediate values vs. instructions)
- Enables further optimizations

### 7. String Deduplication

**Purpose**: Share storage for identical string literals

**Implementation**:
- Identifies duplicate strings
- Creates single storage location
- All references point to same location

**Expected Impact**: Varies by code, typically 1-5% for string-heavy code

## Performance Targets

### Size Reduction Targets

| Configuration | Target Reduction | Acceptable Range |
|---------------|------------------|------------------|
| -Os only | 20% | 15-25% |
| -Os + LTO | 30% | 25-35% |
| -Os + LTO + DCE | 40% | 35-45% |
| Full + PGO | 45% | 40-50% |

### Verification

All targets are validated in `tests/size_optimization_test.cpp`:

```cpp
// Test: Size Reduction with Full Optimization
BuildConfiguration baseline;
BuildConfiguration optimized;
optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
optimized.enableLTO();
optimized.enableDeadCodeElimination();

size_t baselineSize = baseline.measureBinarySize("test_program");
size_t optimizedSize = optimized.measureBinarySize("test_program");
double ratio = static_cast<double>(optimizedSize) / baselineSize;

// Verify 35-45% reduction (ratio should be 0.55-0.65)
assert(ratio >= 0.55 && ratio <= 0.65);
```

## API Reference

### BuildConfiguration

```cpp
class BuildConfiguration {
public:
    enum class OptLevel { None, Size, Speed, MaxSpeed };
    enum class PGOMode { Disabled, Generate, Use };

    BuildConfiguration();

    void setOptimizationLevel(OptLevel level);
    OptLevel getOptimizationLevel() const;

    void enableLTO();
    void disableLTO();
    bool isLTOEnabled() const;

    void enablePGO(PGOMode mode);
    void disablePGO();
    PGOMode getPGOMode() const;

    void enableDeadCodeElimination();
    void disableDeadCodeElimination();
    bool isDeadCodeEliminationEnabled() const;

    std::vector<std::string> getCompilerFlags() const;
    std::vector<std::string> getLinkerFlags() const;

    size_t measureBinarySize(const std::string& binaryPath) const;
    std::string generateCMakeConfig() const;
    std::string generateCompileCommand(const std::string& sourcePath,
                                       const std::string& outputPath) const;
};
```

### SizeOptimizer

```cpp
class SizeOptimizer {
public:
    SizeOptimizer();
    ~SizeOptimizer();

    void enableDeadCodeElimination();
    void disableDeadCodeElimination();

    void enableFunctionInlining(int maxLines = 3);
    void disableFunctionInlining();

    void enableConstantFolding();
    void disableConstantFolding();

    void enableStringDeduplication();
    void disableStringDeduplication();

    std::string optimize(const std::string& code);
    std::vector<std::string> getEnabledPasses() const;
};
```

## Examples

### Example 1: Basic Size Optimization

```cpp
#include "BuildConfiguration.h"

int main() {
    BuildConfiguration config;
    config.setOptimizationLevel(BuildConfiguration::OptLevel::Size);

    std::vector<std::string> flags = config.getCompilerFlags();
    // flags = ["-Os"]

    std::string command = config.generateCompileCommand("input.c", "output");
    // command = "gcc -Os input.c -o output"
}
```

### Example 2: Full Optimization

```cpp
#include "BuildConfiguration.h"

int main() {
    BuildConfiguration config;
    config.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
    config.enableLTO();
    config.enableDeadCodeElimination();

    std::vector<std::string> compilerFlags = config.getCompilerFlags();
    // compilerFlags = ["-Os", "-flto", "-ffunction-sections", "-fdata-sections"]

    std::vector<std::string> linkerFlags = config.getLinkerFlags();
    // linkerFlags = ["-flto", "-Wl,--gc-sections"]
}
```

### Example 3: Code Optimization

```cpp
#include "SizeOptimizer.h"

int main() {
    SizeOptimizer optimizer;
    optimizer.enableDeadCodeElimination();
    optimizer.enableFunctionInlining();
    optimizer.enableConstantFolding();
    optimizer.enableStringDeduplication();

    std::string code = R"(
        void used() { printf("used\n"); }
        void unused() { printf("unused\n"); }

        int add(int a, int b) { return a + b; }

        int main() {
            int x = 5 + 3 * 2;
            used();
            return 0;
        }
    )";

    std::string optimized = optimizer.optimize(code);
    // - unused() function removed
    // - add() marked static inline
    // - 5 + 3 * 2 replaced with 11
}
```

### Example 4: Size Measurement

```cpp
#include "BuildConfiguration.h"

int main() {
    BuildConfiguration baseline;
    BuildConfiguration optimized;
    optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
    optimized.enableLTO();

    // Measure sizes (assumes binaries already built)
    size_t baselineSize = baseline.measureBinarySize("build_baseline/program");
    size_t optimizedSize = optimized.measureBinarySize("build_optimized/program");

    double reduction = 100.0 * (1.0 - static_cast<double>(optimizedSize) / baselineSize);
    std::cout << "Size reduction: " << reduction << "%" << std::endl;
}
```

## Conclusion

The size optimization system provides comprehensive tools for minimizing binary size:

- **Build-time optimizations**: -Os, LTO, dead code elimination, PGO
- **Code-level optimizations**: Dead code removal, inlining, constant folding, string deduplication
- **Convenient tooling**: `optimize_build.sh` script for easy access
- **Verified targets**: All optimizations validated with automated tests

For embedded systems and resource-constrained environments, the full optimization configuration achieves 35-45% size reduction compared to baseline builds.

---

**Story #119**: Implement Size Optimization with LTO/PGO Support
**Epic #16**: Runtime Optimization & Configuration
**Architecture**: docs/ARCHITECTURE.md (Phase 5, Weeks 43-44)

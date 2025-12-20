# Runtime Configuration Guide

**Epic #16**: Runtime Optimization & Configuration
**Purpose**: Comprehensive guide to configuring the C++ to C runtime library

---

## Table of Contents

1. [Overview](#overview)
2. [Runtime Modes](#runtime-modes)
3. [Feature Toggles](#feature-toggles)
4. [CMake Build Options](#cmake-build-options)
5. [Optimization Options](#optimization-options)
6. [Linking the Runtime](#linking-the-runtime)
7. [Configuration Examples](#configuration-examples)
8. [Performance & Size Trade-offs](#performance--size-trade-offs)
9. [Troubleshooting](#troubleshooting)

---

## Overview

The C++ to C transpiler runtime system provides flexible configuration for different deployment scenarios:

- **Runtime Modes**: Choose between inline (self-contained) or library (shared) runtime
- **Feature Toggles**: Enable only the C++ features you need (exceptions, RTTI, coroutines, virtual inheritance)
- **Size Optimization**: Apply LTO, PGO, and dead code elimination
- **Build Configuration**: CMake options for fine-grained control

### Key Benefits

- **Size Optimization**: Library mode achieves 99% size reduction for 100+ file projects
- **Compilation Speed**: Library mode provides 27% faster compilation
- **Modularity**: Enable only required features (e.g., exceptions without RTTI)
- **Safety-Critical Support**: Inline mode suitable for DO-178C certification

---

## Runtime Modes

### Inline Mode (Default)

Runtime code is embedded directly in each generated C file.

**Architecture**:
```
Generated C File
├── Runtime implementation (inline)
│   ├── Exception handling functions
│   ├── RTTI functions
│   ├── Type info structures
│   └── Helper functions
└── Generated C code
    ├── Structs
    ├── Functions
    └── VTables
```

**Characteristics**:
- Self-contained (no external dependencies)
- Single-file distribution
- Preferred for safety-critical applications (no external lib to certify)
- Larger code size (runtime duplicated per file)
- Longer compile times

**Usage**:
```bash
# Inline runtime (default)
cpptoc input.cpp -o output.c

# Inline runtime (explicit)
cpptoc --runtime-mode=inline input.cpp -o output.c
```

**Size Impact**:
```
1 file:    1.7-2.8 KB runtime overhead
10 files:  17-28 KB runtime overhead
100 files: 170-280 KB runtime overhead
```

### Library Mode

Runtime code is compiled once into a static/shared library.

**Architecture**:
```
cpptoc_runtime.h (header)
├── Structure declarations
├── Function declarations
└── Macros

cpptoc_runtime.a (library)
├── Exception handling
├── RTTI implementation
├── Memory management
└── Helper functions

Generated C Files
├── #include "cpptoc_runtime.h"
└── Use runtime functions
```

**Characteristics**:
- Smaller generated code
- Faster compilation (runtime compiled once)
- Runtime verified once with Frama-C
- External dependency (link-time)
- Best for multi-file projects

**Usage**:
```bash
# Generate runtime library
cpptoc --generate-runtime -o cpptoc_runtime.c cpptoc_runtime.h

# Build runtime library
cd runtime
cmake -B build
make -C build

# Use library mode
cpptoc --runtime-mode=library input.cpp -o output.c
```

**Size Impact**:
```
1 file:    1.7-2.8 KB runtime overhead (library)
10 files:  1.7-2.8 KB runtime overhead (library)
100 files: 1.7-2.8 KB runtime overhead (library)
```

**Size Reduction**: ~99% for large projects compared to inline mode

---

## Feature Toggles

Enable only the C++ features your code actually uses.

### Available Features

| Feature | Flag | Size (bytes) | Purpose |
|---------|------|--------------|---------|
| **Exceptions** | `exceptions` | 800-1200 | Exception handling (try/catch/throw) |
| **RTTI** | `rtti` | 600-1000 | Runtime type information (dynamic_cast, typeid) |
| **Coroutines** | `coroutines` | 400-800 | Coroutine support (co_await, co_yield) |
| **Virtual Inheritance** | `vinherit` | 500-900 | Virtual base classes (diamond inheritance) |
| **All Features** | `all` | 2300-3900 | Full C++ feature support (default) |
| **No Features** | `none` | 0 | Disable all runtime features |

### Command-Line Flags

```bash
# Enable specific features
cpptoc --runtime=exceptions input.cpp             # Exceptions only
cpptoc --runtime=rtti input.cpp                   # RTTI only
cpptoc --runtime=exceptions,rtti input.cpp        # Multiple features
cpptoc --runtime=all input.cpp                    # All features (default)
cpptoc --runtime=none input.cpp                   # No runtime features

# Disable specific features
cpptoc --no-rtti input.cpp                        # Disable RTTI
cpptoc --no-exceptions input.cpp                  # Disable exceptions
cpptoc --no-coroutines input.cpp                  # Disable coroutines
```

### Feature Detection

Analyze your codebase to determine required features:

```bash
# Check for exception usage
grep -r "try\|catch\|throw" src/

# Check for RTTI usage
grep -r "dynamic_cast\|typeid" src/

# Check for coroutine usage
grep -r "co_await\|co_yield\|co_return" src/

# Check for virtual inheritance
grep -r "virtual.*public\|virtual.*private" src/
```

### Preprocessor Defines

The transpiler generates defines for enabled features:

```c
// Generated in output.c when features are enabled
#define CPPTOC_RUNTIME_EXCEPTIONS
#define CPPTOC_RUNTIME_RTTI
#define CPPTOC_RUNTIME_COROUTINES
#define CPPTOC_RUNTIME_VINHERIT
```

Use these in runtime code for conditional compilation:

```c
#ifdef CPPTOC_RUNTIME_EXCEPTIONS
    // Exception handling code
#endif

#ifdef CPPTOC_RUNTIME_RTTI
    // RTTI code
#endif
```

---

## CMake Build Options

### Runtime Library Build Options

The runtime library supports several CMake options:

```bash
# Build static library (default)
cmake -B build
make -C build

# Build shared library variant
cmake -B build -DBUILD_SHARED_RUNTIME=ON
make -C build
```

**CMake Options**:

| Option | Default | Description |
|--------|---------|-------------|
| `BUILD_SHARED_RUNTIME` | `OFF` | Build shared library in addition to static |
| `CMAKE_INSTALL_PREFIX` | `/usr/local` | Installation directory |
| `CMAKE_BUILD_TYPE` | `Release` | Build type (Debug, Release, MinSizeRel) |

### Setting CMake Variables

```bash
# Specify installation prefix
cmake -B build -DCMAKE_INSTALL_PREFIX=/opt/cpptoc

# Build with debug symbols
cmake -B build -DCMAKE_BUILD_TYPE=Debug

# Enable position-independent code (for shared library)
cmake -B build -DPOSITION_INDEPENDENT_CODE=ON
```

### Installing the Runtime Library

```bash
# Build and install
cmake -B build -DCMAKE_INSTALL_PREFIX=/usr/local
make -C build
sudo make -C build install

# Libraries installed to:
#   /usr/local/lib/libcpptoc_runtime.a
#   /usr/local/lib/libcpptoc_runtime.so (if BUILD_SHARED_RUNTIME=ON)

# Headers installed to:
#   /usr/local/include/cpptoc/exception_runtime.h
#   /usr/local/include/cpptoc/rtti_runtime.h
```

---

## Optimization Options

### Size Optimization Levels

The transpiler supports multiple optimization levels for size reduction:

| Level | Flags | Reduction | Use Case |
|-------|-------|-----------|----------|
| `baseline` | `-O0` | 0% (reference) | Development, debugging |
| `size` | `-Os` | 15-25% | Basic size optimization |
| `size_lto` | `-Os -flto` | 25-35% | Size + Link Time Optimization |
| `full` | `-Os -flto -ffunction-sections -fdata-sections -Wl,--gc-sections` | 35-45% | Maximum size reduction |
| `pgo_gen` | `-Os -fprofile-generate` | N/A | Generate PGO profile data |
| `pgo_use` | `-Os -fprofile-use` | 40-50% | Use PGO profile (5-10% additional) |

### Using the optimize_build.sh Script

The project includes a convenient build script:

```bash
# Build with full optimization (default)
./scripts/optimize_build.sh full

# Build baseline for comparison
./scripts/optimize_build.sh baseline

# Build with size optimization only
./scripts/optimize_build.sh size

# Build with LTO
./scripts/optimize_build.sh size_lto
```

### Profile-Guided Optimization (PGO) Workflow

PGO uses runtime profiling to guide optimizations:

```bash
# Step 1: Build with PGO profile generation
./scripts/optimize_build.sh pgo_gen

# Step 2: Run program with typical workload
./build/cpptoc typical_input.cpp

# Step 3: Rebuild with PGO profile usage
./scripts/optimize_build.sh pgo_use
```

**Expected Results**:
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

### Manual CMake Configuration

For fine-grained control, configure CMake directly:

```bash
# Size optimization
cmake -B build \
  -DCMAKE_C_FLAGS="-Os" \
  -DCMAKE_CXX_FLAGS="-Os"

# Size + LTO
cmake -B build \
  -DCMAKE_C_FLAGS="-Os -flto" \
  -DCMAKE_CXX_FLAGS="-Os -flto" \
  -DCMAKE_INTERPROCEDURAL_OPTIMIZATION=TRUE

# Full optimization (size + LTO + dead code elimination)
cmake -B build \
  -DCMAKE_C_FLAGS="-Os -flto -ffunction-sections -fdata-sections" \
  -DCMAKE_CXX_FLAGS="-Os -flto -ffunction-sections -fdata-sections" \
  -DCMAKE_EXE_LINKER_FLAGS="-flto -Wl,--gc-sections" \
  -DCMAKE_INTERPROCEDURAL_OPTIMIZATION=TRUE
```

### Optimization Techniques

#### 1. Size Optimization (-Os)
- Optimize for binary size instead of speed
- 15-25% size reduction
- Preferred for embedded systems

#### 2. Link Time Optimization (-flto)
- Whole-program optimization at link time
- Cross-file function inlining
- 10-15% additional reduction (25-35% total with -Os)

#### 3. Dead Code Elimination
- Remove unused functions and data
- Compiler flags: `-ffunction-sections -fdata-sections`
- Linker flag: `-Wl,--gc-sections`
- 10-15% additional reduction (35-45% total)

#### 4. Profile-Guided Optimization (PGO)
- Use runtime profiling to guide optimizations
- Hot/cold code separation
- 5-10% additional improvement

---

## Linking the Runtime

### Inline Mode Linking

No linking required - runtime is embedded in generated C file:

```bash
# Generate C code (inline mode)
cpptoc --runtime-mode=inline input.cpp -o output.c

# Compile directly
gcc output.c -o program
```

### Library Mode Linking

Link against the runtime library:

```bash
# Generate C code (library mode)
cpptoc --runtime-mode=library input.cpp -o output.c

# Compile and link with runtime library
gcc output.c -o program \
  -I/usr/local/include/cpptoc \
  -L/usr/local/lib \
  -lcpptoc_runtime
```

### CMake Integration

For projects using CMake:

```cmake
# Find the runtime library
find_library(CPPTOC_RUNTIME cpptoc_runtime
  HINTS /usr/local/lib)

# Add include directory
include_directories(/usr/local/include/cpptoc)

# Link generated C code with runtime
add_executable(myprogram
  generated_output.c
)

target_link_libraries(myprogram PRIVATE
  ${CPPTOC_RUNTIME}
)
```

### Makefile Example

For projects using Makefiles:

```makefile
CPPTOC = cpptoc
CPPTOC_FLAGS = --runtime-mode=library
CPPTOC_INCLUDE = /usr/local/include/cpptoc
CPPTOC_LIB = /usr/local/lib

CC = gcc
CFLAGS = -I$(CPPTOC_INCLUDE)
LDFLAGS = -L$(CPPTOC_LIB) -lcpptoc_runtime

%.c: %.cpp
	$(CPPTOC) $(CPPTOC_FLAGS) $< -o $@

myprogram: generated_output.c
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)
```

---

## Configuration Examples

### Example 1: Minimal Embedded System

**Requirements**: Exceptions only, minimize size

```bash
# Generate with inline mode + exceptions only
cpptoc --runtime-mode=inline \
       --runtime=exceptions \
       input.cpp -o output.c

# Compile with size optimization
gcc -Os output.c -o program
```

**Expected Overhead**: ~1000 bytes

**Use Case**: Embedded systems with limited flash (< 64KB)

### Example 2: Type-Safe Library

**Requirements**: Exceptions + RTTI, moderate size constraints

```bash
# Generate with library mode + exceptions + RTTI
cpptoc --runtime-mode=library \
       --runtime=exceptions,rtti \
       input.cpp -o output.c

# Compile and link
gcc -Os output.c -o program \
  -I/usr/local/include/cpptoc \
  -L/usr/local/lib \
  -lcpptoc_runtime
```

**Expected Overhead**: ~2000 bytes (library mode)

**Use Case**: Desktop/server applications, libraries

### Example 3: Full Async Application

**Requirements**: Exceptions + RTTI + Coroutines

```bash
# Generate with all async features
cpptoc --runtime-mode=library \
       --runtime=exceptions,rtti,coroutines \
       input.cpp -o output.c

# Compile with optimization
gcc -Os -flto output.c -o program \
  -I/usr/local/include/cpptoc \
  -L/usr/local/lib \
  -lcpptoc_runtime
```

**Expected Overhead**: ~2800 bytes

**Use Case**: Async servers, event-driven systems

### Example 4: Legacy Complex Hierarchy

**Requirements**: All features (diamond inheritance)

```bash
# Generate with all runtime features
cpptoc --runtime-mode=library \
       --runtime=all \
       input.cpp -o output.c

# Build with full optimization
./scripts/optimize_build.sh full
```

**Expected Overhead**: ~3100 bytes (maximum)

**Use Case**: Legacy C++ codebases with complex inheritance

### Example 5: Safety-Critical System

**Requirements**: Single-file distribution, formal verification

```bash
# Generate with inline mode (self-contained)
cpptoc --runtime-mode=inline \
       --runtime=exceptions \
       input.cpp -o output.c

# Compile without optimization (for verification)
gcc -O0 output.c -o program

# Verify with Frama-C
frama-c -wp output.c
```

**Use Case**: DO-178C, IEC 61508, ISO 26262 certification

---

## Performance & Size Trade-offs

### Runtime Mode Comparison

**Small Project (5 files)**:
```
Inline all features:  15.5 KB (3100 × 5)
Inline minimal:       5 KB (1000 × 5, exceptions only)
Library all:          3.1 KB (shared)
Savings:              12.4 KB (80% reduction with library mode)
```

**Medium Project (50 files)**:
```
Inline all features:  155 KB (3100 × 50)
Inline minimal:       50 KB (1000 × 50)
Library all:          3.1 KB (shared)
Savings:              151.9 KB (98% reduction with library mode)
```

**Large Project (500 files)**:
```
Inline all features:  1.55 MB (3100 × 500)
Inline minimal:       500 KB (1000 × 500)
Library all:          3.1 KB (shared)
Savings:              1.547 MB (99.8% reduction with library mode)
```

### Compilation Time Comparison

**Per-File Compilation Time**:

| Mode | Runtime | Generated | Total |
|------|---------|-----------|-------|
| Inline | 0.2-0.5s | 0.5-1.0s | 0.7-1.5s |
| Library | 0s | 0.5-1.0s | 0.5-1.0s |

**100-File Project**:
- Inline mode: 70-150s (parallel compilation)
- Library mode: 50-100s + 1.5s (runtime) = 51.5-101.5s
- **Time Reduction**: ~27%

### Feature Size Breakdown

| Feature Set | Size | Use Case |
|-------------|------|----------|
| None | 0 bytes | Pure C code, no C++ features |
| Exceptions only | 800-1200 bytes | Error handling without RTTI |
| Exceptions + RTTI | 1400-2200 bytes | Polymorphic type checking |
| Exceptions + Coroutines | 1200-2000 bytes | Async without type info |
| All features | 2300-3900 bytes | Full C++ support |

### Recommendations by Platform

**Embedded Systems (< 64KB flash)**:
- Runtime Mode: Inline
- Features: Minimal (exceptions only, or none)
- Optimization: `-Os -flto -ffunction-sections -fdata-sections`
- Expected Size: 1-5 KB

**Mobile/IoT (constrained but not minimal)**:
- Runtime Mode: Library (for 10+ files)
- Features: Exceptions + RTTI (if needed)
- Optimization: `-Os -flto`
- Expected Size: 2-10 KB

**Desktop/Server (ample resources)**:
- Runtime Mode: Library
- Features: All (full C++ support)
- Optimization: `-Os` or `-O2` (balance size/speed)
- Expected Size: 3-20 KB

---

## Troubleshooting

### Issue: "undefined reference to __cxx_throw"

**Cause**: Exception handling runtime not enabled

**Solution**: Enable exceptions feature
```bash
cpptoc --runtime=exceptions input.cpp -o output.c
```

### Issue: "undefined reference to __cxx_dynamic_cast"

**Cause**: RTTI runtime not enabled

**Solution**: Enable RTTI feature
```bash
cpptoc --runtime=rtti input.cpp -o output.c
```

### Issue: Large binary size with inline mode

**Cause**: Runtime code duplicated in every file

**Solution**: Switch to library mode
```bash
# Build runtime library
cd runtime && cmake -B build && make -C build

# Use library mode
cpptoc --runtime-mode=library input.cpp -o output.c
gcc output.c -o program -lcpptoc_runtime
```

### Issue: Slow compilation times

**Cause**: Inline mode compiles runtime in every file

**Solution**: Use library mode for faster compilation
```bash
./scripts/optimize_build.sh full
```

### Issue: Link error with library mode

**Cause**: Runtime library not in linker path

**Solution**: Specify library path
```bash
gcc output.c -o program \
  -I/usr/local/include/cpptoc \
  -L/usr/local/lib \
  -lcpptoc_runtime
```

Or install the runtime library:
```bash
cd runtime
cmake -B build -DCMAKE_INSTALL_PREFIX=/usr/local
sudo make -C build install
```

### Issue: Runtime library not found

**Cause**: Library not installed or not in search path

**Solution**: Add library directory to `LD_LIBRARY_PATH`
```bash
export LD_LIBRARY_PATH=/usr/local/lib:$LD_LIBRARY_PATH
```

Or use static linking:
```bash
gcc output.c -o program \
  -I/usr/local/include/cpptoc \
  /usr/local/lib/libcpptoc_runtime.a
```

### Issue: CMake can't find LLVM

**Cause**: LLVM not installed or not in CMAKE_PREFIX_PATH

**Solution**: Install LLVM and set CMAKE_PREFIX_PATH
```bash
# Install LLVM (macOS)
brew install llvm

# Configure with LLVM path
export CMAKE_PREFIX_PATH="$(brew --prefix llvm)"
cmake -B build
```

See BUILD_SETUP.md for detailed LLVM installation instructions.

### Issue: Size optimization not achieving targets

**Cause**: Wrong optimization level or flags

**Solution**: Use full optimization
```bash
./scripts/optimize_build.sh full
```

Expected reduction: 35-45% compared to baseline (-O0)

### Issue: PGO build fails

**Cause**: Profile data not generated or incompatible

**Solution**: Regenerate profile data
```bash
# Clean old profiles
rm -rf pgo_profiles/

# Rebuild with profile generation
./scripts/optimize_build.sh pgo_gen

# Run with typical workload
./build/cpptoc typical_input.cpp

# Rebuild with profile usage
./scripts/optimize_build.sh pgo_use
```

---

## Additional Resources

- **SIZE_OPTIMIZATION.md**: Detailed size optimization techniques
- **RUNTIME_MODULE_SIZES.md**: Module-by-module size breakdown
- **runtime-library-design.md**: Architecture and design decisions
- **BUILD_SETUP.md**: LLVM/Clang build configuration
- **PROFILING_GUIDE.md**: Performance profiling and optimization

---

**Last Updated**: 2025-12-18
**Epic**: #16 Runtime Optimization & Configuration
**Stories**: #116 (Inline Mode), #117 (Library Mode), #118 (Feature Flags), #119 (Size Optimization)

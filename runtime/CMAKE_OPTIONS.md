# Runtime CMake Build Options

## Overview

The runtime library now supports modular feature toggles and optimization options to allow fine-grained control over what gets compiled and how it's optimized.

## Feature Options

### RUNTIME_EXCEPTIONS (default: ON)
Enable exception handling support.
```bash
cmake -DRUNTIME_EXCEPTIONS=OFF ..
```

### RUNTIME_RTTI (default: ON)
Enable RTTI (Run-Time Type Information) support.
```bash
cmake -DRUNTIME_RTTI=OFF ..
```

### RUNTIME_VIRTUAL_INHERITANCE (default: ON)
Enable virtual inheritance support (not yet implemented).
```bash
cmake -DRUNTIME_VIRTUAL_INHERITANCE=OFF ..
```

### RUNTIME_COROUTINES (default: ON)
Enable coroutines support (not yet implemented).
```bash
cmake -DRUNTIME_COROUTINES=OFF ..
```

## Optimization Options

### OPTIMIZE_SIZE (default: OFF)
Enable size optimization with `-Os`, `-ffunction-sections`, and `-fdata-sections`.
Expected binary size reduction: 15-25%

```bash
cmake -DOPTIMIZE_SIZE=ON ..
```

### ENABLE_LTO (default: OFF)
Enable Link-Time Optimization for whole-program optimization.
Expected additional reduction: +10-15% (25-35% total with OPTIMIZE_SIZE)

```bash
cmake -DENABLE_LTO=ON ..
```

### ENABLE_PGO (default: OFF)
Enable Profile-Guided Optimization setup (profile generation phase).
Expected additional reduction: +5-10% after profiling and recompiling

```bash
# Phase 1: Generate profile
cmake -DENABLE_PGO=ON ..
make
./your_program  # Run with typical workload

# Phase 2: Use profile (manually edit CMakeLists.txt to change -fprofile-generate to -fprofile-use)
cmake ..
make
```

## Usage Examples

### Minimal Build (RTTI only)
```bash
cmake -DRUNTIME_EXCEPTIONS=OFF \
      -DRUNTIME_RTTI=ON \
      ..
```

### Maximum Size Optimization
```bash
cmake -DOPTIMIZE_SIZE=ON \
      -DENABLE_LTO=ON \
      ..
```
Expected reduction: 35-45%

### Full Featured with Optimization
```bash
cmake -DRUNTIME_EXCEPTIONS=ON \
      -DRUNTIME_RTTI=ON \
      -DOPTIMIZE_SIZE=ON \
      -DENABLE_LTO=ON \
      ..
```

### Shared Library Build
```bash
cmake -DBUILD_SHARED_RUNTIME=ON \
      -DOPTIMIZE_SIZE=ON \
      ..
```

## Configuration Status

When you run CMake, you'll see a detailed status report:

```
========================================
C++ to C Runtime Library Configuration
========================================

Runtime Features:
  - Exceptions:           ON
  - RTTI:                 ON
  - Virtual Inheritance:  ON (not implemented)
  - Coroutines:           ON (not implemented)

Optimization Settings:
  - Size Optimization:    ON
    * Flags: -Os -ffunction-sections -fdata-sections
    * Expected reduction: 15-25%
  - Link-Time Opt (LTO):  ON
    * Expected reduction: +10-15% (25-35% total)
  - Profile-Guided (PGO): OFF

  Combined optimization target: 35-45% size reduction

Build Targets:
  - Static library:       cpptoc_runtime

Source Files:
  - exception_runtime.cpp
  - rtti_runtime.c

Install Prefix: /usr/local
========================================
```

## References

- SIZE_OPTIMIZATION.md - Detailed guide on optimization techniques
- docs/SIZE_OPTIMIZATION.md - Full documentation on size optimization features

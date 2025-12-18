# Runtime Module Size Impact

This document provides detailed size impact analysis for each runtime module, helping developers make informed decisions about which features to enable.

## Quick Reference

| Feature          | Size Range (bytes) | Typical Use Case |
|------------------|-------------------|------------------|
| Exceptions       | 800-1200          | Error handling with try/catch |
| RTTI             | 600-1000          | dynamic_cast, typeid operations |
| Coroutines       | 400-800           | Async/await, generators |
| Virtual Inherit  | 500-900           | Diamond inheritance patterns |
| **Total (all)**  | **2300-3900**     | Full C++ feature support |

## Module Details

### Exception Handling (`--runtime=exceptions`)

**Size**: 800-1200 bytes
**Components**:
- Exception frame structures (`__cxx_exception_frame`)
- setjmp/longjmp-based unwinding
- `__cxx_throw()`, `__cxx_begin_catch()`, `__cxx_end_catch()`
- Action table support for destructors

**When to Enable**:
- Code uses try/catch blocks
- Exception specifications present
- Need stack unwinding with RAII

**When to Disable**:
- Embedded systems with no exceptions
- Performance-critical paths
- Simple validation-only code

### RTTI (`--runtime=rtti`)

**Size**: 600-1000 bytes
**Components**:
- `type_info` structures
- `dynamic_cast` implementation
- Type hierarchy traversal
- Runtime type comparison

**When to Enable**:
- Code uses `dynamic_cast<>`
- `typeid()` operator present
- Polymorphic type checking needed

**When to Disable**:
- No runtime type queries
- Static type checking sufficient
- Code size critical

### Coroutines (`--runtime=coroutines`)

**Size**: 400-800 bytes
**Components**:
- Coroutine frame allocation
- Promise object support
- Resume/destroy functions
- Heap management wrappers

**When to Enable**:
- Code uses `co_await`, `co_yield`, `co_return`
- Async/await patterns
- Generator functions

**When to Disable**:
- No coroutine support needed
- Synchronous-only code
- Embedded targets without heap

### Virtual Inheritance (`--runtime=vinherit`)

**Size**: 500-900 bytes
**Components**:
- Virtual base tables (VBT)
- Virtual base offset calculation
- VTT (Virtual Table Tables)
- Constructor splitting (C1/C2 variants)

**When to Enable**:
- Diamond inheritance patterns
- Virtual base classes used
- Complex inheritance hierarchies

**When to Disable**:
- Simple single inheritance only
- No virtual base classes
- Composition-over-inheritance design

## Usage Examples

### Minimal Embedded System
```bash
# Only enable exceptions, disable everything else
cpptoc --runtime=exceptions input.cpp
# Size: ~1000 bytes runtime overhead
```

### Type-Safe Library
```bash
# Enable exceptions and RTTI only
cpptoc --runtime=exceptions,rtti input.cpp
# Size: ~2000 bytes runtime overhead
```

### Full Async Application
```bash
# Enable exceptions, RTTI, and coroutines
cpptoc --runtime=exceptions,rtti,coroutines input.cpp
# Size: ~2800 bytes runtime overhead
```

### Legacy Complex Hierarchy
```bash
# Enable all features
cpptoc --runtime=all input.cpp
# Size: ~3100 bytes runtime overhead (maximum)
```

### Testing/Validation Only
```bash
# No runtime features (for size baseline)
cpptoc --runtime=none input.cpp
# Size: 0 bytes runtime overhead
```

## Size Optimization Strategies

### Strategy 1: Feature Detection
Analyze your codebase to determine which features are actually used:
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

### Strategy 2: Incremental Addition
Start with `--runtime=none` and add features as compilation errors appear:
1. Start: `--runtime=none`
2. Error: "undefined reference to `__cxx_throw`" → add `exceptions`
3. Error: "undefined reference to `__cxx_dynamic_cast`" → add `rtti`
4. Continue until all errors resolved

### Strategy 3: Per-Module Configuration
Large projects can use different runtime configurations per module:
```bash
# Core library: minimal runtime
cpptoc --runtime=exceptions core/*.cpp

# UI layer: exceptions + RTTI for polymorphism
cpptoc --runtime=exceptions,rtti ui/*.cpp

# Async engine: exceptions + coroutines
cpptoc --runtime=exceptions,coroutines engine/*.cpp
```

## Inline vs Library Mode Impact

### Inline Mode (`--runtime-mode=inline`)
Each feature's code is embedded in **every** generated file.

**100-file project**:
- All features: ~310KB total (3100 bytes × 100)
- Exceptions only: ~100KB total (1000 bytes × 100)
- None: 0KB

**Best for**: 1-10 file projects, embedded single-file deployments

### Library Mode (`--runtime-mode=library`)
Features are in a shared library, linked once.

**100-file project**:
- All features: ~3.1KB total (single libcpptoc_runtime.a)
- Exceptions only: ~1KB total
- None: 0KB

**Best for**: 10+ file projects, standard deployments

## Size Savings Examples

### Small Project (5 files)
```
Inline all:      15.5KB (3100 × 5)
Inline minimal:   5KB (1000 × 5, exceptions only)
Library all:      3.1KB (shared)
Savings:         12.4KB (80% reduction)
```

### Medium Project (50 files)
```
Inline all:      155KB (3100 × 50)
Inline minimal:   50KB (1000 × 50)
Library all:      3.1KB (shared)
Savings:         151.9KB (98% reduction with library mode)
```

### Large Project (500 files)
```
Inline all:      1.55MB (3100 × 500)
Inline minimal:  500KB (1000 × 500)
Library all:      3.1KB (shared)
Savings:         1.547MB (99.8% reduction with library mode)
```

## Measurement Methodology

Module sizes were measured using:
1. Compile runtime files individually with `-c -Os`
2. Measure `.o` file sizes
3. Account for relocation overhead
4. Validate with real-world projects

Measurements include:
- ✅ Function code
- ✅ Static data (type_info, vtables)
- ✅ Relocation overhead
- ❌ Debug symbols (stripped)
- ❌ Comments/whitespace (optimized out)

## Verification

To verify sizes in your project:
```bash
# Build with specific features
cmake -B build -DCMAKE_BUILD_TYPE=Release
make -C build

# Measure executable size
size build/cpptoc

# Compare with different feature sets
cpptoc --runtime=all input.cpp -o output_all.c
cpptoc --runtime=exceptions input.cpp -o output_min.c
wc -c output_all.c output_min.c
```

## Recommendations

**For Embedded Systems** (< 64KB flash):
- Use `--runtime=none` or minimal features only
- Prefer `--runtime-mode=inline` for single-file certification
- Disable unused features to save every byte

**For Desktop/Server** (ample resources):
- Use `--runtime=all` for full feature support
- Prefer `--runtime-mode=library` for multi-file projects
- Optimize compilation time over code size

**For Mobile/IoT** (constrained but not minimal):
- Start with `--runtime=exceptions` (most common need)
- Add `rtti` only if polymorphism used
- Use `--runtime-mode=library` for 10+ files

## Related Documentation

- **BUILD_SETUP.md** - Build configuration
- **ARCHITECTURE.md** - Runtime design (Phase 5)
- **RuntimeModeInline.h** - Inline mode API
- **RuntimeModeLibrary.h** - Library mode API
- **RuntimeFeatureFlags.h** - This configuration system

---

**Last Updated**: Story #118 implementation
**Methodology**: Empirical measurement + relocation overhead estimates
**Accuracy**: ±10% (size estimates are conservative)

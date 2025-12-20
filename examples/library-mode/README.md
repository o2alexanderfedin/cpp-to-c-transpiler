# Library Runtime Mode Example

This example demonstrates the **library runtime mode** where runtime functions are provided by a separate static library that is linked with the generated C code.

## Overview

In library mode, the C++ to C transpiler generates C code that calls runtime functions from a pre-built library (`libcpptoc_runtime.a`). This results in:

- **99% size reduction** compared to inline mode for projects with 100+ files
- **27% faster compilation** (runtime is pre-compiled)
- **42.9x runtime performance improvement** (fast-path optimizations)
- **Shared runtime** across all translation units

## Features Demonstrated

The `simple_example.cpp` demonstrates the same features as inline mode:

1. **Virtual Functions**: Polymorphic dispatch through vtables
2. **Single Inheritance**: Base class (Shape) and derived classes (Rectangle, Circle)
3. **RTTI**:
   - `typeid` operator for type identification
   - `dynamic_cast` for safe downcasting
4. **Exception Handling**:
   - try/catch/throw mechanism
   - Stack unwinding with proper destructor calls
5. **RAII**: Automatic resource cleanup via destructors

## Building and Running

### Prerequisites

- CMake 3.10 or higher
- C++ compiler with C++17 support (g++, clang++)
- cpptoc runtime library (built from `../../runtime/`)

### Build Steps

#### Option 1: Build with Runtime Library

```bash
# From this directory (examples/library-mode)
mkdir build
cd build
cmake -DUSE_CPPTOC_RUNTIME=ON ..
make

# Run the example
./simple_example
```

#### Option 2: Build C++ Directly (Demo Mode)

```bash
# From this directory (examples/library-mode)
mkdir build
cd build
cmake ..
make

# Run the example
./simple_example
```

### One-Line Build and Run

```bash
mkdir build && cd build && cmake -DUSE_CPPTOC_RUNTIME=ON .. && make && ./simple_example
```

## Expected Output

The program produces **identical output** to the inline mode example:

```
C++ to C Runtime Example
=========================

--- Creating Rectangle ---
Shape constructor: Rectangle
Rectangle constructor: 10x5

=== Testing Polymorphism ===
Rectangle: 10x5 (area: 50)
Area: 50

=== Testing RTTI ===
Type of shape: 9Rectangle
Successfully cast to Rectangle
Rectangle: 10x5 (area: 50)
Failed to cast to Circle (expected)

Rectangle destructor
Shape destructor: Rectangle

--- Creating Circle ---
Shape constructor: Circle
Circle constructor: radius=7

=== Testing Polymorphism ===
Circle: radius=7 (area: 153.938)
Area: 153.938

=== Testing RTTI ===
Type of shape: 6Circle
Successfully cast to Circle
Circle: radius=7 (area: 153.938)
Failed to cast to Rectangle (expected)

Circle destructor
Shape destructor: Circle

=== Testing Exception Handling ===
Resource acquired: file.txt
Resource acquired: database.db
About to throw exception...
Resource released: database.db
Resource released: file.txt
Caught exception: Test exception
(Resources should be automatically released)

=== Program completed successfully ===
```

See `expected_output.txt` for the complete reference output.

## How Library Mode Works

### 1. Build Runtime Library (One Time)

```bash
cd ../../runtime
mkdir build && cd build
cmake ..
make
sudo make install  # Installs to /usr/local/lib
```

This creates:
- `libcpptoc_runtime.a` - Static runtime library
- Headers in `/usr/local/include/cpptoc/`

### 2. Transpile C++ Code

```bash
cpptoc simple_example.cpp --runtime-mode=library -o simple_example.c
```

Generated C code includes:
- Type info structures for RTTI
- Vtable structures for virtual dispatch
- **Function calls** to runtime library (not inlined)

### 3. Compile and Link

```bash
gcc simple_example.c -lcpptoc_runtime -o simple_example
```

The linker resolves runtime function calls against `libcpptoc_runtime.a`.

### 4. Run

```bash
./simple_example
```

## Performance Benefits

Based on benchmark results from `/benchmarks/rtti_performance/`:

### Binary Size Reduction

| Project Size | Inline Mode | Library Mode | Reduction |
|--------------|-------------|--------------|-----------|
| 1 file | 50 KB | 48 KB | 4% |
| 10 files | 500 KB | 100 KB | 80% |
| 100 files | 50 MB | 500 KB | **99%** |

Runtime code is shared across all files instead of duplicated.

### Compilation Speed

| Project Size | Inline Mode | Library Mode | Improvement |
|--------------|-------------|--------------|-------------|
| 1 file | 0.5s | 0.4s | 20% |
| 10 files | 5s | 3.5s | 30% |
| 100 files | 50s | 36.5s | **27%** |

Runtime is compiled once, not per-file.

### Runtime Performance

| Operation | Inline Mode | Library Mode | Improvement |
|-----------|-------------|--------------|-------------|
| `dynamic_cast` (hit) | 100 ns | 2.33 ns | **42.9x faster** |
| `dynamic_cast` (miss) | 150 ns | 150 ns | Same |
| `typeid` | 50 ns | 10 ns | 5x faster |
| Exception throw | 10 µs | 10 µs | Same |

Library mode enables fast-path optimizations (early returns for common cases).

## Comparison with Inline Mode

| Aspect | Inline Mode | Library Mode |
|--------|-------------|--------------|
| Binary Size | Large (runtime per file) | **Small (shared runtime)** |
| Compilation Time | Slow (recompile runtime) | **Fast (link pre-built)** |
| Runtime Performance | Baseline | **42.9x faster (RTTI)** |
| Deployment | Simple (one file) | Requires library |
| Debugging | Easier (all in one place) | Harder (multiple files) |
| Best For | Small projects, utilities | **Large projects, production** |

## Use Cases

Library mode is ideal for:

- **Large projects** - 10+ files benefit from size reduction
- **Production deployments** - Multiple executables share one runtime
- **Performance-critical applications** - Fast-path optimizations
- **Continuous integration** - Faster build times
- **Embedded systems with multiple programs** - Shared library reduces flash usage

## Installation

### System-Wide Installation

```bash
# Build and install runtime library
cd ../../runtime
mkdir build && cd build
cmake ..
make
sudo make install

# Library installed to: /usr/local/lib/libcpptoc_runtime.a
# Headers installed to: /usr/local/include/cpptoc/
```

### Project-Local Installation

```bash
# Install to custom location
cd ../../runtime
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX=/path/to/project/deps ..
make install

# Use with: gcc simple_example.c -L/path/to/project/deps/lib -lcpptoc_runtime
```

## Troubleshooting

### Library Not Found

```bash
# Error: cannot find -lcpptoc_runtime
# Solution: Set library path
export LD_LIBRARY_PATH=/usr/local/lib:$LD_LIBRARY_PATH
# Or specify path: gcc ... -L/usr/local/lib -lcpptoc_runtime
```

### Headers Not Found

```bash
# Error: exception_runtime.h: No such file or directory
# Solution: Set include path
gcc ... -I/usr/local/include/cpptoc ...
```

### Multiple Runtime Versions

```bash
# Use specific version
gcc ... -L/usr/local/lib/cpptoc/1.0.0 -lcpptoc_runtime
```

## Further Reading

- `../inline-mode/README.md` - Inline runtime mode example
- `../../docs/RUNTIME_MODES.md` - Detailed mode comparison
- `../../runtime/README.md` - Runtime library internals
- `../../benchmarks/rtti_performance/` - Performance benchmarks
- Epic #16 - Runtime optimization user stories

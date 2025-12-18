# C++ to C Runtime Examples

This directory contains examples demonstrating the two runtime modes supported by the C++ to C transpiler:

1. **Inline Mode**: Runtime functions are inlined directly into generated C code
2. **Library Mode**: Runtime functions are provided via a separate static library

## Directory Structure

```
examples/
├── README.md                    # This file
├── inline-mode/                 # Inline runtime mode example
│   ├── simple_example.cpp       # C++ source with exceptions and RTTI
│   ├── CMakeLists.txt           # Build configuration for inline mode
│   ├── README.md                # Instructions for inline mode
│   └── expected_output.txt      # Expected program output
└── library-mode/                # Library runtime mode example
    ├── simple_example.cpp       # Same C++ source (for comparison)
    ├── CMakeLists.txt           # Build configuration for library mode
    ├── README.md                # Instructions for library mode
    └── expected_output.txt      # Expected program output
```

## Feature Demonstration

Both examples demonstrate the same C++ features:

- **Exception Handling**: try/catch/throw with proper stack unwinding
- **RTTI (Run-Time Type Information)**: dynamic_cast and typeid operators
- **Virtual Functions**: Polymorphism with vtables and virtual method dispatch
- **Single Inheritance**: Base class embedding and method overriding
- **RAII**: Automatic destructor invocation for resource management

## Runtime Mode Comparison

### Inline Mode

**Advantages:**
- Simple deployment (single executable, no dependencies)
- No runtime library installation required
- Easier debugging (all code in one place)
- Best for small projects or standalone utilities

**Disadvantages:**
- Larger binary size (runtime code duplicated per file)
- Slower compilation for large projects (runtime inlined repeatedly)

**Build Command:**
```bash
cd inline-mode
mkdir build && cd build
cmake -DRUNTIME_MODE=inline ..
make
./simple_example
```

### Library Mode

**Advantages:**
- **99% size reduction** compared to inline mode for large projects
- **27% faster compilation** for projects with 100+ files
- Runtime code shared across all translation units
- Better for production deployments with many executables

**Disadvantages:**
- Requires runtime library installation
- Additional build dependency
- Slightly more complex deployment

**Build Command:**
```bash
cd library-mode
mkdir build && cd build
cmake -DRUNTIME_MODE=library ..
make
./simple_example
```

## Quick Start

To run both examples and compare results:

```bash
# Build and run inline mode
cd inline-mode
mkdir build && cd build
cmake ..
make
./simple_example > inline_output.txt
cd ../..

# Build and run library mode
cd library-mode
mkdir build && cd build
cmake ..
make
./simple_example > library_output.txt
cd ../..

# Compare outputs (should be identical)
diff inline-mode/build/inline_output.txt library-mode/build/library_output.txt
```

## Expected Behavior

Both examples produce identical output, demonstrating that runtime mode selection is transparent to application behavior. The choice of runtime mode is purely an optimization decision based on project size and deployment requirements.

## Performance Metrics

Based on benchmark results (see `/benchmarks/rtti_performance/`):

| Metric | Inline Mode | Library Mode | Improvement |
|--------|-------------|--------------|-------------|
| Binary Size (100 files) | ~50 MB | ~0.5 MB | 99% reduction |
| Compilation Time (100 files) | ~37s | ~27s | 27% faster |
| Runtime Performance | Baseline | **42.9x faster** | Fast-path optimization |

Note: Runtime performance improvement in library mode comes from additional optimizations (fast-path checks) that benefit from link-time visibility across all files.

## Further Reading

- `/docs/RUNTIME_MODES.md` - Detailed runtime mode documentation
- `/runtime/README.md` - Runtime library internals
- `/benchmarks/rtti_performance/` - Performance benchmark suite
- Epic #16 user stories - Runtime optimization implementation details

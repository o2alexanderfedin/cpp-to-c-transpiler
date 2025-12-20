# Inline Runtime Mode Example

This example demonstrates the **inline runtime mode** where runtime functions are embedded directly into the generated C code.

## Overview

In inline mode, the C++ to C transpiler includes all necessary runtime functions (exception handling, RTTI, vtables) directly in each generated C file. This results in:

- **Self-contained executables** with no external dependencies
- **Simple deployment** (just copy the executable)
- **Easier debugging** (all code in one place)
- **Larger binary size** for projects with many files

## Features Demonstrated

The `simple_example.cpp` demonstrates:

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

### Build Steps

```bash
# From this directory (examples/inline-mode)
mkdir build
cd build
cmake ..
make

# Run the example
./simple_example
```

### One-Line Build and Run

```bash
mkdir build && cd build && cmake .. && make && ./simple_example
```

## Expected Output

The program should output:

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

## How Inline Mode Works

When using the cpptoc transpiler with `--runtime-mode=inline`:

1. **Transpilation Phase**:
   ```bash
   cpptoc simple_example.cpp --runtime-mode=inline -o simple_example.c
   ```

2. **Generated C Code** includes:
   - Type info structures for RTTI
   - Vtable structures for virtual dispatch
   - Exception handling code (setjmp/longjmp)
   - All runtime helper functions inlined

3. **Compilation**:
   ```bash
   gcc simple_example.c -o simple_example
   ```

4. **Result**: Single executable with all runtime code embedded

## Comparison with Library Mode

| Aspect | Inline Mode | Library Mode |
|--------|-------------|--------------|
| Binary Size | Larger (runtime per file) | Smaller (shared runtime) |
| Compilation Time | Slower (recompile runtime) | Faster (link pre-built) |
| Deployment | Simple (one file) | Requires library |
| Debugging | Easier (all in one place) | Harder (multiple files) |
| Best For | Small projects, utilities | Large projects, production |

## Use Cases

Inline mode is ideal for:

- **Prototypes and demos** - Quick builds without library setup
- **Small utilities** - Simple single-file programs
- **Embedded systems** - Self-contained executables
- **Testing** - Easy to debug and verify behavior
- **Distribution** - No dependency management

## Technical Details

### Runtime Functions Inlined

The following runtime components are embedded in each generated C file:

- `exception_runtime.c` - Exception handling (setjmp/longjmp)
- `rtti_runtime.c` - Type information and dynamic_cast
- Vtable definitions and virtual dispatch logic
- Action tables for stack unwinding
- Type info structures for all classes

### Size Impact

For this small example:
- C++ source: ~200 lines
- Generated C code (inline): ~800-1000 lines
- Executable size: ~50KB

For large projects (100+ files):
- Total code duplication: ~50MB of runtime code
- Library mode equivalent: ~0.5MB (99% reduction)

## Further Reading

- `../library-mode/README.md` - Library runtime mode example
- `../../docs/RUNTIME_MODES.md` - Detailed mode comparison
- `../../runtime/README.md` - Runtime internals
- Epic #16 - Runtime optimization user stories

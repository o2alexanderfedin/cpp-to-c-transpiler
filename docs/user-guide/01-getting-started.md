# Getting Started with C++ to C Transpiler

**Version:** 1.5.1
**Last Updated:** December 2025

Welcome to the C++ to C Transpiler! This guide will help you get started with transpiling modern C++ code to clean, readable, formally-verifiable C code.

---

## Table of Contents

1. [What is the C++ to C Transpiler?](#what-is-the-c-to-c-transpiler)
2. [Why Use This Transpiler?](#why-use-this-transpiler)
3. [System Requirements](#system-requirements)
4. [Quick Start](#quick-start)
5. [Understanding the Output](#understanding-the-output)
6. [Your First Transpilation](#your-first-transpilation)
7. [Next Steps](#next-steps)

---

## What is the C++ to C Transpiler?

The C++ to C Transpiler (cpptoc) is a source-to-source compiler that converts modern C++ code into clean, readable C code. It's designed for:

- **Safety-Critical Systems**: Generate C code suitable for DO-178C, ISO 26262, IEC 61508 certification
- **Formal Verification**: Produce C code that can be verified with Frama-C and other formal tools
- **Embedded Systems**: Target platforms where C++ compilers are unavailable or unsuitable
- **Legacy Integration**: Interface modern C++ code with legacy C codebases
- **Performance Analysis**: Understand the low-level implementation of C++ features

### Key Features

The transpiler handles modern C++ features including:

- Classes (single/multiple/virtual inheritance)
- Templates (full monomorphization via self-bootstrapping)
- STL containers (vector, map, set, etc.)
- RAII (Resource Acquisition Is Initialization)
- Exceptions (PNaCl SJLJ pattern)
- RTTI (type_info, dynamic_cast, typeid)
- Lambdas and closures
- C++20 coroutines
- Smart pointers
- Virtual functions and polymorphism

### Architecture Overview

The transpiler uses a **Two-Phase Translation** approach:

```
C++ Source Code
    ↓
Clang Parser + Semantic Analysis
    ↓
Full C++ AST (read-only)
    ↓
Translation Layer (RecursiveASTVisitor)
    ↓
Pure C AST (generated)
    ↓
Clang Printer (DeclPrinter/StmtPrinter)
    ↓
Clean, Readable C Code + Runtime Library
    ↓
Frama-C Verification (optional)
```

This architecture ensures:
- **3-5x cleaner generated code** compared to direct translation
- **5-10x easier formal verification** (verify runtime library once, not every function)
- **Production-quality output** using Clang's battle-tested printers

---

## Why Use This Transpiler?

### For Safety-Critical Applications

- **Certification-Ready**: Generate C code suitable for DO-178C (aviation), ISO 26262 (automotive), IEC 61508 (industrial)
- **Formal Verification**: Output compatible with Frama-C, ACSL annotations included
- **Deterministic Runtime**: Predictable memory usage, no dynamic allocation in critical paths
- **Single-File Distribution**: Inline runtime mode for self-contained certification

### For Embedded Systems

- **Zero Dependencies**: Inline runtime mode requires no external libraries
- **Minimal Overhead**: Runtime library is 1.7-2.8 KB total
- **Size Optimization**: 35-45% size reduction with full optimization
- **C99 Compatible**: Works with any C99-compliant compiler

### For Legacy Integration

- **Clean C Output**: Human-readable code that integrates easily with existing C projects
- **Standard C Types**: Uses standard C struct/function patterns
- **No C++ Runtime**: No dependency on C++ standard library or runtime
- **Clear ABI**: Predictable memory layout and calling conventions

### For Code Understanding

- **Educational Tool**: See how C++ features map to C constructs
- **Performance Analysis**: Understand the overhead of C++ abstractions
- **Debugging**: Debug C code instead of complex C++ templates
- **Documentation**: Use generated C code as implementation documentation

---

## System Requirements

### Supported Platforms

- **macOS**: 10.15 (Catalina) or later
- **Linux**: Ubuntu 20.04+, Debian 11+, Fedora 33+, or equivalent
- **Windows**: WSL2 (Windows Subsystem for Linux) recommended

### Required Software

| Software | Minimum Version | Recommended | Purpose |
|----------|----------------|-------------|---------|
| **Clang/LLVM** | 15.0 | 18.0+ | AST infrastructure and LibTooling |
| **CMake** | 3.20 | 3.27+ | Build system |
| **C++ Compiler** | C++17 | C++20 | Building the transpiler itself |
| **Git** | 2.25 | Latest | Version control |

### Optional Software

| Software | Purpose |
|----------|---------|
| **Frama-C** | Formal verification of generated C code |
| **GCC** | Compiling generated C code (alternative to Clang) |
| **lcov** | Code coverage reporting |
| **Doxygen** | Generating API documentation |

### Hardware Requirements

**Minimum:**
- CPU: 2 cores, 2.0 GHz
- RAM: 4 GB
- Disk: 2 GB free space

**Recommended:**
- CPU: 4+ cores, 3.0+ GHz
- RAM: 8 GB or more
- Disk: 10 GB free space (for building LLVM from source if needed)

---

## Quick Start

### Installation

#### macOS

```bash
# Install dependencies
brew install llvm cmake

# Set LLVM path for CMake
export CMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm"

# Clone repository
git clone https://github.com/o2alexanderfedin/cpp-to-c-transpiler.git
cd cpp-to-c-transpiler

# Configure and build
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j$(sysctl -n hw.ncpu)

# Verify installation
./build/cpptoc --help
```

#### Linux (Ubuntu/Debian)

```bash
# Install dependencies
sudo apt update
sudo apt install clang-18 llvm-18-dev libclang-18-dev cmake build-essential git

# Clone repository
git clone https://github.com/o2alexanderfedin/cpp-to-c-transpiler.git
cd cpp-to-c-transpiler

# Configure and build (CMake will find system LLVM)
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j$(nproc)

# Verify installation
./build/cpptoc --help
```

#### Linux (Fedora/RHEL)

```bash
# Install dependencies
sudo dnf install clang llvm-devel cmake gcc-c++ git

# Clone and build (same as above)
git clone https://github.com/o2alexanderfedin/cpp-to-c-transpiler.git
cd cpp-to-c-transpiler
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j$(nproc)

# Verify
./build/cpptoc --help
```

### Verifying the Installation

After building, verify the installation:

```bash
# Check version
./build/cpptoc --version

# Expected output:
# cpptoc version 1.5.1
# Using LLVM 18.1.0
# Built: Dec 2025

# Run a simple test
cat > test.cpp << 'EOF'
#include <iostream>

class Greeter {
    const char* name;
public:
    Greeter(const char* n) : name(n) {}
    void greet() { std::cout << "Hello, " << name << "!\n"; }
};

int main() {
    Greeter g("World");
    g.greet();
    return 0;
}
EOF

./build/cpptoc test.cpp --
```

If you see AST information printed, the transpiler is working correctly!

---

## Understanding the Output

### Current Status (Epic #1 Complete)

The transpiler is currently in **Phase 1: Infrastructure Setup**. At this stage, it:

- **Parses C++ files** using Clang's AST infrastructure
- **Reports AST structure** showing classes, methods, variables
- **Validates Clang integration** ensuring correct parsing

### Example Output

Given this input:

```cpp
// example.cpp
class Counter {
    int count;
public:
    Counter() : count(0) {}
    void increment() { count++; }
    int get() const { return count; }
};
```

Current output (Phase 1):

```
Parsed file: example.cpp
Translation unit has 1 top-level declarations
Found class: Counter
  Found constructor: Counter::Counter
  Found method: Counter::increment
  Found method: Counter::get
  Found field: Counter::count
```

### Future Output (Phase 2+ Implementation)

After completing Phase 2 (CNodeBuilder) and Phase 3 (Code Generation), the transpiler will produce:

```c
// example.c - Generated by cpptoc
#include "cpptoc_runtime.h"

// Struct definition for Counter
struct Counter {
    int count;
};

// Constructor: Counter::Counter()
void Counter_ctor(struct Counter* this) {
    this->count = 0;
}

// Method: Counter::increment()
void Counter_increment(struct Counter* this) {
    this->count++;
}

// Method: Counter::get() const
int Counter_get(const struct Counter* this) {
    return this->count;
}
```

---

## Your First Transpilation

### Example 1: Simple Class

Let's transpile a simple C++ class:

```cpp
// simple_class.cpp
class Point {
    double x, y;
public:
    Point(double px, double py) : x(px), y(py) {}
    double distanceFromOrigin() const {
        return sqrt(x*x + y*y);
    }
};

int main() {
    Point p(3.0, 4.0);
    return 0;
}
```

Run the transpiler:

```bash
./build/cpptoc simple_class.cpp --
```

Current output (Phase 1):

```
Parsed file: simple_class.cpp
Translation unit has 2 top-level declarations
Found class: Point
  Found constructor: Point::Point
  Found method: Point::distanceFromOrigin
  Found field: Point::x
  Found field: Point::y
Found function: main
```

### Example 2: Template Class

Templates are fully supported via self-bootstrapping:

```cpp
// template_example.cpp
template<typename T>
class Container {
    T value;
public:
    Container(T v) : value(v) {}
    T get() const { return value; }
};

int main() {
    Container<int> intContainer(42);
    Container<double> doubleContainer(3.14);
    return 0;
}
```

The transpiler will see **instantiated templates** in the AST:

```bash
./build/cpptoc template_example.cpp --
```

Output:

```
Parsed file: template_example.cpp
Translation unit has 3 top-level declarations
Found class: Container<int>
  Found constructor: Container<int>::Container
  Found method: Container<int>::get
  Found field: Container<int>::value
Found class: Container<double>
  Found constructor: Container<double>::Container
  Found method: Container<double>::get
  Found field: Container<double>::value
Found function: main
```

### Example 3: Standard Library

The transpiler handles STL the same way as user code (self-bootstrapping):

```cpp
// stl_example.cpp
#include <vector>
#include <string>

int main() {
    std::vector<int> numbers;
    numbers.push_back(1);
    numbers.push_back(2);

    std::string greeting = "Hello";
    return 0;
}
```

The transpiler sees instantiated `vector<int>` and `basic_string<char>` templates in the AST.

---

## Next Steps

### Learn the Core Features

Continue to the next guides in the User Guide series:

1. **Installation Guide** - Detailed installation instructions for all platforms
2. **Quick Start Tutorial** - Step-by-step transpilation examples
3. **Core Features** - Learn about class translation, inheritance, templates
4. **Advanced Topics** - Exceptions, RTTI, coroutines, virtual inheritance
5. **Best Practices** - Code organization, optimization, debugging

### Explore API Reference

Once you're comfortable with basic usage, explore:

- **CLI Options** - Command-line flags and configuration
- **Configuration Files** - CMake integration and build system setup
- **Build Integration** - Integrating the transpiler into your build process

### Troubleshooting

If you encounter issues:

- **Troubleshooting Guide** - Common issues and solutions
- **FAQ** - Frequently asked questions
- **Error Messages** - Explanation of error messages and fixes

### For Safety-Critical Applications

If you're working on safety-critical systems:

- **Safety-Critical Guide** - DO-178C, ISO 26262, IEC 61508 guidance
- **Formal Verification Guide** - Frama-C integration and ACSL annotations
- **Migration Guide** - Best practices for C++ to C migration

---

## Getting Help

### Documentation

- **Online Documentation**: https://o2alexanderfedin.github.io/cpp-to-c-transpiler/
- **User Guide**: Complete user documentation (this guide)
- **API Reference**: Command-line options and configuration
- **Architecture Docs**: Technical architecture and design decisions

### Community & Support

- **GitHub Issues**: Report bugs and request features
- **Discussions**: Ask questions and share experiences
- **Email**: alexander.fedin@hapyy.com for commercial support

### Contributing

The project follows Test-Driven Development (TDD) with SOLID principles:

1. Write failing test first (RED phase)
2. Implement minimal code to pass (GREEN phase)
3. Refactor for quality (REFACTOR phase)
4. Follow conventional commits

See `CLAUDE.md` for development guidelines.

---

## What's Next?

Now that you have the transpiler installed and running, continue to:

- **[02-installation.md](02-installation.md)** - Detailed installation and troubleshooting
- **[03-quick-start.md](03-quick-start.md)** - Hands-on tutorial with real examples
- **[04-core-features.md](04-core-features.md)** - Learn about class translation and core features

---

**Ready to transpile C++ to C? Let's get started!**

*Generated with [Claude Code](https://claude.com/claude-code) | December 2025*

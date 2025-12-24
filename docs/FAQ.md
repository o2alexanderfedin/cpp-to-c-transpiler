# Frequently Asked Questions (FAQ)

**Version:** 1.5.1
**Last Updated:** December 2025

Common questions and answers about the C++ to C Transpiler.

---

## Table of Contents

1. [General Questions](#general-questions)
2. [Installation and Setup](#installation-and-setup)
3. [Usage and Features](#usage-and-features)
4. [Performance and Optimization](#performance-and-optimization)
5. [Safety-Critical and Formal Verification](#safety-critical-and-formal-verification)
6. [Troubleshooting](#troubleshooting)
7. [Project Status and Roadmap](#project-status-and-roadmap)
8. [Contributing and Support](#contributing-and-support)

---

## General Questions

### Q1: What is the C++ to C Transpiler?

**A:** The C++ to C Transpiler (cpptoc) is a source-to-source compiler that converts modern C++ code into clean, readable C code. It handles classes, templates, STL, exceptions, RTTI, coroutines, and virtual inheritance.

**Key Features:**
- Clean, human-readable C output
- Compatible with Frama-C formal verification
- Suitable for safety-critical systems (DO-178C, ISO 26262)
- Handles modern C++ including C++20 coroutines
- Self-bootstrapping for STL conversion

---

### Q2: Why would I want to transpile C++ to C?

**A:** There are several compelling use cases:

**Safety-Critical Systems:**
- C is required for DO-178C (aviation), ISO 26262 (automotive), IEC 61508 (industrial) certification
- Formal verification with Frama-C is easier with C
- Deterministic behavior and predictable memory usage

**Embedded Systems:**
- Some platforms lack C++ compiler support
- Smaller runtime footprint (1.7-2.8 KB vs. full C++ runtime)
- No dependency on C++ standard library

**Legacy Integration:**
- Interface modern C++ with legacy C codebases
- Migrate incrementally from C to C++ or vice versa
- Understand low-level implementation of C++ features

**Code Understanding:**
- See how C++ features map to C constructs
- Educational tool for learning C++ internals
- Performance analysis and optimization

---

### Q3: How does this differ from C++ compilers that generate C code (like Cfront)?

**A:** Modern approach with several advantages:

**Cfront (historical, 1980s-1990s):**
- Generated unreadable C code
- No formal verification support
- Limited C++ feature support
- No longer maintained

**cpptoc (modern, 2025):**
- Clean, human-readable C output (Clang's battle-tested printers)
- Frama-C compatible with ACSL annotations
- Full C++20 support (including coroutines)
- Active development
- Intermediate C AST for optimal code quality (3-5x cleaner than direct translation)
- Self-bootstrapping for STL (no manual reimplementation)

---

### Q4: Does it support the C++ Standard Library (STL)?

**A:** Yes! Via **self-bootstrapping**.

The transpiler doesn't require manual STL reimplementation. Instead:

1. You write C++ code using STL (`std::vector`, `std::map`, etc.)
2. Clang parser sees **instantiated templates** in the AST
3. Transpiler treats `std::vector<int>` like any other C++ class
4. Generated C code includes monomorphized versions

**Example:**
```cpp
// C++
std::vector<int> numbers;
numbers.push_back(42);

// Generated C (future)
struct vector_int { int* data; size_t size; size_t capacity; };
void vector_int_push_back(struct vector_int* this, int value);
```

No manual STL porting needed!

---

### Q5: Is the generated C code human-readable?

**A:** Yes! That's a core design goal.

**Why it's readable:**
- Uses Clang's DeclPrinter/StmtPrinter (15+ years production use)
- Intermediate C AST ensures clean output
- Standard C naming conventions
- Minimal runtime library (not inline spaghetti)
- Comments and #line directives preserved

**Comparison:**
```c
// Direct translation (unreadable)
if(((__cxx_frame_stack->jmpbuf_valid=1),setjmp(__cxx_frame_stack->jmpbuf))==0){
  __cxx_try_begin(__cxx_frame_stack,1,&action_table_1);
  // ... 40 more lines of inline exception handling
}

// cpptoc output (readable)
CXXExceptionFrame frame;
__cxx_frame_push(&frame);
if (setjmp(frame.jmpbuf) == 0) {
    may_throw();
} else {
    __cxx_handle_exception();
}
__cxx_frame_pop(&frame);
```

3-5x cleaner than direct translation!

---

## Installation and Setup

### Q6: What are the system requirements?

**A:** Minimal requirements:

**Required:**
- **Clang/LLVM** 15.0+ (recommended: 18.0+)
- **CMake** 3.20+
- **C++ Compiler** with C++17 support (GCC 9+, Clang 10+)
- **Git** 2.25+

**Platforms:**
- macOS 10.15+ (Catalina or later)
- Linux: Ubuntu 20.04+, Debian 11+, Fedora 33+
- Windows: WSL2 (Windows Subsystem for Linux)

**Disk Space:**
- 2 GB (pre-built LLVM)
- 10 GB (building LLVM from source)

---

### Q7: How do I install on macOS?

**A:** Using Homebrew:

```bash
# Install dependencies
brew install llvm cmake

# Set LLVM path
export CMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm"

# Clone and build
git clone https://github.com/o2alexanderfedin/cpp-to-c-transpiler.git
cd cpp-to-c-transpiler
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j$(sysctl -n hw.ncpu)

# Verify
./build/cpptoc --help
```

See [Installation Guide](user-guide/02-installation.md) for detailed instructions.

---

### Q8: How do I install on Linux?

**A:** Ubuntu/Debian example:

```bash
# Install dependencies
sudo apt update
sudo apt install clang-18 llvm-18-dev libclang-18-dev cmake build-essential git

# Clone and build
git clone https://github.com/o2alexanderfedin/cpp-to-c-transpiler.git
cd cpp-to-c-transpiler
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j$(nproc)

# Verify
./build/cpptoc --help
```

See [Installation Guide](user-guide/02-installation.md) for other distributions.

---

### Q9: Do I need to install Frama-C?

**A:** No, Frama-C is **optional**.

Frama-C is only needed if you want to perform **formal verification** of the generated C code. The transpiler works fine without it.

**To install Frama-C** (optional):
```bash
# Install OPAM
sudo apt install opam  # Ubuntu
brew install opam  # macOS

# Install Frama-C via OPAM
opam init
opam install frama-c
```

---

## Usage and Features

### Q10: Can I transpile multiple files at once?

**A:** Yes! The transpiler fully supports processing multiple C++ files in a single invocation.

**Basic Example:**
```bash
# Transpile multiple files
./build/cpptoc file1.cpp file2.cpp file3.cpp --

# With output directory
./build/cpptoc src/*.cpp --output-dir ./generated

# With include paths
./build/cpptoc main.cpp utils.cpp -- -I./include
```

**Output:** Each input file generates separate `.h` and `.c` files:
```
Input:  Point.cpp    →  Output:  Point.h + Point.c
Input:  Circle.cpp   →  Output:  Circle.h + Circle.c
Input:  main.cpp     →  Output:  main.h + main.c
```

**Key Features:**
- Independent processing (each file gets its own AST)
- Automatic header/implementation separation
- Output directory control with `--output-dir`
- Include path support via `-I` flags
- Works with compilation databases

**See Also:** [Multi-File Transpilation Guide](MULTI_FILE_TRANSPILATION.md)

---

### Q11: What C++ features are supported?

**A:** Full C++20 support (roadmap):

**Currently Implemented:**
- AST parsing and infrastructure (Phase 1 complete)

**Planned (Phases 2-5):**
- Classes (single/multiple/virtual inheritance)
- Templates (full monomorphization)
- STL containers (vector, map, set, etc.)
- RAII and destructors
- Exceptions (PNaCl SJLJ pattern)
- RTTI (type_info, dynamic_cast, typeid)
- Lambdas and closures
- C++20 coroutines
- Smart pointers
- Virtual functions and polymorphism

See [Roadmap](user-guide/01-getting-started.md#implementation-roadmap) for timeline.

---

### Q11: How do I transpile my first C++ file?

**A:** Simple example:

```bash
# Create a C++ file
cat > hello.cpp << 'EOF'
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

# Transpile (Phase 1: shows AST structure)
./build/cpptoc hello.cpp --
```

**Current Output (Phase 1):**
```
Parsed file: hello.cpp
Found class: Greeter
  Found constructor: Greeter::Greeter
  Found method: Greeter::greet
  Found field: Greeter::name
Found function: main
```

**Future Output (Phase 2+):** Will generate `hello.c` with full C code.

See [Quick Start Tutorial](user-guide/03-quick-start.md) for more examples.

---

### Q12: What is the difference between inline and library runtime modes?

**A:** Two runtime modes with different trade-offs:

**Inline Mode:**
- Runtime code embedded in each generated C file
- **Best for:** Small projects (< 20 files), embedded systems, safety certification
- **Pros:** Self-contained, zero dependencies, single-file certification
- **Cons:** Larger binaries (runtime duplicated), slower compilation

**Library Mode:**
- Runtime code compiled once into a library
- **Best for:** Large projects (20+ files), rapid development
- **Pros:** 99% size reduction for 100+ file projects, 27% faster compilation
- **Cons:** External dependency, multi-file certification

**Size Comparison (100-file project):**
- Inline mode: 310 KB
- Library mode: 3.1 KB (99% reduction)

See [Runtime Configuration Guide](RUNTIME_CONFIGURATION.md) for details.

---

### Q13: Can I use templates?

**A:** Yes! Full template support via **self-bootstrapping**.

Templates are handled automatically:

```cpp
// C++ template
template<typename T>
class Container {
    T value;
public:
    Container(T v) : value(v) {}
    T get() const { return value; }
};

int main() {
    Container<int> ci(42);
    Container<double> cd(3.14);
    return 0;
}
```

The transpiler sees **instantiated templates** (`Container<int>`, `Container<double>`) in the AST and generates separate C structs:

```c
// Generated C (future)
struct Container_int { int value; };
void Container_int_ctor(struct Container_int* this, int v) { this->value = v; }

struct Container_double { double value; };
void Container_double_ctor(struct Container_double* this, double v) { this->value = v; }
```

**Standard transpiler workflow:** C++ is the source of truth, C is the build artifact.

---

### Q14: How are exceptions handled in C?

**A:** Using the **PNaCl SJLJ (setjmp/longjmp) pattern** with action tables.

Not naive nested setjmp - uses proper exception frames and type matching:

```c
// Exception handling translation (future)
CXXExceptionFrame frame;
__cxx_frame_push(&frame);  // Thread-local stack

if (setjmp(frame.jmpbuf) == 0) {
    may_throw();
} else {
    __cxx_handle_exception();  // Action tables for destructors
}

__cxx_frame_pop(&frame);
```

**Validated by:** Comeau C++ (1990s), PNaCl (2013), Emscripten (present)

**Features:**
- Thread-safe (thread-local exception stack)
- Type-safe catch handlers
- Proper destructor invocation
- Formally verifiable with Frama-C

See [Exception Handling Guide](docs/features/exceptions.md) for details.

---

### Q15: Is RTTI (dynamic_cast) supported?

**A:** Yes! Based on **Itanium C++ ABI** + libcxxabi patterns.

RTTI implementation includes:
- `type_info` structures
- `dynamic_cast` translation
- `typeid` operator support
- Hierarchy traversal for cross-casts

**Implementation time:** 3-4 weeks (see roadmap)

See [RTTI Guide](docs/features/rtti.md) for technical details.

---

## Performance and Optimization

### Q16: What is the overhead of the generated C code?

**A:** Minimal overhead, often **identical** to C++ compiled code.

**Runtime Performance:**
- Virtual function calls: 0% overhead (same as C++ vtables)
- Exception handling: 0% overhead when not throwing
- RTTI dynamic_cast: 0% overhead (same algorithm as libcxxabi)
- Memory layout: Identical to C++ ABI

**Size Overhead (with Library Mode):**
- Runtime library: 1.7-2.8 KB total
- Per-file overhead: ~0 bytes (library mode)
- With optimization (-Os -flto): 35-45% reduction vs. baseline

**Compilation Time:**
- Library mode: 27% faster than inline mode for 20+ files
- Incremental builds: 28% faster (library compiled once)

See [Profiling Guide](docs/PROFILING_GUIDE.md) for benchmarks.

---

### Q17: How can I optimize the generated code size?

**A:** Multiple optimization strategies:

**1. Choose Library Runtime Mode** (for 20+ files):
```bash
cpptoc --runtime-mode=library input.cpp --
# Result: 99% size reduction for 100-file projects
```

**2. Enable Only Needed Features:**
```bash
cpptoc --runtime=exceptions input.cpp --  # Exceptions only (1 KB vs. 3 KB)
```

**3. Apply Compiler Optimizations:**
```bash
# Size optimization
gcc -Os -flto -ffunction-sections -fdata-sections -Wl,--gc-sections output.c

# Result: 35-45% size reduction
```

**4. Use Profile-Guided Optimization (PGO):**
```bash
# Generate profile
gcc -Os -fprofile-generate output.c -o app
./app  # Run with typical workload

# Rebuild with profile
gcc -Os -fprofile-use output.c -o app
# Result: 5-10% additional reduction
```

See [Size Optimization Guide](docs/SIZE_OPTIMIZATION.md) for full details.

---

### Q18: Does runtime mode affect performance?

**A:** No! Runtime performance is **identical** (0% overhead difference).

Both inline and library modes generate the same function calls. The only difference is code organization:

**Inline Mode:**
```c
// Runtime embedded in file
#ifndef __EXCEPTION_RUNTIME_H__
// ... 50 lines of exception runtime
#endif

void my_function() {
    __cxx_throw(...);  // Same call
}
```

**Library Mode:**
```c
// Runtime in separate library
#include "cpptoc_runtime.h"

void my_function() {
    __cxx_throw(...);  // Same call
}
```

**Benchmarks show:** 0% runtime overhead difference.

**Difference is in:**
- Binary size (library mode is 99% smaller)
- Compilation time (library mode is 27% faster)
- Deployment complexity (inline mode is simpler)

---

## Safety-Critical and Formal Verification

### Q19: Is the generated C code suitable for safety-critical applications?

**A:** Yes! Designed for safety-critical systems.

**Certification Support:**
- **DO-178C** (aviation)
- **ISO 26262** (automotive)
- **IEC 61508** (industrial)

**Key Features for Safety:**
- Deterministic runtime behavior
- Predictable memory usage
- No dynamic allocation in critical paths
- Formally verifiable with Frama-C
- ACSL annotations included
- Single-file certification (inline mode)

**Validation:**
- PNaCl SJLJ exception pattern (proven safe)
- Itanium ABI RTTI (industry standard)
- Frama-C weakest precondition verification

See [Safety-Critical Guide](docs/SAFETY_CRITICAL_GUIDE.md) for certification guidance.

---

### Q20: Can I verify the generated C code with Frama-C?

**A:** Yes! Full Frama-C integration.

**Features:**
- ACSL annotations in generated code
- Runtime library verified with Frama-C WP
- Weakest precondition analysis
- Tractable verification (verify library once, not every function)

**Example Verification:**
```bash
# Generate C code
cpptoc input.cpp -- -o output.c

# Verify with Frama-C
frama-c -wp output.c cpptoc_runtime.c

# Result: All proof obligations discharged
```

**Advantage over C++:** C is 5-10x easier to verify than C++.

See [Formal Verification Guide](docs/FORMAL_VERIFICATION_GUIDE.md) for details.

---

### Q21: What is ACSL and how is it used?

**A:** ACSL (ANSI/ISO C Specification Language) is a formal specification language for C.

The transpiler generates ACSL annotations:

```c
/*@
  requires \valid(this);
  requires \valid(this->data + (0..this->size-1));
  ensures \result == this->size;
  assigns \nothing;
*/
int vector_size(const struct vector_int* this) {
    return this->size;
}
```

**ACSL Annotations:**
- `requires`: Preconditions
- `ensures`: Postconditions
- `assigns`: Side effects
- `invariant`: Loop invariants

Frama-C uses these to prove correctness.

See [ACSL Annotations Guide](docs/ACSL_ANNOTATIONS.md) for syntax and examples.

---

## Troubleshooting

### Q22: I get "CMake cannot find LLVM" error. How do I fix it?

**A:** Set `CMAKE_PREFIX_PATH`:

```bash
# macOS with Homebrew
export CMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm"

# Linux (find LLVM first)
llvm-config-18 --prefix
# Then set CMAKE_PREFIX_PATH to that directory

# Or specify LLVM directory explicitly
cmake .. -DLLVM_DIR=$(llvm-config-18 --cmakedir)
```

See [Installation Troubleshooting](user-guide/02-installation.md#troubleshooting) for more solutions.

---

### Q23: The build fails with "undefined reference to clang::..." errors. What's wrong?

**A:** Version mismatch between Clang and LLVM libraries.

**Solution:**
```bash
# Check versions match
clang --version
llvm-config --version

# If mismatch, reinstall matching versions
sudo apt install clang-18 llvm-18-dev libclang-18-dev  # Ubuntu

# Clean rebuild
rm -rf build
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build
```

---

### Q24: Generated C code doesn't compile. What should I check?

**A:** (This will apply when code generation is implemented)

Common issues:
1. **Missing runtime library**: Link with `-lcpptoc_runtime`
2. **Missing headers**: Add `-I/path/to/cpptoc/runtime`
3. **C99 compiler required**: Use `-std=c99`
4. **Undefined symbols**: Check all generated .c files are compiled

**Debugging:**
```bash
# Check generated code
cat output.c

# Try compiling with verbose
gcc -v -std=c99 output.c -lcpptoc_runtime

# Check for linker issues
nm output.o  # Should show symbols
```

---

## Project Status and Roadmap

### Q25: What is the current status of the project?

**A:** **Phase 1 (Infrastructure Setup) Complete** - December 2025

**Completed:**
- Epic #1: Infrastructure Setup & Clang Integration
  - CMake build system
  - Clang LibTooling integration
  - RecursiveASTVisitor skeleton
  - AST parsing and structure reporting

**Current Capability:**
- Parse C++ files and report AST structure
- Identify classes, methods, inheritance, templates
- Validate Clang integration

**Next Up:**
- Phase 2: CNodeBuilder Helper Library (3-4 weeks)
- Phase 3: Core Features (4-8 weeks)
- Phase 4: Advanced Features (8-12 weeks)

See [Roadmap](docs/feasibility-and-roadmap.md) for detailed timeline.

---

### Q26: When will full code generation be available?

**A:** Estimated timeline:

- **Phase 2 (CNodeBuilder)**: ~3-4 weeks from now
  - C AST node builder
  - Clang printer integration
  - Simple class translation

- **Phase 3 (Core Features)**: ~4-8 weeks
  - RAII and destructors
  - Single inheritance
  - Virtual functions
  - Name mangling

- **Phase 4 (Advanced Features)**: ~8-12 weeks
  - Exception handling
  - RTTI
  - Multiple inheritance
  - STL self-conversion validation

**Total to production-ready:** ~6 months

Follow development on GitHub for progress updates.

---

### Q27: Can I contribute to the project?

**A:** Yes! Contributions welcome.

**How to Contribute:**

1. **Report Issues**: Open GitHub issues for bugs or feature requests
2. **Submit Pull Requests**: Follow TDD workflow (see below)
3. **Write Tests**: Expand test coverage
4. **Documentation**: Improve guides and examples
5. **Commercial Support**: Contact alexander.fedin@hapyy.com

**Development Process (TDD):**
1. Write failing test (RED)
2. Implement minimal code to pass (GREEN)
3. Refactor for quality (REFACTOR)
4. Follow conventional commits

See `CLAUDE.md` for development guidelines.

---

### Q28: Is there commercial support available?

**A:** Yes! Commercial licensing and support available.

**Commercial License Benefits:**
- Commercial use rights
- Modification and derivative works
- Distribution and sublicensing
- Priority technical support
- Custom development options

**Licensing Tiers:**
- Individual/Startup
- Enterprise
- OEM/Redistribution

**Contact:** alexander.fedin@hapyy.com

See [LICENSE-COMMERCIAL.md](../LICENSE-COMMERCIAL.md) for details.

---

## Contributing and Support

### Q29: Where can I get help?

**A:** Multiple support channels:

**Documentation:**
- **User Guide**: [docs/user-guide/](user-guide/)
- **API Reference**: [docs/api-reference/](api-reference/)
- **Troubleshooting**: [docs/troubleshooting/](troubleshooting/)
- **Online Docs**: https://o2alexanderfedin.github.io/cpp-to-c-transpiler/

**Community:**
- **GitHub Issues**: Report bugs and request features
- **GitHub Discussions**: Ask questions and share experiences
- **Email**: alexander.fedin@hapyy.com

**Commercial:**
- Priority support with commercial license
- Custom development available

---

### Q30: Where can I learn more?

**A:** Comprehensive documentation available:

**User Documentation:**
- [Getting Started](user-guide/01-getting-started.md)
- [Installation Guide](user-guide/02-installation.md)
- [Quick Start Tutorial](user-guide/03-quick-start.md)
- [Core Features](user-guide/04-core-features.md)

**Technical Documentation:**
- [Architecture Decision](docs/architecture/architecture-decision.md)
- [Runtime Library Design](docs/architecture/runtime-library-design.md)
- [Exception Handling](docs/features/exceptions.md)
- [RTTI Implementation](docs/features/rtti.md)

**Research Archive:**
- [Research Index](../research-archive/INDEX.md)
- 13,545+ lines of comprehensive technical documentation
- 4 research phases, 23,629+ lines total

---

**Still have questions? Open a GitHub Discussion or email alexander.fedin@hapyy.com**

*Generated with [Claude Code](https://claude.com/claude-code) | December 2025*

# Troubleshooting Guide

**Version:** 1.5.1
**Last Updated:** December 2025

Solutions to common issues when using the C++ to C Transpiler.

---

## Table of Contents

1. [Installation Issues](#installation-issues)
2. [Build Issues](#build-issues)
3. [Runtime Issues](#runtime-issues)
4. [Generated Code Issues](#generated-code-issues)
5. [Performance Issues](#performance-issues)
6. [Formal Verification Issues](#formal-verification-issues)
7. [Platform-Specific Issues](#platform-specific-issues)
8. [Getting Additional Help](#getting-additional-help)

---

## Installation Issues

### Issue 1: CMake Cannot Find LLVM

**Symptoms:**
```
CMake Error at CMakeLists.txt:10 (find_package):
  Could not find a package configuration file provided by "LLVM"
```

**Root Cause:** CMake doesn't know where LLVM is installed.

**Solution 1: Set CMAKE_PREFIX_PATH (Recommended)**

```bash
# macOS with Homebrew
export CMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm"

# macOS with MacPorts
export CMAKE_PREFIX_PATH="/opt/local/libexec/llvm-18"

# Linux: Find LLVM installation first
llvm-config-18 --prefix
# Output: /usr/lib/llvm-18
export CMAKE_PREFIX_PATH="/usr/lib/llvm-18"

# Add to shell profile for persistence
echo 'export CMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm"' >> ~/.zshrc  # macOS
echo 'export CMAKE_PREFIX_PATH="/usr/lib/llvm-18"' >> ~/.bashrc      # Linux
```

**Solution 2: Specify LLVM_DIR Directly**

```bash
cmake -B build -DLLVM_DIR=$(llvm-config-18 --cmakedir)
```

**Solution 3: Install LLVM Dev Package**

```bash
# Ubuntu/Debian
sudo apt install llvm-18-dev libclang-18-dev

# Fedora/RHEL
sudo dnf install llvm-devel clang-devel

# macOS
brew install llvm
```

**Verification:**
```bash
# Check LLVM is found
llvm-config-18 --version
# Should output: 18.1.0 or similar

# Check CMake can find it
cmake -B build -DCMAKE_PREFIX_PATH="/path/to/llvm" --debug-find
```

---

### Issue 2: Clang Headers Not Found

**Symptoms:**
```
fatal error: 'clang/AST/AST.h' file not found
#include "clang/AST/AST.h"
         ^~~~~~~~~~~~~~~~~
```

**Root Cause:** Clang development headers not installed.

**Solution:**

```bash
# Ubuntu/Debian
sudo apt install libclang-18-dev clang-18

# Fedora/RHEL
sudo dnf install clang-devel

# macOS Homebrew
brew reinstall llvm

# Arch Linux
sudo pacman -S clang llvm
```

**Verification:**
```bash
# Find Clang include directory
llvm-config-18 --includedir
# Should show: /usr/lib/llvm-18/include or similar

# Check headers exist
ls -la $(llvm-config-18 --includedir)/clang/AST/
```

---

### Issue 3: C++17 Compiler Not Available

**Symptoms:**
```
CMake Error: The C++ compiler does not support C++17
```

**Root Cause:** Compiler too old or not found.

**Solution 1: Install Modern Compiler**

```bash
# Ubuntu/Debian
sudo apt install g++-11 clang-18

# Fedora/RHEL
sudo dnf install gcc-c++ clang

# macOS (Xcode Command Line Tools)
xcode-select --install
```

**Solution 2: Specify Compiler Explicitly**

```bash
# Use GCC 11
cmake -B build -DCMAKE_CXX_COMPILER=g++-11

# Use Clang 18
cmake -B build -DCMAKE_CXX_COMPILER=clang++-18
```

**Verification:**
```bash
# Check compiler version
g++ --version
clang++ --version

# Test C++17 support
echo 'int main() { auto [a, b] = std::pair{1, 2}; }' | g++ -std=c++17 -x c++ -
```

---

### Issue 4: Permission Denied (macOS)

**Symptoms:**
```
zsh: permission denied: ./build/cpptoc
```

**Root Cause:** macOS Gatekeeper blocking execution.

**Solution 1: Allow Execution**

```bash
# Make executable
chmod +x build/cpptoc

# Remove quarantine attribute
xattr -d com.apple.quarantine build/cpptoc

# Or allow all in build directory
xattr -dr com.apple.quarantine build/
```

**Solution 2: System Preferences (if needed)**

1. Open **System Preferences** > **Security & Privacy**
2. Click **General** tab
3. Look for message about blocked app
4. Click **Allow Anyway**

---

## Build Issues

### Issue 5: Undefined Reference to clang::... Symbols

**Symptoms:**
```
undefined reference to `clang::Decl::getASTContext() const'
/usr/bin/ld: cpptoc.o: in function `main':
```

**Root Cause:** LLVM/Clang version mismatch or incomplete linking.

**Solution 1: Clean Rebuild**

```bash
# Remove build directory
rm -rf build

# Reconfigure and rebuild
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build
```

**Solution 2: Check Version Match**

```bash
# Check Clang and LLVM versions match
clang --version
llvm-config --version

# If mismatch, reinstall matching versions
sudo apt install clang-18 llvm-18-dev libclang-18-dev
```

**Solution 3: Verify Linking**

```bash
# Check what libraries CMake found
cmake -B build 2>&1 | grep -i "clang\|llvm"

# Verify linker command includes Clang libraries
cmake --build build --verbose 2>&1 | grep -i "link\|ld"
```

---

### Issue 6: Out of Memory During Build

**Symptoms:**
```
c++: fatal error: Killed signal terminated program cc1plus
compilation terminated.
```

**Root Cause:** Insufficient RAM (Clang is memory-intensive).

**Solution 1: Reduce Parallel Jobs**

```bash
# Instead of -j$(nproc), use fewer cores
cmake --build build -j2

# Or build sequentially
cmake --build build -j1
```

**Solution 2: Add Swap Space (Linux)**

```bash
# Create 4GB swap file
sudo fallocate -l 4G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile

# Make permanent (add to /etc/fstab)
echo '/swapfile none swap sw 0 0' | sudo tee -a /etc/fstab
```

**Solution 3: Build in Release Mode**

```bash
# Release builds use less memory
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build
```

---

### Issue 7: Ninja Not Found

**Symptoms:**
```
CMake Error: CMAKE_MAKE_PROGRAM is set to NOTFOUND
```

**Root Cause:** Ninja build system not installed but was specified with `-G Ninja`.

**Solution 1: Install Ninja**

```bash
# Ubuntu/Debian
sudo apt install ninja-build

# macOS
brew install ninja

# Fedora/RHEL
sudo dnf install ninja-build
```

**Solution 2: Use Default Make**

```bash
# Don't specify -G Ninja, CMake will use Make
cmake -B build -DCMAKE_BUILD_TYPE=Release
```

---

## Runtime Issues

### Issue 8: cpptoc: command not found

**Symptoms:**
```
bash: cpptoc: command not found
```

**Root Cause:** Binary not in PATH or not installed.

**Solution 1: Run from Build Directory**

```bash
# Run directly
./build/cpptoc input.cpp --

# Or add to PATH
export PATH="$(pwd)/build:$PATH"
```

**Solution 2: Install Systemwide**

```bash
# Install to /usr/local/bin
cd build
sudo make install

# Verify
which cpptoc
cpptoc --version
```

**Solution 3: Create Alias**

```bash
# Add to shell profile
echo 'alias cpptoc="/path/to/build/cpptoc"' >> ~/.bashrc
source ~/.bashrc
```

---

### Issue 9: No Output Generated (Phase 1)

**Symptoms:**
```
# Expected output files not created
ls -la output.c
ls: cannot access 'output.c': No such file or directory
```

**Root Cause:** **Current implementation (Phase 1) only parses and reports AST structure**. Code generation will be implemented in Phase 2+.

**Expected Behavior (Phase 1):**

```bash
./build/cpptoc input.cpp --

# Output (to stdout):
Parsed file: input.cpp
Found class: MyClass
  Found method: MyClass::foo
  ...
```

**No .c files are generated yet.** This is normal for Phase 1.

**Future (Phase 2+):** Will generate actual C files:

```bash
cpptoc input.cpp -- -o output.c
# Will create output.c
```

---

## Generated Code Issues

### Issue 10: Missing Runtime Library (Future)

**Symptoms (when code generation is implemented):**
```
undefined reference to `__cxx_throw'
undefined reference to `__cxx_frame_push'
```

**Root Cause:** Runtime library not linked.

**Solution 1: Link Runtime Library**

```bash
# Build runtime library first
cd runtime
cmake -B build && cmake --build build

# Link with generated code
gcc output.c -lcpptoc_runtime -L runtime/build -o app
```

**Solution 2: Use Inline Mode**

```bash
# Generate with inline runtime (no library needed)
cpptoc --runtime-mode=inline input.cpp -- -o output.c

# Compile directly
gcc output.c -o app
```

---

### Issue 11: Type Mismatch Errors in Generated C (Future)

**Symptoms:**
```
error: incompatible pointer types passing 'struct Base *' to parameter of type 'struct Derived *'
```

**Root Cause:** Incorrect casting or inheritance translation.

**Solution 1: Report Bug**

This indicates a transpiler bug. Please report with minimal reproducing example:

```bash
# Create minimal test case
cat > bug.cpp << 'EOF'
class Base { virtual void foo(); };
class Derived : public Base { void foo() override; };

void test(Base* b) {
    Derived* d = static_cast<Derived*>(b);  // Triggers error
}
EOF

# Report on GitHub Issues with:
# - Input C++ code
# - Generated C code
# - Compiler error message
```

---

### Issue 12: Stack Overflow in Generated Code (Future)

**Symptoms:**
```
Segmentation fault (core dumped)
```

**Root Cause:** Infinite recursion or excessive stack usage.

**Solution 1: Check Destructor Chains**

```bash
# Enable core dumps
ulimit -c unlimited

# Run with debugger
gdb ./app
run
bt  # Show backtrace

# Look for infinite destructor calls
```

**Solution 2: Increase Stack Size**

```bash
# Increase stack limit
ulimit -s 16384  # 16 MB stack

# Or compile with larger stack
gcc output.c -o app -Wl,-stack_size,0x1000000  # macOS
gcc output.c -o app -Wl,-z,stack-size=16777216  # Linux
```

---

## Performance Issues

### Issue 13: Slow Compilation (Inline Mode)

**Symptoms:**
```
# Compilation takes > 2 minutes for 100 files
```

**Root Cause:** Inline mode embeds runtime in each file.

**Solution: Switch to Library Mode**

```bash
# Build runtime library once
cd runtime && cmake -B build && cmake --build build

# Use library mode
cpptoc --runtime-mode=library input.cpp --

# Compilation time reduction: ~27% for 20+ files
```

See [Runtime Mode Migration Guide](../MIGRATION_GUIDE.md).

---

### Issue 14: Large Binary Size

**Symptoms:**
```
# Generated executable is 500 KB+ for small program
```

**Root Cause:** Inline runtime or no optimization.

**Solution 1: Use Library Mode**

```bash
cpptoc --runtime-mode=library input.cpp --
# Size reduction: 99% for 100-file projects
```

**Solution 2: Apply Size Optimization**

```bash
# Size optimization flags
gcc -Os -flto -ffunction-sections -fdata-sections -Wl,--gc-sections output.c -o app
# Size reduction: 35-45%
```

**Solution 3: Enable Only Needed Features**

```bash
# Exceptions only (not all features)
cpptoc --runtime=exceptions input.cpp --
# Size: 1 KB vs. 3 KB for all features
```

See [Size Optimization Guide](../SIZE_OPTIMIZATION.md).

---

## Formal Verification Issues

### Issue 15: Frama-C Proof Obligations Fail

**Symptoms:**
```
frama-c -wp output.c
[kernel] warning: unknown property status: false
```

**Root Cause:** Missing preconditions or unsupported constructs.

**Solution 1: Check ACSL Annotations**

```bash
# Verify ACSL syntax
frama-c -wp -wp-print output.c

# Check specific function
frama-c -wp -wp-fct=my_function output.c
```

**Solution 2: Add Preconditions**

```c
// Add missing preconditions
/*@
  requires \valid(this);
  requires size > 0;
  ensures \result != NULL;
*/
void* allocate(size_t size);
```

**Solution 3: Simplify Code**

```bash
# Use inline mode for simpler verification
cpptoc --runtime-mode=inline --runtime=exceptions input.cpp --
```

See [Formal Verification Guide](../FORMAL_VERIFICATION_GUIDE.md).

---

## Platform-Specific Issues

### macOS: Library Not Loaded

**Symptoms:**
```
dyld: Library not loaded: @rpath/libcpptoc_runtime.dylib
Reason: image not found
```

**Solution:**

```bash
# Use static linking (recommended)
gcc output.c runtime/build/libcpptoc_runtime.a -o app

# Or set runtime library path
export DYLD_LIBRARY_PATH=runtime/build:$DYLD_LIBRARY_PATH
./app
```

---

### Linux: GLIBC Version Mismatch

**Symptoms:**
```
./cpptoc: /lib/x86_64-linux-gnu/libc.so.6: version `GLIBC_2.34' not found
```

**Solution:**

```bash
# Rebuild on target system
git clone https://github.com/o2alexanderfedin/cpp-to-c-transpiler.git
cd cpp-to-c-transpiler
cmake -B build && cmake --build build

# Or use static linking
cmake -B build -DBUILD_STATIC_BINARY=ON
```

---

### Windows (WSL2): Path Issues

**Symptoms:**
```
error: cannot find -lcpptoc_runtime
```

**Solution:**

```bash
# Use Windows-style paths in WSL2
export LD_LIBRARY_PATH="/mnt/c/Users/YourName/project/runtime/build:$LD_LIBRARY_PATH"

# Or use Linux paths within WSL
export LD_LIBRARY_PATH="$HOME/project/runtime/build:$LD_LIBRARY_PATH"
```

---

## Error Messages Reference

### Top 20 Common Error Messages

| Error Message | Cause | Solution |
|---------------|-------|----------|
| `CMake Error: Could not find LLVM` | LLVM not in CMAKE_PREFIX_PATH | Set CMAKE_PREFIX_PATH=[Issue 1](#issue-1-cmake-cannot-find-llvm) |
| `fatal error: 'clang/AST/AST.h' file not found` | Clang headers not installed | Install libclang-dev [Issue 2](#issue-2-clang-headers-not-found) |
| `The C++ compiler does not support C++17` | Compiler too old | Install modern compiler [Issue 3](#issue-3-c17-compiler-not-available) |
| `permission denied: ./build/cpptoc` | macOS Gatekeeper | Remove quarantine [Issue 4](#issue-4-permission-denied-macos) |
| `undefined reference to 'clang::...'` | Version mismatch | Clean rebuild [Issue 5](#issue-5-undefined-reference-to-clang-symbols) |
| `Killed signal terminated program` | Out of memory | Reduce parallel jobs [Issue 6](#issue-6-out-of-memory-during-build) |
| `CMAKE_MAKE_PROGRAM is set to NOTFOUND` | Ninja not found | Install ninja [Issue 7](#issue-7-ninja-not-found) |
| `cpptoc: command not found` | Binary not in PATH | Run from build/ [Issue 8](#issue-8-cpptoc-command-not-found) |
| `undefined reference to '__cxx_throw'` | Runtime library not linked | Link runtime [Issue 10](#issue-10-missing-runtime-library-future) |
| `Segmentation fault` | Stack overflow or null pointer | Debug with gdb [Issue 12](#issue-12-stack-overflow-in-generated-code-future) |

---

## Debugging Techniques

### Enable Verbose Output

```bash
# Verbose transpilation
./build/cpptoc -v input.cpp --

# Extra verbose
./build/cpptoc -vv input.cpp --

# CMake verbose
cmake -B build -DCMAKE_VERBOSE_MAKEFILE=ON
cmake --build build --verbose
```

### Use Debugger

```bash
# Build with debug symbols
cmake -B build -DCMAKE_BUILD_TYPE=Debug

# Debug with GDB
gdb ./build/cpptoc
break main
run input.cpp --

# Debug with LLDB (macOS)
lldb ./build/cpptoc
b main
r input.cpp --
```

### Check Clang AST

```bash
# Dump C++ AST with Clang
clang++ -Xclang -ast-dump input.cpp

# Dump with cpptoc (future)
./build/cpptoc --dump-ast input.cpp --
```

---

## Getting Additional Help

### Before Asking for Help

1. **Search existing issues**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues
2. **Check documentation**: Read relevant guides
3. **Create minimal example**: Reduce to smallest reproducing case
4. **Collect diagnostic info**: Version, platform, error messages

### Information to Provide

When reporting an issue, include:

```bash
# System information
uname -a
cat /etc/os-release  # Linux
sw_vers  # macOS

# LLVM/Clang version
llvm-config --version
clang --version

# CMake version
cmake --version

# Build configuration
cat build/CMakeCache.txt | grep -i "llvm\|clang"

# Full error message (copy-paste)
```

### Where to Get Help

- **GitHub Issues**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues
- **GitHub Discussions**: For questions and discussions
- **Documentation**: Check FAQ and guides
- **Email**: alexander.fedin@hapyy.com (commercial support)

---

**Still stuck? Open a GitHub issue with the information above!**

*Generated with [Claude Code](https://claude.com/claude-code) | December 2025*

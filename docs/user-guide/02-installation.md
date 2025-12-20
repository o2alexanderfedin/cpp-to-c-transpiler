# Installation Guide

**Version:** 1.5.1
**Last Updated:** December 2025

Complete installation instructions for the C++ to C Transpiler on all supported platforms.

---

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Platform-Specific Installation](#platform-specific-installation)
3. [Building from Source](#building-from-source)
4. [Verification](#verification)
5. [Troubleshooting](#troubleshooting)
6. [Optional Components](#optional-components)
7. [Uninstallation](#uninstallation)

---

## Prerequisites

### Required Dependencies

| Component | Minimum Version | Recommended | Installation |
|-----------|----------------|-------------|--------------|
| **Clang/LLVM** | 15.0 | 18.0+ | Package manager or source |
| **CMake** | 3.20 | 3.27+ | Package manager |
| **C++ Compiler** | C++17 | C++20 | GCC 9+ or Clang 10+ |
| **Git** | 2.25 | Latest | Package manager |

### Optional Dependencies

| Component | Purpose | Installation |
|-----------|---------|--------------|
| **Frama-C** | Formal verification | `opam install frama-c` |
| **lcov** | Code coverage | Package manager |
| **Doxygen** | Documentation | Package manager |
| **Graphviz** | Visualization | Package manager |

---

## Platform-Specific Installation

### macOS

#### Using Homebrew (Recommended)

```bash
# Update Homebrew
brew update

# Install dependencies
brew install llvm cmake git

# IMPORTANT: Set LLVM path for CMake
export CMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm"

# Add to shell profile for persistence
echo 'export CMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm"' >> ~/.zshrc
source ~/.zshrc
```

#### Using MacPorts

```bash
# Install dependencies
sudo port install llvm-18 cmake git

# Set LLVM path
export CMAKE_PREFIX_PATH="/opt/local/libexec/llvm-18"
```

#### Verify LLVM Installation

```bash
# Check LLVM version
llvm-config --version

# Expected output: 18.1.0 or similar

# Check Clang version
clang++ --version

# Expected output: clang version 18.1.0
```

### Linux - Ubuntu/Debian

#### Ubuntu 24.04 (Noble) or Debian 12 (Bookworm)

```bash
# Update package list
sudo apt update

# Install LLVM 18 (recommended)
sudo apt install clang-18 llvm-18-dev libclang-18-dev \
                 cmake build-essential git

# Install additional development tools
sudo apt install ninja-build ccache

# Optional: Set clang-18 as default (if you have multiple versions)
sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-18 100
sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-18 100
```

#### Ubuntu 22.04 (Jammy) or Debian 11 (Bullseye)

```bash
# Add LLVM APT repository
wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key | sudo apt-key add -
sudo add-apt-repository "deb http://apt.llvm.org/jammy/ llvm-toolchain-jammy-18 main"

# Update and install
sudo apt update
sudo apt install clang-18 llvm-18-dev libclang-18-dev cmake build-essential git
```

#### Verify Installation

```bash
# Check installations
clang-18 --version
llvm-config-18 --version
cmake --version

# Set environment variables if needed
export LLVM_DIR=$(llvm-config-18 --cmakedir)
```

### Linux - Fedora/RHEL/CentOS

#### Fedora 39+

```bash
# Install dependencies
sudo dnf install clang llvm-devel clang-devel \
                 cmake gcc-c++ git ninja-build

# Install additional tools
sudo dnf install ccache
```

#### RHEL 9/CentOS Stream 9

```bash
# Enable Code Ready Builder repository (for development tools)
sudo dnf install epel-release
sudo dnf config-manager --set-enabled crb

# Install dependencies
sudo dnf install clang llvm-devel clang-devel cmake gcc-c++ git
```

### Linux - Arch Linux

```bash
# Install dependencies (Arch has latest LLVM in repos)
sudo pacman -S llvm clang cmake ninja git

# Optional development tools
sudo pacman -S ccache gdb
```

### Windows (WSL2 Recommended)

#### Using WSL2 (Windows Subsystem for Linux)

```bash
# Install WSL2 (Windows PowerShell as Administrator)
wsl --install

# Or install specific distribution
wsl --install -d Ubuntu-24.04

# Inside WSL2, follow Ubuntu installation instructions above
```

#### Native Windows (MinGW-w64 + MSYS2)

```bash
# Install MSYS2 from https://www.msys2.org/

# In MSYS2 terminal:
pacman -S mingw-w64-x86_64-clang \
          mingw-w64-x86_64-llvm \
          mingw-w64-x86_64-cmake \
          mingw-w64-x86_64-ninja \
          git

# Set environment
export PATH="/mingw64/bin:$PATH"
```

**Note**: WSL2 is strongly recommended over native Windows for better LLVM compatibility.

---

## Building from Source

### Clone the Repository

```bash
# Clone from GitHub
git clone https://github.com/o2alexanderfedin/cpp-to-c-transpiler.git
cd cpp-to-c-transpiler

# Or clone via SSH
git clone git@github.com:o2alexanderfedin/cpp-to-c-transpiler.git
cd cpp-to-c-transpiler
```

### Configure Build

#### Standard Configuration

```bash
# Create build directory
mkdir -p build
cd build

# Configure with CMake
cmake .. -DCMAKE_BUILD_TYPE=Release

# macOS: If LLVM not found, set CMAKE_PREFIX_PATH
cmake .. -DCMAKE_BUILD_TYPE=Release \
         -DCMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm"
```

#### Advanced Configuration Options

```bash
# Use Ninja build system (faster)
cmake .. -G Ninja -DCMAKE_BUILD_TYPE=Release

# Enable optimization and LTO
cmake .. -DCMAKE_BUILD_TYPE=Release \
         -DCMAKE_INTERPROCEDURAL_OPTIMIZATION=ON

# Custom install prefix
cmake .. -DCMAKE_BUILD_TYPE=Release \
         -DCMAKE_INSTALL_PREFIX=/opt/cpptoc

# Enable testing
cmake .. -DCMAKE_BUILD_TYPE=Debug \
         -DENABLE_TESTING=ON

# Enable code coverage
cmake .. -DCMAKE_BUILD_TYPE=Debug \
         -DENABLE_COVERAGE=ON
```

### Build the Project

```bash
# Build with make
make -j$(nproc)  # Linux
make -j$(sysctl -n hw.ncpu)  # macOS

# Or with Ninja (if configured with -G Ninja)
ninja

# Or with CMake wrapper (works with any generator)
cmake --build . -j4
```

### Install (Optional)

```bash
# Install to system directories (requires sudo)
sudo make install

# Or to custom prefix
cmake .. -DCMAKE_INSTALL_PREFIX=$HOME/.local
make install

# Verify installation
cpptoc --version
```

---

## Verification

### Quick Verification Test

```bash
# Test 1: Check executable exists
ls -lh build/cpptoc

# Test 2: Run help
./build/cpptoc --help

# Test 3: Parse a simple C++ file
cat > /tmp/test.cpp << 'EOF'
class Test {
    int value;
public:
    Test(int v) : value(v) {}
    int getValue() const { return value; }
};

int main() {
    Test t(42);
    return t.getValue();
}
EOF

./build/cpptoc /tmp/test.cpp --

# Expected: AST structure printed, no errors
```

### Run Test Suite

```bash
# Build tests
cmake --build build --target all

# Run unit tests
cd build
./CppToCVisitorTest
./NameManglerTest
# ... run other tests

# Or run all tests with CTest (if enabled)
ctest --output-on-failure
```

### Check Dependencies

```bash
# Check LLVM libraries
ldd build/cpptoc | grep LLVM  # Linux
otool -L build/cpptoc | grep LLVM  # macOS

# Check Clang libraries
ldd build/cpptoc | grep clang  # Linux
otool -L build/cpptoc | grep clang  # macOS
```

---

## Troubleshooting

### Issue 1: CMake Cannot Find LLVM

**Symptoms:**
```
CMake Error: Could not find LLVM
```

**Solution 1**: Set `CMAKE_PREFIX_PATH`

```bash
# macOS with Homebrew
export CMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm"

# macOS with MacPorts
export CMAKE_PREFIX_PATH="/opt/local/libexec/llvm-18"

# Linux: Find LLVM installation
llvm-config-18 --prefix
# Then set CMAKE_PREFIX_PATH to that directory
```

**Solution 2**: Specify LLVM directory explicitly

```bash
cmake .. -DLLVM_DIR=$(llvm-config-18 --cmakedir)
```

### Issue 2: Clang Headers Not Found

**Symptoms:**
```
fatal error: 'clang/AST/AST.h' file not found
```

**Solution**: Install development headers

```bash
# Ubuntu/Debian
sudo apt install libclang-18-dev

# Fedora/RHEL
sudo dnf install clang-devel

# macOS Homebrew
brew reinstall llvm
```

### Issue 3: C++17 Compiler Required

**Symptoms:**
```
CMake Error: The C++ compiler does not support C++17
```

**Solution**: Upgrade compiler or specify newer compiler

```bash
# Ubuntu/Debian
sudo apt install g++-11

# Set compiler explicitly
cmake .. -DCMAKE_CXX_COMPILER=g++-11

# Or use Clang
cmake .. -DCMAKE_CXX_COMPILER=clang++-18
```

### Issue 4: Ninja Not Found

**Symptoms:**
```
CMake Error: CMAKE_MAKE_PROGRAM not found
```

**Solution**: Install Ninja or use default Make

```bash
# Install Ninja
sudo apt install ninja-build  # Ubuntu
brew install ninja  # macOS

# Or configure without Ninja
cmake .. -DCMAKE_BUILD_TYPE=Release  # Uses Make by default
```

### Issue 5: Linker Errors

**Symptoms:**
```
undefined reference to `clang::Decl::getASTContext()'
```

**Solution 1**: Clean rebuild

```bash
rm -rf build
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
make -j$(nproc)
```

**Solution 2**: Check LLVM/Clang version mismatch

```bash
# Ensure clang and llvm-dev versions match
clang --version
llvm-config --version

# If mismatch, reinstall matching versions
```

### Issue 6: Permission Denied on macOS

**Symptoms:**
```
Permission denied: build/cpptoc
```

**Solution**: macOS Gatekeeper issue

```bash
# Allow execution
chmod +x build/cpptoc

# If Gatekeeper blocks
xattr -d com.apple.quarantine build/cpptoc

# Or allow in System Preferences > Security & Privacy
```

### Issue 7: Out of Memory During Build

**Symptoms:**
```
c++: fatal error: Killed signal terminated program cc1plus
```

**Solution**: Reduce parallel jobs

```bash
# Use fewer cores
make -j2  # Instead of -j$(nproc)

# Or add swap space (Linux)
sudo fallocate -l 4G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile
```

---

## Optional Components

### Install Frama-C (For Formal Verification)

#### Using OPAM (Recommended)

```bash
# Install OPAM
sudo apt install opam  # Ubuntu
brew install opam  # macOS

# Initialize OPAM
opam init
eval $(opam env)

# Install Frama-C
opam install frama-c

# Verify
frama-c -version
```

### Install Code Coverage Tools

```bash
# Ubuntu/Debian
sudo apt install lcov

# macOS
brew install lcov

# Fedora
sudo dnf install lcov
```

### Install Documentation Tools

```bash
# Ubuntu/Debian
sudo apt install doxygen graphviz

# macOS
brew install doxygen graphviz

# Generate documentation
cd docs
doxygen Doxyfile
```

---

## Uninstallation

### Remove Installed Binaries

```bash
# If installed with 'make install'
sudo make uninstall  # In build directory

# Or manually remove
sudo rm /usr/local/bin/cpptoc
sudo rm -rf /usr/local/include/cpptoc
sudo rm /usr/local/lib/libcpptoc_runtime.a
```

### Remove Build Artifacts

```bash
# Remove build directory
cd cpp-to-c-transpiler
rm -rf build

# Remove repository (if desired)
cd ..
rm -rf cpp-to-c-transpiler
```

### Remove Dependencies (Optional)

```bash
# Ubuntu/Debian
sudo apt remove llvm-18-dev libclang-18-dev

# macOS
brew uninstall llvm

# This will NOT remove other packages that depend on LLVM
```

---

## Next Steps

After successful installation, continue to:

- **[03-quick-start.md](03-quick-start.md)** - Hands-on tutorial with examples
- **[04-core-features.md](04-core-features.md)** - Learn core transpilation features
- **API Reference** - Command-line options and configuration

---

## Getting Help

If you encounter installation issues not covered here:

1. Check **[Troubleshooting Guide](../troubleshooting/common-issues.md)**
2. Search **GitHub Issues**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues
3. Open a new issue with:
   - Platform and version (e.g., Ubuntu 24.04)
   - LLVM version (`llvm-config --version`)
   - CMake version (`cmake --version`)
   - Full error message
   - CMake configuration command used

---

**Installation complete? Let's start transpiling!**

*Generated with [Claude Code](https://claude.com/claude-code) | December 2025*

# LLVM/Clang Build Configuration Guide

## Problem Summary

**Root Cause:** LLVM is not installed on the system, causing CMake to fail with:
```
CMake Error at CMakeLists.txt:10 (find_package):
  Could not find a package configuration file provided by "LLVM" with any of
  the following names:
    LLVMConfig.cmake
    llvm-config.cmake
```

## System Information

- **Platform:** macOS (Darwin 24.5.0)
- **Architecture:** Apple Silicon (expected)
- **Project:** C++ to C Transpiler using Clang LibTooling
- **Required:** LLVM/Clang 15+ with development files

## Investigation Results

### What Was Checked

1. **Homebrew LLVM**: Not installed (confirmed via `brew list --formula | grep llvm`)
2. **System LLVM**: No LLVMConfig.cmake found in standard locations (/usr, /Library, /opt)
3. **Xcode Toolchain**: Not checked (Xcode Command Line Tools may not include LibTooling headers)
4. **CMakeLists.txt Analysis**: Requires both `find_package(LLVM REQUIRED CONFIG)` and `find_package(Clang REQUIRED CONFIG)`

### Why This Matters

The project requires **full LLVM development libraries**, not just the compiler:
- LLVMConfig.cmake - CMake configuration
- Clang LibTooling headers (RecursiveASTVisitor, FrontendAction, etc.)
- Clang libraries (clangTooling, clangFrontend, clangAST, clangBasic)
- LLVM libraries and headers

Apple's bundled clang/LLVM (in Xcode) typically **does not include** these development files.

## Solution: Install LLVM via Homebrew

### Step 1: Verify Homebrew is Installed

```bash
brew --version
```

If not installed, install Homebrew first:
```bash
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
```

### Step 2: Install LLVM

```bash
# Install LLVM (this will take 5-15 minutes)
brew install llvm

# Verify installation
brew list llvm
```

### Step 3: Find LLVM Installation Path

```bash
# Get LLVM prefix
brew --prefix llvm
```

Expected output (Apple Silicon):
```
/opt/homebrew/opt/llvm
```

Expected output (Intel Mac):
```
/usr/local/opt/llvm
```

### Step 4: Verify LLVMConfig.cmake Exists

```bash
# Check for config file
ls $(brew --prefix llvm)/lib/cmake/llvm/LLVMConfig.cmake
```

You should see the file path printed. This confirms LLVM is properly installed.

## Building the Project

### Option 1: Set CMAKE_PREFIX_PATH (Recommended)

```bash
# Navigate to project root
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c

# Set CMAKE_PREFIX_PATH and configure
export CMAKE_PREFIX_PATH="$(brew --prefix llvm)"
cmake -B build -DCMAKE_BUILD_TYPE=Debug

# Build
cmake --build build

# Test the build
./build/cpptoc --version
```

### Option 2: Set LLVM_DIR Directly

```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c

# Configure with explicit LLVM_DIR
cmake -B build \
  -DCMAKE_BUILD_TYPE=Debug \
  -DLLVM_DIR="$(brew --prefix llvm)/lib/cmake/llvm" \
  -DClang_DIR="$(brew --prefix llvm)/lib/cmake/clang"

# Build
cmake --build build
```

### Option 3: Permanent Environment Variable

Add to your `~/.zshrc` or `~/.bash_profile`:

```bash
# Add LLVM to CMAKE_PREFIX_PATH
export CMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm:$CMAKE_PREFIX_PATH"
```

Then reload your shell:
```bash
source ~/.zshrc  # or source ~/.bash_profile
```

## Building RuntimeModeInlineTest Specifically

Once LLVM is configured, build the specific test:

```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c

# Configure (if not already done)
export CMAKE_PREFIX_PATH="$(brew --prefix llvm)"
cmake -B build -DCMAKE_BUILD_TYPE=Debug

# Build just RuntimeModeInlineTest
cmake --build build --target RuntimeModeInlineTest

# Run the test
./build/RuntimeModeInlineTest
```

## Verification Steps

After installation, verify everything works:

```bash
# 1. Check LLVM version
$(brew --prefix llvm)/bin/llvm-config --version

# 2. Check CMake can find LLVM
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c
export CMAKE_PREFIX_PATH="$(brew --prefix llvm)"
cmake -B build -DCMAKE_BUILD_TYPE=Debug

# Expected output should include:
# -- Found LLVM: ...
# -- Found Clang: ...

# 3. Build all targets
cmake --build build

# 4. Verify executables exist
ls -lh build/cpptoc
ls -lh build/RuntimeModeInlineTest
```

## Troubleshooting

### Issue: "brew: command not found"

**Solution:** Install Homebrew:
```bash
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
```

### Issue: "Could not find a package configuration file provided by LLVM"

**Solution:** Ensure CMAKE_PREFIX_PATH is set:
```bash
export CMAKE_PREFIX_PATH="$(brew --prefix llvm)"
```

### Issue: "ld: library not found for -lclangTooling"

**Solution:** The linker can't find Clang libraries. Add to CMake command:
```bash
cmake -B build \
  -DCMAKE_PREFIX_PATH="$(brew --prefix llvm)" \
  -DCMAKE_CXX_FLAGS="-L$(brew --prefix llvm)/lib"
```

### Issue: Compilation fails with "fatal error: 'clang/AST/RecursiveASTVisitor.h' file not found"

**Solution:** Headers aren't in include path. This shouldn't happen with proper CMake configuration, but if it does:
```bash
export CPLUS_INCLUDE_PATH="$(brew --prefix llvm)/include:$CPLUS_INCLUDE_PATH"
```

### Issue: Wrong LLVM version (too old)

Check version:
```bash
$(brew --prefix llvm)/bin/llvm-config --version
```

If < 15.0, update:
```bash
brew upgrade llvm
```

## Why Homebrew LLVM?

1. **Complete Package**: Includes all development files (headers, CMake configs, libraries)
2. **Known Location**: Consistent installation path
3. **Version Control**: Can install specific versions if needed
4. **Updates**: Easy to keep up-to-date with `brew upgrade llvm`
5. **Compatibility**: Tested and working configuration for LibTooling projects

## Alternative: Building LLVM from Source

If you cannot use Homebrew, you can build LLVM from source:

```bash
# This takes 1-3 hours and requires 20+ GB disk space
git clone --depth 1 --branch llvmorg-17.0.6 https://github.com/llvm/llvm-project.git
cd llvm-project
cmake -B build -S llvm \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_PROJECTS="clang" \
  -DCMAKE_INSTALL_PREFIX=/usr/local/llvm-17
cmake --build build -j$(sysctl -n hw.ncpu)
sudo cmake --install build
```

Then use:
```bash
export CMAKE_PREFIX_PATH="/usr/local/llvm-17"
```

## Expected Build Output

After successful configuration, CMake should output:

```
-- The C compiler identification is AppleClang X.X.X
-- The CXX compiler identification is AppleClang X.X.X
-- Found LLVM 17.0.6
-- Using LLVMConfig.cmake in: /opt/homebrew/opt/llvm/lib/cmake/llvm
-- Found Clang: /opt/homebrew/opt/llvm/lib/cmake/clang
-- Configuring done
-- Generating done
-- Build files have been written to: .../hupyy-cpp-to-c/build
```

Build should complete with:

```
[100%] Linking CXX executable cpptoc
[100%] Built target cpptoc
[100%] Linking CXX executable RuntimeModeInlineTest
[100%] Built target RuntimeModeInlineTest
```

## Summary of Required Actions

Due to environment limitations during automated setup, **manual installation is required**:

1. **Open a terminal** (not through this tool)
2. **Install LLVM**: `brew install llvm`
3. **Configure CMake**:
   ```bash
   cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c
   export CMAKE_PREFIX_PATH="$(brew --prefix llvm)"
   cmake -B build -DCMAKE_BUILD_TYPE=Debug
   ```
4. **Build**: `cmake --build build`
5. **Verify**: `./build/RuntimeModeInlineTest`

## Documentation References

- **Project README**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/README.md` (lines 266-321)
- **Clang LibTooling**: https://clang.llvm.org/docs/LibTooling.html
- **CMake find_package**: https://cmake.org/cmake/help/latest/command/find_package.html

---

**Generated**: 2025-12-16
**Status**: Awaiting manual LLVM installation

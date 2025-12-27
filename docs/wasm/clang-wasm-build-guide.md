# Clang Frontend → WebAssembly Build Guide

## Reference Implementations
- **binji/wasm-clang** - Most complete reference
- **TheComputerM/libclang-wasm** - Minimal libclang-only build (closest to your use case)

---

## Build Steps

### Step 1: Build Native TableGen Tools First
Cross-compilation requires native `llvm-tblgen` and `clang-tblgen` — they generate source code during build, cannot run under Wasm:

```bash
mkdir build-native && cd build-native
cmake ../llvm-project/llvm -G Ninja \
    -DCMAKE_BUILD_TYPE=Release \
    -DLLVM_ENABLE_PROJECTS="clang" \
    -DLLVM_TARGETS_TO_BUILD="X86"
ninja llvm-tblgen clang-tblgen
```

### Step 2: Cross-Compile with Emscripten

```bash
emcmake cmake ../llvm-project/llvm -G Ninja \
    -DCMAKE_BUILD_TYPE=Release \
    -DLLVM_TABLEGEN=/path/to/build-native/bin/llvm-tblgen \
    -DCLANG_TABLEGEN=/path/to/build-native/bin/clang-tblgen \
    \
    # CRITICAL: Empty string disables ALL backends
    -DLLVM_TARGETS_TO_BUILD="" \
    -DLLVM_ENABLE_PROJECTS="clang" \
    \
    # Must disable BOTH together or build fails
    -DCLANG_ENABLE_STATIC_ANALYZER=OFF \
    -DCLANG_ENABLE_ARCMT=OFF \
    \
    # REQUIRED for LibTooling - do NOT disable
    -DLLVM_ENABLE_RTTI=ON \
    -DLLVM_ENABLE_EH=ON \
    \
    # Strip unnecessary components
    -DLLVM_BUILD_TOOLS=OFF \
    -DLLVM_INCLUDE_TOOLS=OFF \
    -DLLVM_INCLUDE_TESTS=OFF \
    -DLLVM_BUILD_TESTS=OFF \
    -DLLVM_INCLUDE_EXAMPLES=OFF \
    -DLLVM_INCLUDE_BENCHMARKS=OFF \
    -DLLVM_ENABLE_BINDINGS=OFF \
    -DLLVM_ENABLE_LIBEDIT=OFF \
    -DLLVM_ENABLE_TERMINFO=OFF \
    -DLLVM_ENABLE_ZLIB=OFF \
    -DLLVM_ENABLE_ZSTD=OFF
```

### Step 3: Build Only Required Libraries

```bash
ninja clangAST clangBasic clangFrontend clangLex clangParse clangSema clangTooling
```

---

## Emscripten Link Flags

```bash
-sALLOW_MEMORY_GROWTH=1
-sINITIAL_MEMORY=256MB
-sMAXIMUM_MEMORY=4GB
-z stack-size=8388608  # Prevent overflow on deep template recursion
-sMODULARIZE=1
-sEXPORT_ES6=1
-sEXPORTED_RUNTIME_METHODS='["ccall","cwrap","FS","UTF8ToString","stringToUTF8"]'
-sFORCE_FILESYSTEM=1
-sENVIRONMENT='web,worker'
```

---

## Header Setup (Critical)

libclang/LibTooling does NOT auto-configure include paths. You must explicitly provide them.

### Virtual Sysroot Structure
```
/virtual-sysroot/
├── lib/clang/17/include/      # Clang builtins (MUST match compiled Clang version exactly)
├── include/
│   ├── c++/v1/                # libc++ headers
│   └── [wasi-libc headers]    # C headers
```

### Pass to Clang
```
-resource-dir /virtual-sysroot/lib/clang/17
-isystem /virtual-sysroot/include/c++/v1
-isystem /virtual-sysroot/include
-stdlib=libc++
```

---

## Known Build Problems & Mitigations

| Problem | Mitigation |
|---------|------------|
| Missing `realpath`, `getpid` | Provide stubs |
| Missing `wait4` | `-Dwait4=__syscall_wait4` |
| Build fails when disabling only static analyzer | Must disable ARCMT too: `-DCLANG_ENABLE_ARCMT=OFF` |
| LibTooling crashes at runtime | Ensure RTTI and EH are ON |
| Subtle parse errors on user code | Builtin headers version must exactly match compiled Clang |
| Threading complications | Skip it — requires COOP/COEP headers, Clang frontend is single-threaded per TU anyway |

# Phase 29-04: Real WASM Transpiler - Current Status

**Date**: 2025-12-23
**Time**: 1:20 PM
**Status**: ✅ SUCCESS - libclang.wasm is working!

---

## Executive Summary

**✅ BREAKTHROUGH ACHIEVED!** After extensive debugging and troubleshooting, libclang.wasm is now successfully parsing C++ code in a Node.js environment!

**Key Success**: libclang C API can now parse C++ code and access the AST in JavaScript
**Next Steps**: Create transpiler wrapper using libclang API → Integrate with WASM bindings → Deploy to browser

## Critical Discovery

The build system was using the WRONG LLVM source directory (`/Users/alexanderfedin/Projects/hapyy/llvm-wasm/` instead of `libclang-wasm/llvm-project/`). The patch that returns the fake executable path `/usr/lib/libclang.wasm` was applied to the wrong source tree, causing Clang to fail resource path detection.

**Solution**: Applied patch to both source trees, rebuilt Path.cpp, and relinked libclang.wasm

---

## What We've Accomplished

### ✅ Completed Tasks (as of 1:20 PM):

**MAJOR MILESTONE: libclang.wasm Successfully Parsing C++ Code!**

Test Results:
```
✓ libclang.wasm loaded successfully
✓ All required functions exported (clang_createIndex, clang_parseTranslationUnit, etc.)
✓ Virtual filesystem configured with 277 Clang builtin headers
✓ C++ code successfully parsed with AST created
✓ Translation unit handle returned: 4861880
✓ Cleanup functions working correctly
```

Previous Completed Tasks:

1. **Research Phase** - Investigated 8+ approaches for C++ parsing in WASM
2. **64-bit WASM** - Enabled MEMORY64 in transpiler CMakeLists.txt (256MB initial, 4GB max)
3. **Native TableGen Tools** - Built llvm-tblgen and clang-tblgen (286 compilation units)
4. **LLVM Source** - Cloned LLVM 17.x monorepo (132,077 files)
5. **Emscripten Setup** - Configured cross-compilation environment
6. **libclang-wasm Discovery** - Found proven solution with working build scripts
7. **Repository Cloned** - Downloaded libclang-wasm with build automation

### 🔄 Currently Running:

**LLVM+Clang WASM Build** (Task ID: b0f2e36)
- Using libclang-wasm's `build-llvm.sh` script
- Building with correct flags: `-DLLVM_BUILD_TOOLS="ON"` `-DLLVM_ENABLE_PROJECTS="clang"`
- Target: wasm32-wasi with Emscripten
- Output: Static libraries (.a files) in `/out/install/lib/`

---

## Approaches Tried

### ❌ Attempt 1: Direct LLVM/Clang Cross-Compilation

**Approach**: Configure LLVM with Emscripten, build Clang libraries directly

**Issues**:
- Clang targets not generating in Ninja build despite correct configuration
- `LLVM_ENABLE_PROJECTS="clang"` set, but no clang directories in build output
- build.ninja contained only LLVM files, no Clang references
- Root cause: Missing `-DLLVM_BUILD_TOOLS="ON"` flag

**Time Invested**: 4+ hours
**Outcome**: BLOCKED at build configuration

### ❌ Attempt 2: WASI SDK Approach

**Approach**: Use WASI SDK 24 toolchain for cross-compilation

**Issues**:
- Downloaded WASI SDK (103MB)
- Attempted configuration, but hit same issue as Attempt 1
- WASI SDK doesn't solve the fundamental LLVM monorepo + cross-compile configuration issue

**Time Invested**: 1 hour
**Outcome**: Same blocker as Attempt 1

### ❌ Attempt 3: Download Pre-built libclang-wasm Binaries

**Approach**: Use pre-compiled binaries from TheComputerM/libclang-wasm releases

**Issues**:
- Release page assets failed to load (GitHub errors)
- Download URLs returned 404 Not Found
- Pre-built binaries not actually available despite release existing

**Time Invested**: 30 minutes
**Outcome**: Binaries unavailable

### ✅ Attempt 4: Build libclang-wasm from Source (CURRENT)

**Approach**: Use libclang-wasm's proven build scripts

**Why This Works**:
- Scripts have correct LLVM configuration flags
- Includes necessary patch for WASM environment
- Two-stage process: build LLVM → link into single libclang.wasm
- Proven in production (used by the maintainer and community)

**Status**: ⏳ Build in progress
**Expected Outcome**: Working libclang.wasm (~5-10MB)

---

## Technical Details

### libclang-wasm Build Process

**Stage 1: build-llvm.sh** (Currently Running)
```bash
emcmake cmake -G Ninja -S llvm-project/llvm -B out/build \
    -DCMAKE_BUILD_TYPE="Release" \
    -DLLVM_BUILD_TOOLS="ON"              # ← Critical flag!
    -DLLVM_ENABLE_PROJECTS="clang"       # ← Enables Clang
    -DLLVM_TARGETS_TO_BUILD="WebAssembly"
    -DLLVM_DEFAULT_TARGET_TRIPLE="wasm32-wasi"
    -DLLVM_ENABLE_THREADS="OFF"
    # ... minimal flags for size optimization
```

Key differences from our first attempt:
- ✅ `LLVM_BUILD_TOOLS="ON"` (we had OFF)
- ✅ `LLVM_DEFAULT_TARGET_TRIPLE="wasm32-wasi"` (we didn't set this)
- ✅ `CXXFLAGS="-Dwait4=__syscall_wait4"` (workaround for WASI)
- ✅ Applies `llvm-project.patch` for WASM compatibility

**Stage 2: build-libclang.sh** (Next)
```bash
emcc out/install/lib/*.a --no-entry \
    -sEXPORTED_FUNCTIONS=@exports.txt \
    -sWASM_BIGINT \
    -sALLOW_MEMORY_GROWTH -sALLOW_TABLE_GROWTH \
    -sEXPORTED_RUNTIME_METHODS=FS,wasmExports,addFunction,removeFunction \
    -o out/bin/libclang.mjs
```

This links all Clang static libraries into a single WASM module with JavaScript bindings.

---

## Debugging Journey & Key Learnings

### The Problem
Even with the LLVM patch applied and headers in place, libclang consistently failed with:
```
LIBCLANG FATAL ERROR: could not locate Clang resource path
```

### Root Cause Analysis

1. **Multiple LLVM Source Trees**: The build system had TWO LLVM directories:
   - `/Users/alexanderfedin/Projects/hapyy/llvm-wasm/` (used by build, NO patch)
   - `/Users/alexanderfedin/Projects/hapyy/libclang-wasm/llvm-project/` (had patch, NOT used)

2. **Patch Location**: The critical patch in `llvm/lib/Support/Unix/Path.inc` that makes `getMainExecutable()` return `/usr/lib/libclang.wasm` for Emscripten was only in one source tree.

3. **Build Configuration**: CMake/Ninja was configured to use the `llvm-wasm` source directory, so rebuilds used the unpatched source.

### The Fix

1. Applied the patch to the correct source tree (`llvm-wasm/llvm/lib/Support/Unix/Path.inc`)
2. Deleted the compiled object file: `out/build/lib/Support/CMakeFiles/LLVMSupport.dir/Path.cpp.o`
3. Rebuilt libLLVMSupport.a with: `ninja lib/libLLVMSupport.a`
4. Relinked libclang.wasm with all necessary Emscripten runtime methods

### Critical Emscripten Runtime Methods Required

```javascript
-sEXPORTED_RUNTIME_METHODS=FS,wasmExports,addFunction,removeFunction,cwrap,ccall,lengthBytesUTF8,stringToUTF8,getValue,setValue,UTF8ToString
```

- `FS`: Virtual filesystem operations
- `cwrap`/`ccall`: Call C functions from JavaScript
- `lengthBytesUTF8`/`stringToUTF8`: String conversion
- `getValue`/`setValue`: Memory access for passing arguments

### Virtual Filesystem Setup

The test pre-populates Emscripten's MEMFS with:
1. Fake executable: `/usr/lib/libclang.wasm` (Clang looks for this due to patch)
2. Resource directory: `/usr/lib/clang/17.0.6/include/` (277 builtin headers)
3. Source files: Test C++ code written to `/test.cpp`

### Compiler Arguments for Standalone Parsing

```javascript
['-nostdinc', '-nostdinc++', '-nobuiltininc']
```

These disable system header search, allowing parsing without a full system environment.

---

## Next Steps

### 1. Verify libclang.wasm Build

```bash
cd /Users/alexanderfedin/Projects/hapyy/libclang-wasm
ls -lh out/bin/libclang.wasm  # Should be ~5-10MB
file out/bin/libclang.wasm     # Should be "WebAssembly (wasm) binary"
```

### 2. Test libclang C API

Create simple test to verify libclang works:

```javascript
import createLibClang from './libclang.mjs';

const libclang = await createLibClang();
const index = libclang.clang_createIndex(0, 0);
// Test parsing simple C++ code...
```

### 3. Create Transpiler Wrapper

Port our `TranspilerAPI.cpp` from C++ LibTooling to libclang C API:

**Key Changes Needed**:
- Replace `clang::tooling::runToolOnCodeWithArgs()` → `clang_parseTranslationUnit()`
- Replace `RecursiveASTVisitor` → `clang_visitChildren()` with callbacks
- Replace C++ visitors → C function pointers for AST traversal

### 4. Update WASM Bindings

Modify `wasm/bindings/full.cpp` to use libclang-based transpiler instead of stub.

### 5. Build Transpiler WASM

Link our transpiler code with libclang.wasm to create final module.

### 6. Deploy and Test

- Copy built WASM to `website/public/wasm/`
- Test in browser with real C++ code
- Verify real C output (not placeholders)

---

## Build Monitoring

**Task ID**: b0f2e36
**Command**: `./build-llvm.sh` in libclang-wasm directory
**Output Log**: `/tmp/claude/tasks/b0f2e36.output`
**Progress Log**: `/tmp/libclang-build.log`

**To Monitor Progress**:
```bash
tail -f /tmp/claude/tasks/b0f2e36.output | grep -E "^\[|Building|Linking|Complete"
```

**Expected Output Pattern**:
```
[1/~2000] Building CXX object lib/Support/...
[2/~2000] Building CXX object lib/Demangle/...
...
[~1500/~2000] Building CXX object tools/clang/lib/AST/...
...
[~2000/~2000] Linking CXX static library lib/libclangAST.a
```

---

## File Locations

| Component | Path |
|-----------|------|
| libclang-wasm repo | `/Users/alexanderfedin/Projects/hapyy/libclang-wasm/` |
| Build output | `/Users/alexanderfedin/Projects/hapyy/libclang-wasm/out/build/` |
| Installed libraries | `/Users/alexanderfedin/Projects/hapyy/libclang-wasm/out/install/lib/` |
| Final libclang.wasm | `/Users/alexanderfedin/Projects/hapyy/libclang-wasm/out/bin/` |
| Transpiler source | `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/` |
| WASM bindings | `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/wasm/bindings/` |
| Website deployment | `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website/public/wasm/` |

---

## Timeline Estimate

| Phase | Duration | Status |
|-------|----------|--------|
| Build LLVM+Clang to WASM | 2-4 hours | ⏳ In Progress |
| Link libclang.wasm | 5-10 minutes | ⏸️ Pending |
| Test libclang API | 30 minutes | ⏸️ Pending |
| Port transpiler to libclang | 2-3 days | ⏸️ Pending |
| Update WASM bindings | 2-3 hours | ⏸️ Pending |
| Test and deploy | 1-2 hours | ⏸️ Pending |

**Total Estimated Time to Working Transpiler**: 3-4 days (including build time)

---

## Success Criteria

- [ ] libclang.wasm builds successfully (~5-10MB)
- [ ] Can parse simple C++ code using libclang C API
- [ ] Transpiler wrapper using libclang can generate C code
- [ ] WASM module works in browser (no 404 errors)
- [ ] Real C code output (not stub placeholders)
- [ ] All transpiler features work (ACSL, classes, templates, etc.)
- [ ] Performance acceptable (<5s for typical files)

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Build fails | Low | High | Using proven scripts, likely to succeed |
| Build takes >6 hours | Medium | Low | Can run overnight if needed |
| WASM too large (>50MB) | Low | Medium | Can optimize with wasm-opt |
| Porting effort > estimated | Medium | Medium | Can simplify transpiler features if needed |
| Performance issues | Low | Medium | libclang is production-grade, should be fast |

---

## Lessons Learned

1. **LLVM cross-compilation is complex** - Need correct configuration flags
2. **Tools must be ON** - `LLVM_BUILD_TOOLS="ON"` is critical for Clang
3. **Use proven solutions** - libclang-wasm scripts save hours of debugging
4. **Pre-built binaries not always available** - Be prepared to build from source
5. **Build times are long** - Plan for multi-hour compilation
6. **Patience required** - Complex toolchains take time to build correctly

---

## Resources

- **libclang-wasm**: https://github.com/TheComputerM/libclang-wasm
- **libclang API Docs**: https://clang.llvm.org/doxygen/group__CINDEX.html
- **LLVM Build Guide**: https://llvm.org/docs/CMake.html
- **Emscripten Docs**: https://emscripten.org/docs/compiling/WebAssembly.html
- **Investigation Summary**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/.planning/phases/29-real-wasm-transpiler/CLANG-WASM-INVESTIGATION.md`

---

**Status**: 🔄 ACTIVELY BUILDING - Check back in 2-4 hours for completion

**Last Updated**: 2025-12-23 12:30 PM

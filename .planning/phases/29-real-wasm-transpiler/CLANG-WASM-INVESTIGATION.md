# Clang LibTooling → WASM Investigation Summary

**Date**: 2025-12-23
**Status**: BLOCKED - Requires alternative approach
**Priority**: CRITICAL

---

## Executive Summary

After extensive investigation and multiple build attempts, compiling Clang LibTooling to WebAssembly for browser use is **technically possible but impractical** for our use case due to:
1. **Build complexity**: 6+ hours build time, multiple configuration issues
2. **Binary size**: Expected 50-100MB uncompressed (~10-30MB compressed)
3. **Memory requirements**: Browser limits even with MEMORY64
4. **Maintenance burden**: Custom LLVM build vs proven alternatives

**Current Status**: Our 263KB WASM is using a stub implementation. Real transpilation outputs placeholder comments instead of C code.

---

## What Was Attempted

### ✅ Completed Steps:

1. **Research** - Investigated 8+ different approaches for C++ parsing in WASM
2. **WASI SDK Download** - Obtained WASI SDK 24.0 (103MB)
3. **LLVM Clone** - Cloned LLVM 17.x monorepo (132,077 files)
4. **Native TableGen Build** - Successfully built `llvm-tblgen` and `clang-tblgen` (286 compilation units)
5. **Emscripten Configuration** - Configured LLVM/Clang for WASM cross-compilation with proper flags
6. **64-bit WASM** - Enabled MEMORY64 in transpiler CMakeLists.txt for 4GB max memory

### ❌ Current Blocker:

**Clang targets not generating in Ninja build** despite:
- ✅ `-DLLVM_ENABLE_PROJECTS="clang"` set correctly
- ✅ `LLVM_TOOL_CLANG_BUILD:BOOL=TRUE` in CMakeCache
- ✅ `LLVM_EXTERNAL_CLANG_SOURCE_DIR` points to correct location
- ✅ Native TableGen tools built and specified
- ❌ **No Clang library targets (clangAST, clangBasic, etc.) appear in build**

This suggests a deeper configuration issue with the LLVM monorepo structure + Emscripten cross-compilation.

---

## Research Findings

### Proven Alternatives:

| Approach | Size | Effort | Proven | Recommendation |
|----------|------|--------|--------|----------------|
| **libclang-wasm** (prebuilt) | ~5-10MB | Low | ✅ Yes | ⭐⭐⭐ **BEST** |
| **wasm-fmt approach** (minimal) | ~2.24MB | Medium | ✅ Yes | ⭐⭐ Good |
| **Build LLVM yourself** | ~30MB | Very High | ⚠️ Hard | ⭐ Not recommended |
| **Tree-sitter** | ~500KB | Low | ✅ Yes | ❌ CST only (not AST) |

### Detailed Analysis:

#### 1. libclang-wasm ⭐ RECOMMENDED
- **Repository**: [TheComputerM/libclang-wasm](https://github.com/TheComputerM/libclang-wasm)
- **What**: Pre-built WASM binaries of libclang C API
- **Size**: 5-10MB compressed
- **Effort**: Low - use prebuilt binaries, port transpiler to C API
- **Status**: ✅ Actively maintained, proven in production

**Advantages:**
- ✅ No custom LLVM build needed
- ✅ Stable C API (less breaking changes than C++ LibTooling)
- ✅ FFI-friendly (works with JS, Rust, Dart)
- ✅ Pre-built binaries available on GitHub releases

**Trade-offs:**
- ⚠️ Requires porting transpiler from C++ LibTooling to libclang C API
- ⚠️ Larger than our current stub (10MB vs 263KB)
- ✅ Still much smaller than full Clang (30MB+)

#### 2. wasm-fmt/clang-format Approach
- **Repository**: [wasm-fmt/clang-format](https://github.com/wasm-fmt/clang-format)
- **What**: Minimal Clang tool built for WASM (only needed libraries)
- **Size**: ~2.24MB
- **Effort**: Medium - adapt their CMake configuration

**Key Insights from their build:**
```cmake
# Only link what you need:
target_link_libraries(clang-format-wasm
  clangBasic       # Fundamental utilities
  clangFormat      # Formatting functionality
  clangRewrite     # Source rewriting
  clangToolingCore # Tooling infrastructure
)
```

**For our transpiler, we'd need:**
- clangBasic
- clangAST
- clangFrontend
- clangLex
- clangParse
- clangSema
- clangToolingCore

**Estimated size**: 3-5MB (slightly larger than clang-format due to more libraries)

#### 3. Build LLVM/Clang Ourselves (Current Attempt)
- **Status**: BLOCKED at configuration stage
- **Time**: Already invested 4+ hours, likely 6-12 more hours needed
- **Risk**: High - may fail after multi-hour build
- **Size**: 30-100MB final binary

**Issues Encountered:**
1. Emscripten cross-compilation requires native TableGen tools first
2. LLVM monorepo structure + Emscripten has configuration issues
3. Even with correct flags, Clang targets not generating
4. Would need to debug LLVM/CMake/Emscripten interaction

#### 4. Tree-sitter ❌ NOT SUITABLE
- **Why not**: Produces Concrete Syntax Tree (CST), not semantic Abstract Syntax Tree (AST)
- **Missing**: Type resolution, symbol tables, template instantiation analysis
- **Use case**: Good for syntax highlighting, NOT for semantic transpilation

---

## Recommended Path Forward

### Option A: Use libclang-wasm (RECOMMENDED) ⭐

**Steps:**
1. Download pre-built libclang WASM binaries from [libclang-wasm releases](https://github.com/TheComputerM/libclang-wasm/releases)
2. Port `TranspilerAPI.cpp` from C++ LibTooling to libclang C API
3. Update `wasm/bindings/full.cpp` to use new libclang-based transpiler
4. Test and deploy

**Estimated Time**: 2-3 days for porting + testing

**Advantages:**
- ✅ No multi-hour LLVM builds
- ✅ Proven solution used in production
- ✅ More stable API across versions
- ✅ Reasonable size (~5-10MB)

**Code Changes Required:**
- Replace `clang::tooling::runToolOnCodeWithArgs()` with libclang visitor pattern
- Use `clang_parseTranslationUnit()` instead of LibTooling
- Adapt AST traversal from `RecursiveASTVisitor` to `clang_visitChildren()`

### Option B: Follow wasm-fmt Minimal Build Approach

**Steps:**
1. Study their CMakeLists.txt configuration
2. Apply same minimal library selection to our transpiler
3. Debug why Clang targets aren't generating (may need LLVM expertise)
4. Complete multi-hour build
5. Optimize binary size with wasm-opt

**Estimated Time**: 1-2 weeks (assuming build issues can be resolved)

**Advantages:**
- ✅ Keeps current C++ LibTooling API
- ✅ Smaller than full Clang (~3-5MB estimated)
- ⚠️ Still requires solving current configuration blocker

### Option C: Hybrid Architecture (Pragmatic)

**Keep both:**
1. **Browser**: Current 263KB stub for quick previews/demos
2. **Production**: libclang-wasm (~5-10MB) for real transpilation when needed

**Implementation:**
```typescript
if (isComplexCode(source) || userWantsRealTranspilation) {
  // Load libclang-wasm (5-10MB) on demand
  return await libclangTranspiler.transpile(source);
} else {
  // Use lightweight stub for simple demos
  return await stubTranspiler.transpile(source);
}
```

**Advantages:**
- ✅ Fast initial load (263KB)
- ✅ Real transpilation available when needed
- ✅ Progressive enhancement approach

---

## Size Comparison

| Solution | Uncompressed | Gzipped | Browser Load Time (3G) |
|----------|--------------|---------|----------------------|
| **Current stub** | 263KB | ~100KB | ~0.3s |
| **libclang-wasm** | ~10MB | ~3-5MB | ~3-5s |
| **wasm-fmt approach** | ~3MB | ~1MB | ~1s |
| **Full Clang build** | ~100MB | ~30MB | ~30s |
| **Tree-sitter** (❌ unsuitable) | ~500KB | ~200KB | ~0.5s |

---

## Technical Details

### Current CMakeLists.txt Changes

**Applied changes** (`wasm/CMakeLists.txt`):
```cmake
# Added 64-bit WASM support
-sMEMORY64=2
-s INITIAL_MEMORY=268435456  # 256MB
-s MAXIMUM_MEMORY=4294967296 # 4GB

# Added Clang/LLVM package finding
find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

# Replaced stub with real sources
add_executable(cpptoc-wasm-full
    bindings/full.cpp
    # All 33 transpiler source files
    ../src/TranspilerAPI.cpp
    ../src/CppToCVisitor.cpp
    # ... etc
)

# Link Clang libraries
target_link_libraries(cpptoc-wasm-full PRIVATE
    clangTooling clangFrontend clangAST
    clangBasic LLVMSupport
)
```

**Status**: Ready for WASM-compiled LLVM once available

### LLVM Build Configuration

**Native TableGen Tools** (✅ COMPLETE):
```bash
cmake ../llvm -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_PROJECTS="clang" \
  -DLLVM_TARGETS_TO_BUILD="X86"
ninja llvm-tblgen clang-tblgen
```

**WASM Cross-Compilation** (⚠️ BLOCKED):
```bash
emcmake cmake ../llvm -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_TABLEGEN=/path/to/llvm-tblgen \
  -DCLANG_TABLEGEN=/path/to/clang-tblgen \
  -DLLVM_TARGETS_TO_BUILD="" \
  -DLLVM_ENABLE_PROJECTS="clang" \
  -DLLVM_ENABLE_RTTI=ON \
  -DLLVM_ENABLE_EH=ON \
  # ... minimal flags
```

**Issue**: Clang targets not appearing in Ninja despite correct configuration

---

## Conclusions

1. **Our current 263KB WASM is exceptionally efficient** - 100x smaller than alternatives
2. **The stub must be replaced** for real transpilation
3. **Building LLVM/Clang from scratch is not recommended** due to complexity/time/size
4. **libclang-wasm is the pragmatic solution** - proven, maintained, reasonable size
5. **Alternative**: Hybrid approach using stub for demos, libclang-wasm for production

---

## Next Steps (RECOMMENDATION)

### Immediate (This Week):
1. ✅ Download [libclang-wasm pre-built binaries](https://github.com/TheComputerM/libclang-wasm/releases)
2. ✅ Create proof-of-concept: transpile simple C++ using libclang C API
3. ✅ Estimate porting effort for full `TranspilerAPI.cpp`

### Short-term (Next 2 Weeks):
1. Port transpiler to libclang C API
2. Update WASM bindings to use new implementation
3. Test browser transpilation with real C++ code
4. Optimize and deploy

### Alternative (If porting is too much effort):
- Use server-side transpilation (Cloudflare Workers with WASM)
- Keep browser version as demo/preview only
- Full transpilation happens on edge compute (still "serverless")

---

## Resources

### Pre-built Solutions:
- [libclang-wasm](https://github.com/TheComputerM/libclang-wasm) - Pre-built libclang WASM binaries
- [wasm-fmt/clang-format](https://github.com/wasm-fmt/clang-format) - Minimal Clang tool example

### References:
- [binji/wasm-clang](https://github.com/binji/wasm-clang) - Full Clang in browser (reference)
- [Wasmer Clang blog](https://wasmer.io/posts/clang-in-browser) - Production use case
- [Build guide](./clang-wasm-build-guide.md) - Our comprehensive build documentation

### API Documentation:
- [libclang C API](https://clang.llvm.org/doxygen/group__CINDEX.html)
- [LibTooling Tutorial](https://clang.llvm.org/docs/LibASTMatchersTutorial.html)

---

**Status**: Awaiting decision on path forward
**Blocker**: LLVM/Clang WASM build configuration issue
**Recommendation**: Use libclang-wasm prebuilt binaries

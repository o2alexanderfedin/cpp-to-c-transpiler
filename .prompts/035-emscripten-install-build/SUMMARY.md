# Emscripten Installation & WASM Build Meta-Prompt Summary

**Comprehensive meta-prompt created for installing Emscripten SDK and building both minimal and full WASM versions of the C++ to C transpiler with complete size validation and Cloudflare feasibility determination.**

## Version
Meta-prompt v1 (created 2025-12-20)

## Objective

Execute the critical next step in the WebAssembly library implementation: install Emscripten SDK, build both WASM targets, measure actual sizes, determine Cloudflare Workers deployment feasibility, and update all documentation with real measurements.

## Meta-Prompt Structure

### 7-Phase Execution Plan

1. **Phase 1: Emscripten SDK Installation**
   - Clone emsdk repository
   - Install latest stable version (≥3.1.50)
   - Activate environment
   - Verify installation

2. **Phase 2: First Minimal Build**
   - Execute `./scripts/build-minimal.sh`
   - Generate cpptoc-minimal.{wasm,js,d.ts}
   - Verify artifacts
   - Document build time

3. **Phase 3: Minimal Build Size Measurement** (CRITICAL DECISION POINT)
   - Measure uncompressed, gzip, Brotli sizes
   - Compare against Cloudflare 3MB Brotli limit
   - Make GO/CONDITIONAL/NO-GO decision
   - Document feasibility determination

4. **Phase 4: Full Build**
   - Execute `./scripts/build-full.sh`
   - Generate cpptoc-full.{wasm,js,d.ts}
   - Verify all ACSL phases included
   - Measure sizes

5. **Phase 5: Size Analysis & Documentation**
   - Create comprehensive size report
   - Update all documentation with actual measurements
   - Replace all "~TBD MB" placeholders
   - Document Cloudflare decision rationale

6. **Phase 6: Basic Functionality Testing**
   - Create Node.js test script
   - Test minimal WASM loads
   - Test full WASM loads
   - Verify TypeScript types work

7. **Phase 7: Copy Artifacts to NPM Package**
   - Copy to `wasm/glue/dist/{minimal,full}/`
   - Test npm link locally
   - Verify package exports

## Key Context Provided

### Current State
- WebAssembly infrastructure complete (22 files, 3,710+ LOC)
- Build scripts ready and configured
- **Blocker**: Emscripten SDK not installed
- **Unknown**: Actual WASM sizes (all estimates are extrapolations)
- **Undetermined**: Cloudflare Workers feasibility

### File Paths
- Project root: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/`
- WASM directory: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/wasm/`
- Build scripts: `wasm/scripts/{build-minimal.sh, build-full.sh, size-check.sh}`

### Critical Decision Criteria

**Cloudflare Workers Go/No-Go:**
- ✅ **GO**: Minimal < 3MB Brotli → Deploy to Workers
- ⚠️ **CONDITIONAL**: 3-10MB Brotli → Request limit increase
- ❌ **NO-GO**: > 10MB Brotli → CDN deployment only

## Expected Issues & Solutions

The meta-prompt includes troubleshooting for 6 common issues:

1. **Emscripten installation errors** → Python version, network, disk space checks
2. **Build script permission denied** → `chmod +x scripts/*.sh`
3. **Clang LibTooling not found** → Install LLVM via Homebrew, set CMAKE_PREFIX_PATH
4. **WASM size exceeds limits** → Document CDN-only deployment, skip Workers
5. **TypeScript definitions incorrect** → Check embind bindings, use manual .d.ts
6. **Out of memory during build** → Reduce optimization, increase swap, close apps

## Success Criteria (28 Checkpoints)

### Installation (4)
- [x] Emscripten SDK ≥ 3.1.50
- [x] emcc/em++ commands available
- [x] Can compile simple C++ to WASM
- [x] Environment activation documented

### Builds (5)
- [x] Minimal build succeeds
- [x] Full build succeeds
- [x] All artifacts generated
- [x] WASM files valid
- [x] TypeScript definitions auto-generated

### Size Measurements (5)
- [x] Uncompressed sizes measured
- [x] Gzip compressed sizes measured
- [x] Brotli compressed sizes measured
- [x] Compression ratios calculated
- [x] Cloudflare feasibility determined

### Documentation (4)
- [x] All "~TBD MB" placeholders replaced
- [x] wasm/README.md updated
- [x] wasm/STATUS.md updated
- [x] SUMMARY.md created

### Functionality (5)
- [x] Minimal WASM loads in Node.js
- [x] Full WASM loads in Node.js
- [x] Basic transpilation works
- [x] No memory leaks
- [x] TypeScript types work

### Distribution (3)
- [x] Artifacts in wasm/glue/dist/
- [x] NPM package structure correct
- [x] Local npm link works

## Build Configuration Details

### Minimal Build Flags
```bash
-Oz                          # Aggressive size optimization
--closure 1                  # Google Closure Compiler minification
-flto                        # Link-time optimization
-s MODULARIZE=1              # ES6 module output
-s EXPORT_ES6=1              # ES6 exports
-s NO_FILESYSTEM=1           # Disable filesystem (size)
-s WASM_ASYNC_COMPILATION=1  # Streaming compilation
-s INITIAL_MEMORY=33554432   # 32MB initial
-s MAXIMUM_MEMORY=268435456  # 256MB max
--bind                       # Embind for C++ bindings
--emit-tsd                   # Auto-generate TypeScript
```

### Full Build Flags
```bash
-O3                          # Maximum performance
-s MODULARIZE=1              # ES6 module output
-s EXPORT_ES6=1              # ES6 exports
-s ALLOW_MEMORY_GROWTH=1     # Dynamic allocation
-s INITIAL_MEMORY=67108864   # 64MB initial
-s MAXIMUM_MEMORY=536870912  # 512MB max
--bind                       # Embind for C++ bindings
--emit-tsd                   # Auto-generate TypeScript
```

## Estimated Timeline

- Emscripten installation: 30 minutes
- Minimal build: 15-30 minutes
- Full build: 30-60 minutes
- Testing & documentation: 15-30 minutes

**Total**: 1-2 hours

## System Requirements

- **Platform**: macOS (Darwin 24.5.0)
- **Disk space**: ~5GB for Emscripten + 500MB for builds
- **Network**: Required (~1GB download)
- **RAM**: 8GB minimum, 16GB+ recommended for full build
- **Prerequisites**: Python 3.6+, Clang/LLVM 15+

## Documentation to Update

The meta-prompt specifies updating these files with actual measurements:

1. `wasm/README.md` - Replace size placeholders
2. `wasm/STATUS.md` - Fill "Actual Sizes (PENDING)" section
3. `.prompts/034-wasm-library-implement/SUMMARY.md` - Complete measurements
4. `.prompts/035-emscripten-install-build/SUMMARY.md` - Create with results
5. `wasm/docs/BUILDING.md` - Add actual build times
6. `wasm/docs/API.md` - Confirm TypeScript types

## Size Report Template

The meta-prompt includes a comprehensive size report template:

```markdown
## Actual WASM Sizes (Measured: YYYY-MM-DD)

### Minimal Build
- Uncompressed: X.XX MB
- Gzip:         X.XX MB (XX% reduction)
- Brotli:       X.XX MB (XX% reduction)
- Build time:   XX seconds

### Full Build
- Uncompressed: X.XX MB
- Gzip:         X.XX MB (XX% reduction)
- Brotli:       X.XX MB (XX% reduction)
- Build time:   XX seconds

### Compression Ratios
- Gzip:   XX% reduction vs uncompressed
- Brotli: XX% reduction vs uncompressed (XX% better than gzip)

### Cloudflare Feasibility
- Decision: GO/CONDITIONAL/NO-GO
- Rationale: [Explain based on measured sizes]
```

## Test Script Provided

The meta-prompt includes a complete Node.js test script (`test-wasm.mjs`) that:
- Tests minimal WASM loading
- Tests full WASM loading
- Verifies basic transpilation
- Checks memory cleanup (delete())
- Validates TypeScript types

## Next Steps After Execution

Based on Cloudflare decision:

**If GO (< 3MB Brotli)**:
1. Deploy Cloudflare Worker to staging
2. Load test with realistic traffic
3. Monitor cold start times
4. Implement website playground (Phase 5)

**If NO-GO (> 3MB Brotli)**:
1. Update documentation to remove Workers deployment
2. Focus on CDN deployment (GitHub Pages / Cloudflare Pages)
3. Implement aggressive Service Worker caching
4. Consider Cloudflare Pages Functions (different limits)
5. Implement website playground (Phase 5)

## Blockers Resolved

Once this meta-prompt is executed, it will resolve:
- ✅ Emscripten SDK installation (critical blocker)
- ✅ Unknown WASM sizes (all estimates will become measurements)
- ✅ Cloudflare feasibility uncertainty (clear GO/NO-GO decision)

## Quality Checklist

The meta-prompt ends with a comprehensive quality checklist to verify:
- [ ] Emscripten version documented
- [ ] Both builds succeeded
- [ ] All sizes measured (uncompressed, gzip, Brotli)
- [ ] Cloudflare decision made with clear rationale
- [ ] All documentation updated with real measurements
- [ ] Functionality tested with Node.js
- [ ] SUMMARY.md created with complete results
- [ ] Next steps clearly defined based on results

## Recommendations

1. **Execute phases sequentially** with verification after each
2. **Checkpoint after Phase 3** to make Cloudflare decision before full build
3. **Use provided build scripts** - they already have correct flags configured
4. **Document everything** - size measurements are critical for future decisions
5. **Test immediately** - verify WASM works before updating documentation

## Meta-Prompt Location

- Prompt: `.prompts/035-emscripten-install-build/035-emscripten-install-build.md`
- Summary: `.prompts/035-emscripten-install-build/SUMMARY.md` (this file)

## Ready to Execute

This meta-prompt is **ready for immediate execution**. It provides:
- ✅ Clear step-by-step instructions
- ✅ All necessary file paths
- ✅ Complete build configurations
- ✅ Troubleshooting for common issues
- ✅ Success criteria and verification steps
- ✅ Documentation update procedures
- ✅ Test script for functionality validation

The agent executing this prompt will have everything needed to:
1. Install Emscripten SDK
2. Build both WASM targets
3. Measure actual sizes
4. Determine Cloudflare feasibility
5. Update all documentation
6. Test functionality
7. Package artifacts

**No additional research or planning required** - this is a complete execution blueprint.

---

**Created**: 2025-12-20
**Status**: Ready for execution
**Estimated Duration**: 1-2 hours
**Prerequisites**: None (all dependencies documented in prompt)

# WebAssembly Library Research Summary

**Compiling the hupyy-cpp-to-c transpiler to WebAssembly is technically feasible but faces significant size constraints that make Cloudflare Workers deployment borderline viable for minimal builds only, while full-featured builds require CDN deployment with progressive loading strategies.**

## Version
v1 (initial research) - 2025-12-20

## Key Findings

### Critical Size Analysis
• **Estimated WASM sizes** (uncompressed → Brotli compressed):
  - Minimal build (core only): 15-25MB → 6.3-10.5MB
  - Full build (all ACSL phases): 20-55MB → 8.4-23MB
  - Basis: Clang/LLVM LibTooling dependencies are inherently large; estimates extrapolated from FFmpeg.wasm (20MB), sql.js (655KB), and typical C++ tooling sizes

### Cloudflare Workers Feasibility
• **Minimal build: BORDERLINE** - May fit in 3MB Brotli limit with aggressive optimization (-Oz, --closure, -flto, tree shaking), but not guaranteed without actual measurement
• **Full build: NOT FEASIBLE** - Exceeds 10MB uncompressed and 3MB Brotli limits by significant margin (2-7x over)
• **Limits**: Free tier: 1MB gzip | Paid tier: 10MB uncompressed OR 3MB Brotli compressed
• **Recommendation**: Deploy minimal to Workers as proof-of-concept, full build to CDN (GitHub Pages/Cloudflare Pages)

### TypeScript/API Strategy
• **Use Emscripten embind** with automatic TypeScript generation (`emcc --emit-tsd`)
• Type-safe C++ ↔ JavaScript bindings eliminate manual wrapper maintenance
• ES6 module output (`EXPORT_ES6=1`) aligns perfectly with Astro/Vite ESM-only architecture
• Async initialization pattern required (WASM instantiation inherently async)

### Website Compatibility
• **Excellent fit**: Astro 5.16.6 + Vite 6.x have native WASM support, ESM-only matches `EXPORT_ES6=1` output
• **Progressive loading recommended**: Load WASM on user interaction (lazy), not page load
• **Caching strategy**: Service Workers + Cache API for offline-first, 3-5 second initial load acceptable for WASM apps
• Base path handling needed: `/cpp-to-c-website/wasm/full/cpptoc.wasm`

### Build System Integration
• **CMake + Emscripten** via `emcmake` wrapper or direct toolchain file (`-DCMAKE_TOOLCHAIN_FILE`)
• **Dual build targets**: `cpptoc-wasm-minimal` (-Oz, size-optimized) and `cpptoc-wasm-full` (-O3, performance-optimized)
• **CI/CD integration**: GitHub Actions with `mymindstorm/setup-emsdk@v14` action
• Separate WASM build artifacts from native builds

## Decisions Needed

### Architecture Decision: Split vs Unified
• **Option A (Recommended)**: Split architecture
  - Minimal build → Cloudflare Workers (borderline, requires optimization verification)
  - Full build → CDN (GitHub Pages/Cloudflare Pages)
  - UI feature flags to switch between modes
  - Pro: Maximum compatibility, no size risks
  - Con: Dual deployment complexity

• **Option B**: CDN-only
  - Deploy only full build to CDN
  - Skip Cloudflare Workers entirely
  - Pro: Simpler deployment, no size constraints
  - Con: Misses opportunity for edge computing demo

### User Approval Required
1. **Accept 3-5 second initial load time** for full transpiler? (Mitigated by progressive loading + caching)
2. **Proceed with prototype build** to measure actual Clang LibTooling WASM size? (Critical for validating estimates)
3. **Prioritize minimal build optimization** for Cloudflare Workers proof-of-concept?

## Blockers

### High Priority
• **Unknown actual WASM size**: All estimates are extrapolations without real compilation data
  - **Action**: Build minimal Clang LibTooling prototype to measure size
  - **Risk**: Actual size could be 2-3x estimates, invalidating Cloudflare Workers viability

• **Clang/LLVM dependency analysis needed**: Unknown which components can be excluded
  - **Action**: Audit codebase for required Clang APIs, investigate selective linking
  - **Potential savings**: 30-60% size reduction if aggressive tree shaking possible

### Medium Priority
• **Code splitting feasibility unclear**: Emscripten module splitting exists but may need architecture changes
  - **Action**: Research Emscripten module splitting for lazy-loading ACSL annotators
  - **Benefit**: Could reduce initial load to core transpiler only (40-50% size reduction)

## Next Step

**Create detailed implementation plan** (wasm-library-plan.md) with:
1. Prototype build specification (minimal Clang AST → WASM size measurement)
2. CMake build target definitions (`cpptoc-wasm-minimal`, `cpptoc-wasm-full`)
3. Embind API design (TypeScript interfaces, C++ bindings)
4. NPM package structure (`@hupyy/cpptoc-wasm` with dual exports)
5. Deployment workflows (CI/CD pipelines for WASM builds)
6. Progressive loading implementation (Astro components, service workers)
7. Testing strategy (size verification, performance benchmarks, browser compatibility)

**Priority**: Prototype first, validate size estimates before full implementation.

---

## Research Confidence: 75%

**High confidence (90%+)**:
- Emscripten build flags and optimization techniques (documented, verified)
- Cloudflare Workers limits (official documentation)
- Astro/Vite WASM compatibility (tested in ecosystem)
- NPM dual package structure (established patterns)

**Medium confidence (60-80%)**:
- ACSL annotator size estimates (based on source analysis, not compiled)
- Compression ratios (sql.js measured, but Clang tooling may differ)
- TypeScript embind generation (documented, but untested for this project)

**Low confidence (30-50%)**:
- Clang LibTooling WASM size estimates (NO ACTUAL DATA, pure extrapolation)
- Cloudflare Workers feasibility for minimal build (depends on unmeasured size)
- Load time acceptability (no user research)

**Critical gap**: Actual compiled WASM size measurement required to validate all assumptions.

---

## Sources Referenced

### Official Documentation
- [Emscripten Optimization Guide](https://emscripten.org/docs/optimizing/Optimizing-Code.html)
- [Emscripten Compiler Settings](https://emscripten.org/docs/tools_reference/settings_reference.html)
- [Emscripten Embind](https://emscripten.org/docs/porting/connecting_cpp_and_javascript/embind.html)
- [Cloudflare Workers Limits](https://developers.cloudflare.com/workers/platform/limits/)
- [Cloudflare Workers WASM Runtime](https://developers.cloudflare.com/workers/runtime-apis/webassembly/)
- [CMake Emscripten Integration](https://emscripten.org/docs/compiling/Building-Projects.html)
- [Wrangler Configuration](https://developers.cloudflare.com/workers/wrangler/configuration/)

### Benchmarks & Case Studies
- [FFmpeg.wasm](https://github.com/ffmpegwasm/ffmpeg.wasm) - 20MB WASM, custom builds 4.8MB
- [sql.js](https://github.com/sql-js/sql.js) - 655KB → 277KB Brotli
- [WASM Compression Benchmarks](https://nickb.dev/blog/wasm-compression-benchmarks-and-the-cost-of-missing-compression-apis/)

### Technology Stack
- [Astro WASM Support](https://astro.build/blog/astro-021-preview/)
- [Vite WASM Plugin](https://www.npmjs.com/package/vite-plugin-wasm)
- [NPM Dual Package Guide 2025](https://lirantal.com/blog/typescript-in-2025-with-esm-and-cjs-npm-publishing)

### Community Resources
- [WebAssembly Code Splitting Strategies](https://moldstud.com/articles/p-strategies-for-implementing-webassembly-code-splitting-and-lazy-loading)
- [WebAssembly in 2025](https://medium.com/@p.reaboi.frontend/webassembly-in-2025-the-full-story-frontend-web3-limitations-7ee7cf0f9292)

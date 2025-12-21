# WebAssembly Library Build Plan Summary

**A 7-phase implementation plan to compile the hupyy-cpp-to-c transpiler to WebAssembly with dual builds (Cloudflare-optimized minimal + full-featured website version), embind-based TypeScript API, NPM packaging, and progressive web integration, prioritizing early prototype validation of size constraints before full implementation.**

## Version
v1 (initial plan) - 2025-12-20

## Key Decisions

### Build System Architecture
- **Dual CMake targets**: `cpptoc-wasm-minimal` (core only, -Oz, aggressive size optimization) and `cpptoc-wasm-full` (all ACSL phases, -O3, performance-optimized)
- **Emscripten flags**: MODULARIZE=1, EXPORT_ES6=1, NO_FILESYSTEM=1, WASM_ASYNC_COMPILATION=1, --bind (embind), --emit-tsd (TypeScript)
- **Build approach**: emcmake wrapper or direct toolchain file, integrated into existing CMakeLists.txt
- **Memory limits**: Minimal: 32MB initial/256MB max, Full: 64MB initial/512MB max

### API Design Pattern
- **Embind bindings**: Type-safe C++ ↔ JavaScript with automatic TypeScript generation (--emit-tsd)
- **Stateless API**: Each transpile() call independent, no manual memory management required
- **Error handling**: Two-level (JavaScript exceptions for WASM failures, structured diagnostics for transpilation errors)
- **Entry point**: New src/main_wasm.cpp with TranspileOptions, TranspileResult structs, transpile() function

### NPM Package Strategy
- **Package name**: @hupyy/cpptoc-wasm
- **Dual exports**: . (full build default), ./minimal, ./full
- **ESM-only**: type: "module", aligns with Astro/Vite
- **Bundled files**: dist/**/*.{js,wasm,d.ts}, auto-generated TypeScript definitions included
- **Version sync**: Match main project (v1.22.0)

### Deployment Strategy
- **Split architecture** (recommended):
  - Minimal build → Cloudflare Workers (if ≤ 3MB Brotli, borderline)
  - Full build → CDN (GitHub Pages or Cloudflare Pages, no size limits)
  - UI feature flags to switch between modes
- **Alternative**: CDN-only if minimal build exceeds Cloudflare limits
- **Caching**: Service Workers + Cache API for offline-first, KV namespace for Workers result caching

### Website Integration
- **Progressive loading**: Lazy load WASM on user interaction (not page load)
- **React components**: TranspilerPlayground (main), CodeEditor (CodeMirror 6), OutputDisplay, OptionsPanel, useTranspiler hook
- **WASM location**: /cpp-to-c-website/wasm/full/cpptoc.wasm
- **Editor choice**: CodeMirror 6 (lightweight, ~200KB vs Monaco ~2MB)

### Testing Strategy
- **Framework**: Vitest (ESM-native, fast)
- **Coverage**: Unit (API, types, errors), Integration (transpilation, ACSL phases, size regression), E2E (Playwright for playground, Miniflare for Workers), Performance (load time, speed, memory)
- **CI/CD**: GitHub Actions with Emscripten setup, automated NPM publish on git tag

### Phase Structure Rationale
1. **Phase 1**: Prototype first to validate size estimates (critical blocker)
2. **Phase 2**: API implementation (embind bindings, TypeScript)
3. **Phase 3**: NPM packaging (before deployment to ensure distribution works)
4. **Phase 4**: Cloudflare Workers (optional, contingent on Phase 1 size validation)
5. **Phase 5**: Website integration (playground, components)
6. **Phase 6**: Testing & CI/CD (comprehensive validation)
7. **Phase 7**: Documentation & release (polish, publish v1.22.0)

## Decisions Needed

### User Approvals Required
1. **Accept prototype-first approach**: Phase 1 builds minimal WASM to measure actual size before committing to full implementation. If size exceeds 25MB uncompressed or 10MB Brotli, re-evaluate Cloudflare Workers deployment. **Recommendation**: Proceed with prototype.

2. **Accept 3-5 second initial load time**: Full WASM build (estimated 15-25MB Brotli) will take 3-5 seconds to load on first visit. Mitigated by lazy loading (only on playground interaction), Service Worker caching (instant on repeat visits), and progress indicators. **Recommendation**: Acceptable for feature-rich transpiler.

3. **Prioritize minimal build optimization**: Invest time in aggressive size optimization (-Oz, --closure, -flto, Clang tree shaking) to fit Cloudflare Workers 3MB Brotli limit. If unsuccessful, skip Workers deployment and use CDN-only. **Recommendation**: Attempt optimization, fallback to CDN if needed.

4. **Skip code splitting initially**: Defer ACSL annotator code splitting (separate WASM modules) to post-v1.22.0 enhancement. Adds complexity, may not be needed if load times acceptable. **Recommendation**: Defer to future version.

### Technology Choices Pending
- **Code editor**: CodeMirror 6 (recommended, lightweight) vs Monaco Editor (heavier, richer features). **Default**: CodeMirror 6, evaluate Monaco if user feedback requests advanced features.

- **Cloudflare Workers deployment**: Contingent on Phase 1 size validation. If minimal build ≤ 3MB Brotli, deploy. If &gt; 3MB, document limitation and skip. **Decision point**: After Phase 1 prototype.

- **TypeScript wrapper complexity**: Auto-generated .d.ts may be sufficient, or manual wrapper for better DX. **Default**: Auto-generated, add manual wrapper only if needed.

## Blockers

### High Priority (Phase 1)
- **Unknown actual WASM size**: All estimates are extrapolations without real compilation data. **Risk**: Actual size could be 2-3x estimates, invalidating Cloudflare Workers viability.
  - **Mitigation**: Phase 1 prototype measures minimal Clang LibTooling WASM size immediately.
  - **Go/No-Go**: If minimal &gt; 10MB Brotli, Cloudflare Workers not viable. Proceed with CDN-only deployment.

- **Clang/LLVM WASM compatibility**: Assumed to work based on research, but untested with this codebase.
  - **Mitigation**: Phase 1 prototype validates Clang LibTooling compiles to WASM.
  - **Fallback**: If blockers found, explore alternative parsing or server-side only.

### Medium Priority (Phase 2)
- **embind TypeScript generation**: Assumed --emit-tsd produces complete types, but untested.
  - **Mitigation**: Phase 2 validates auto-generation. Manual .d.ts authoring if needed.

- **TranspilerAPI refactoring**: main.cpp logic must be refactored into library function for WASM.
  - **Mitigation**: Phase 2 task. Requires no filesystem I/O, in-memory only.

### Low Priority (Phase 4+)
- **Cloudflare Workers size limit**: Free tier 1MB gzip insufficient, paid tier 3MB Brotli borderline.
  - **Mitigation**: Phase 1 size validation. Fallback: CDN-only or Cloudflare Pages Functions.

## Next Step

**Implement Phase 1: Build System Setup & Prototype**

### Immediate Actions
1. **Create minimal WASM prototype** (src/main_wasm_minimal.cpp):
   - Barebones Clang AST parsing only (no transpilation logic)
   - CMake target: cpptoc-wasm-minimal-prototype
   - Build with: emcmake cmake -B build-wasm && emmake cmake --build build-wasm
   - Measure: ls -lh cpptoc-minimal.wasm && gzip -c cpptoc-minimal.wasm | wc -c && brotli -c cpptoc-minimal.wasm | wc -c

2. **Validate size against Cloudflare limits**:
   - Target: ≤ 10MB uncompressed, ≤ 3MB Brotli compressed
   - If successful: Proceed with full implementation
   - If exceeds: Document limitation, skip Cloudflare Workers, focus on CDN deployment

3. **Configure dual WASM targets in CMakeLists.txt**:
   - Add EMSCRIPTEN detection block
   - Define cpptoc-wasm-minimal (size-optimized) and cpptoc-wasm-full (performance-optimized)
   - Link embind (--bind) and enable TypeScript generation (--emit-tsd)

4. **Document build process**:
   - Update README.md with WASM build instructions
   - Create scripts/build-wasm.sh helper script
   - Test on clean checkout

### Success Criteria for Phase 1
- ✅ Minimal WASM prototype compiles successfully
- ✅ Actual size measured and documented
- ✅ Cloudflare Workers feasibility determined (yes/no with evidence)
- ✅ Dual CMake targets configured and tested
- ✅ Build documentation complete

### Timeline Estimate
- Phase 1: 2-3 days (prototype, measurement, CMake configuration)
- Phase 2: 3-4 days (embind API, TypeScript wrapper, refactoring)
- Phase 3: 2-3 days (NPM package, README, examples)
- Phase 4: 1-2 days (Cloudflare Worker, optional)
- Phase 5: 3-4 days (website components, playground integration)
- Phase 6: 3-4 days (tests, CI/CD, performance benchmarks)
- Phase 7: 2-3 days (documentation, release automation, publish)

**Total**: ~16-23 days (3-4 weeks) for full implementation, assuming no major blockers.

---

## Plan Confidence: 85%

### High Confidence (95%+)
- Emscripten build process and optimization flags (documented, verified in research)
- Cloudflare Workers limits and constraints (official documentation)
- Astro/Vite WASM compatibility (tested in ecosystem, website already uses ESM)
- NPM dual package structure (established patterns, well-documented)
- GitHub Actions CI/CD integration (standard workflow, Emscripten action available)

### Medium Confidence (70-85%)
- embind TypeScript generation quality (documented feature, but untested for this project)
- ACSL annotator size estimates (based on source analysis, not compiled measurements)
- Compression ratios (measured from sql.js, but Clang tooling may differ)
- Load time acceptability (3-5 seconds is common for WASM apps, but no user research)

### Low Confidence (50-70%)
- Clang LibTooling WASM size (NO ACTUAL DATA, extrapolated from native sizes)
- Cloudflare Workers feasibility (depends on unmeasured size, borderline)
- Selective Clang library linking (unknown if tree shaking can reduce size 30-60%)
- Code splitting implementation effort (Emscripten module splitting untested)

### Critical Gap
**Phase 1 prototype is essential** to validate all low-confidence assumptions. Without actual size measurement, Cloudflare Workers deployment remains speculative.

---

## References

### Planning Input
- Research findings: `.prompts/032-wasm-library-research/wasm-library-research.md`
- Research summary: `.prompts/032-wasm-library-research/SUMMARY.md`
- Planning prompt: `.prompts/033-wasm-library-plan/033-wasm-library-plan.md`

### Project Context
- Current version: v1.22.0 (5 ACSL phases complete)
- Build system: CMake, Clang/LLVM 15+
- Website: Astro 5.16.6 + React 19.2.3, deployed to GitHub Pages
- Repository: https://github.com/o2alexanderfedin/hupyy-cpp-to-c

### Key Research Sources
- [Emscripten Documentation](https://emscripten.org/docs/)
- [Cloudflare Workers Limits](https://developers.cloudflare.com/workers/platform/limits/)
- [Emscripten Embind](https://emscripten.org/docs/porting/connecting_cpp_and_javascript/embind.html)
- [FFmpeg.wasm](https://github.com/ffmpegwasm/ffmpeg.wasm) (20MB WASM benchmark)
- [sql.js](https://github.com/sql-js/sql.js) (655KB → 277KB Brotli benchmark)

---

## Output Files

This planning phase produces:

1. **wasm-library-plan.md**: Comprehensive implementation plan (this file's companion)
   - 8 planning sections (build system, API, NPM, Cloudflare, website, testing, docs, CI/CD)
   - 7 implementation phases with tasks, deliverables, verification criteria
   - Dependencies, risks, open questions, assumptions

2. **SUMMARY.md**: Executive summary (this file)
   - Key decisions and rationale
   - User approvals needed
   - Blockers and mitigations
   - Next step (Phase 1 prototype)

Both files ready for implementation. Proceed to Phase 1: Build System Setup & Prototype.

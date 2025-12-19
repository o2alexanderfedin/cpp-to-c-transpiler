# Transpiler Website Plan - Executive Summary

**Created**: 2025-12-19
**Status**: Ready for Execution
**Framework**: Astro (monorepo)
**Timeline**: 4-5 weeks

---

## One-Liner

Build a modern documentation and demo website for the C++ to C transpiler using **Astro** (component islands), **CodeMirror 6** (code editor), and **Vercel** (deployment with native COOP/COEP headers), implementing a **monorepo architecture** with WebAssembly-powered interactive playground.

---

## 5 Key Phases

### Phase 1: Foundation & Setup (3-4 days)
Initialize Astro project in `website/` directory, configure Vercel deployment with COOP/COEP headers, create responsive landing page and basic layout structure.

**Deliverables**: Astro project live on Vercel, headers verified, landing page functional

### Phase 2: WebAssembly Integration (4-5 days)
Compile transpiler to multi-threaded WASM with Emscripten, create WASM loading infrastructure, build transpiler JavaScript API, integrate into CI/CD pipeline.

**Deliverables**: WASM builds automatically, threading verified, transpilation API functional

### Phase 3: Interactive Code Playground (5-6 days)
Implement CodeMirror 6 split-pane editor (C++ input | C output), connect to transpiler WASM, add example code snippets, create dedicated playground page.

**Deliverables**: Fully functional playground with real-time transpilation, 5+ examples

### Phase 4: Documentation Content Migration (4-5 days)
Migrate existing docs to MDX format, create sidebar navigation, convert API reference, document core features, add FAQ and troubleshooting.

**Deliverables**: Complete documentation site with all existing content migrated

### Phase 5: Example Gallery & Polish (3-4 days)
Showcase 5 real-world examples (json-parser, logger, test-framework, string-formatter, resource-manager), optimize performance, finalize SEO and accessibility.

**Deliverables**: Lighthouse 90+ scores, example gallery live, production-ready

---

## Architecture Highlights

**Monorepo Structure**:
```
hupyy-cpp-to-c/
├── src/          # Transpiler source
├── website/      # NEW: Astro site
│   ├── public/wasm/   # Transpiler WASM artifacts
│   ├── src/
│   │   ├── components/  # React islands (CodePlayground)
│   │   ├── pages/       # Astro pages + MDX docs
│   │   └── utils/       # WASM loader, transpiler API
│   └── vercel.json      # COOP/COEP headers
└── .github/workflows/
    └── deploy-website.yml  # CI/CD
```

**Tech Stack**:
- **Framework**: Astro 4.x (static generation + component islands)
- **Code Editor**: CodeMirror 6 (300KB vs Monaco 2MB+)
- **Deployment**: Vercel (native COOP/COEP headers, no workarounds)
- **Headers**: COEP: credentialless + COOP: same-origin (third-party compatible)
- **WebAssembly**: Emscripten with pthread support for multi-threading

---

## Decisions Needed

1. **Custom Domain** (by Phase 1): Do you want a custom domain (e.g., cpptoc.dev)?
   - Current: Will use Vercel subdomain
   - Decision: Can add custom domain later

2. **Analytics Platform** (by Phase 5): Vercel Analytics, Google Analytics, or Plausible?
   - Recommendation: Vercel Analytics (privacy-friendly, zero config)
   - Decision: Approve or specify alternative

3. **Mobile Playground** (by Phase 3): Should playground work on mobile?
   - Current assumption: Desktop primary, mobile read-only
   - Decision: Confirm or request mobile editing support

4. **Versioning** (by Phase 5): Support multiple transpiler versions on website?
   - Current assumption: Single latest version
   - Decision: Confirm or plan for version selector

---

## Blockers & Risks

### Blockers (None Critical)
- **Emscripten Setup**: Need Emscripten SDK installed in CI (GitHub Actions)
  - **Mitigation**: Use `mymindstorm/setup-emsdk@v12` action (proven solution)

- **WASM File Size**: Unknown transpiler WASM size
  - **Mitigation**: Will measure in Phase 2, apply compression if >5MB

### Risks (All Mitigated)
- **Browser Compatibility**: Older browsers lack SharedArrayBuffer
  - **Mitigation**: Add compatibility check, show friendly error message

- **Performance**: Large transpilations may be slow
  - **Mitigation**: Add timeout, progress indicator, optimize with worker threads

- **Vercel Bandwidth**: Free tier 100GB/month limit
  - **Mitigation**: Monitor usage, upgrade to paid ($20/month) or switch to Cloudflare (unlimited)

---

## Success Criteria

**Must Have**:
- ✅ Website deployed at production URL
- ✅ Interactive playground transpiles C++ to C in browser
- ✅ All 5 real-world examples showcased
- ✅ Existing documentation migrated and accessible
- ✅ Lighthouse Performance score 90+
- ✅ Mobile-responsive design
- ✅ crossOriginIsolated === true (headers working)

**Nice to Have**:
- Search functionality in docs
- Syntax highlighting comparison view
- Download transpiled code as .zip
- Video tutorial embed

---

## Next Step

**Execute Phase 1: Foundation & Setup**

1. Create `website/` directory
2. Initialize Astro project with TypeScript
3. Add React and Tailwind integrations
4. Configure Vercel deployment with COOP/COEP headers
5. Create landing page with hero section
6. Verify headers in production

**First Task**: Run `npm create astro@latest` in `website/` directory

**Timeline**: Start immediately, complete Phase 1 in 3-4 days

---

## Resources

**Research Document**: `.prompts/022-transpiler-website-research/transpiler-website-research.md`
**Full Plan**: `.prompts/023-transpiler-website-plan/transpiler-website-plan.md`
**Real-World Examples**: `tests/real-world/` (5 projects, 10,000+ LOC)
**Existing Docs**: `docs/` (user guides, API reference, features)

**Key References**:
- Astro Docs: https://docs.astro.build
- CodeMirror 6: https://codemirror.net
- Vercel Headers: https://vercel.com/docs/concepts/edge-network/headers
- Emscripten Pthreads: https://emscripten.org/docs/porting/pthreads.html

---

**Plan Status**: ✅ APPROVED - Ready for Phase 1 Implementation

*Created with Claude Code | December 2025*

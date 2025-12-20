# Transpiler Website Implementation Plan

**Created**: 2025-12-19
**Status**: ✅ APPROVED - Ready for Execution
**Timeline**: 4-5 weeks (19-24 days)

---

## Quick Navigation

| Document | Purpose | When to Use |
|----------|---------|------------|
| **[SUMMARY.md](./SUMMARY.md)** | Executive overview, one-liner, key decisions | Management review, stakeholder communication |
| **[transpiler-website-plan.md](./transpiler-website-plan.md)** | Complete implementation plan (952 lines) | Primary reference during implementation |
| **[QUICK_REFERENCE.md](./QUICK_REFERENCE.md)** | Cheat sheet with commands and checkpoints | Daily implementation, quick lookups |
| **[VERIFICATION.md](./VERIFICATION.md)** | Requirements coverage and quality check | Plan approval, completeness audit |

---

## Plan Overview

### What We're Building

A modern documentation and demonstration website for the C++ to C transpiler featuring:

- **Interactive WebAssembly Playground**: Transpile C++ to C directly in the browser
- **Comprehensive Documentation**: Migrated from existing docs/ with enhanced navigation
- **Example Gallery**: Showcase 5 real-world projects (10,000+ LOC)
- **Fast Performance**: Lighthouse 90+ scores, <3s to interactive
- **Mobile Responsive**: Works on all devices

### Technology Stack

| Layer | Technology |
|-------|-----------|
| Framework | Astro 4.x (component islands) |
| UI Components | React 18 |
| Code Editor | CodeMirror 6 (300KB) |
| Styling | Tailwind CSS |
| WebAssembly | Emscripten (pthread) |
| Deployment | Vercel (COOP/COEP headers) |
| CI/CD | GitHub Actions |

### Architecture

**Monorepo Approach** - Website lives in `website/` directory within main transpiler repository:

```
hupyy-cpp-to-c/
├── src/              # Transpiler source (existing)
├── website/          # NEW: Astro site
│   ├── public/wasm/  # Transpiler WASM
│   ├── src/
│   │   ├── components/  # React islands
│   │   ├── pages/       # Astro + MDX
│   │   └── utils/       # WASM loader
│   └── vercel.json   # Headers config
└── .github/workflows/
    └── deploy-website.yml  # CI/CD
```

---

## Implementation Phases

### Phase 1: Foundation & Setup (3-4 days)

**Goal**: Astro project initialized, deployed to Vercel with correct headers

**Key Tasks**:
- Initialize Astro with TypeScript, React, Tailwind
- Configure Vercel with COOP/COEP headers
- Create landing page and basic layout
- Verify crossOriginIsolated === true

**Deliverable**: Live website with verified headers

---

### Phase 2: WebAssembly Integration (4-5 days)

**Goal**: Transpiler compiled to WASM, loading infrastructure working

**Key Tasks**:
- Build transpiler with Emscripten (pthread enabled)
- Create WASM loader and transpiler API
- Add GitHub Actions workflow for automated builds
- Verify multi-threading functional

**Deliverable**: WASM transpilation working in test page

---

### Phase 3: Interactive Code Playground (5-6 days)

**Goal**: Full code playground with real-time transpilation

**Key Tasks**:
- Install and configure CodeMirror 6
- Build split-pane editor (C++ | C)
- Connect to transpiler WASM
- Add 5+ example code snippets
- Create playground page

**Deliverable**: Working playground at /playground

---

### Phase 4: Documentation Content Migration (4-5 days)

**Goal**: Complete documentation site with navigation

**Key Tasks**:
- Set up docs structure with sidebar
- Migrate existing docs to MDX
- Create API reference pages
- Document core features
- Add FAQ and troubleshooting

**Deliverable**: Comprehensive docs at /docs

---

### Phase 5: Example Gallery & Polish (3-4 days)

**Goal**: Production-ready site with optimized performance

**Key Tasks**:
- Create example gallery (5 real-world projects)
- Performance optimization (Lighthouse 90+)
- SEO and accessibility
- Final testing across browsers
- Production launch

**Deliverable**: Live production website

---

## Key Decisions (Locked In)

### Why Astro?

- ✅ Component islands for optimal performance
- ✅ Full TypeScript and React support
- ✅ No header limitations (unlike Next.js static export)
- ✅ Excellent build performance

### Why CodeMirror 6?

- ✅ 6-8x smaller than Monaco (300KB vs 2MB+)
- ✅ Industry validated (Replit, Sourcegraph migrated)
- ✅ Better mobile performance
- ✅ Sufficient features for C++ syntax

### Why Vercel?

- ✅ Native COOP/COEP header support (no workarounds)
- ✅ Zero configuration for Astro
- ✅ Preview deployments for every push
- ✅ Free tier sufficient (100GB/month)

### Why Monorepo?

- ✅ Simpler for solo developer (no submodules)
- ✅ Docs stay in sync with code
- ✅ Single CI/CD pipeline
- ✅ Can refactor later if needed

---

## Success Criteria

### Must Have (Launch Blockers)

- [ ] Website deployed and accessible
- [ ] Playground transpiles C++ to C in browser
- [ ] All 5 real-world examples showcased
- [ ] Existing documentation migrated
- [ ] Lighthouse Performance 90+
- [ ] Mobile responsive
- [ ] crossOriginIsolated === true

### Nice to Have (Iteration 2)

- [ ] Search functionality in docs
- [ ] Download transpiled code as .zip
- [ ] Syntax comparison view
- [ ] Video tutorials
- [ ] Blog for announcements

---

## Getting Started

### Prerequisites

- [x] Transpiler source code (exists in src/)
- [x] Real-world examples (exist in tests/real-world/)
- [x] Existing documentation (exists in docs/)
- [ ] Vercel account (create free account)
- [ ] Emscripten SDK (install for WASM build)

### First Steps

1. **Read the Plan**: Start with [SUMMARY.md](./SUMMARY.md) for overview
2. **Review Architecture**: Read [transpiler-website-plan.md](./transpiler-website-plan.md) Architecture section
3. **Execute Phase 1**: Follow Phase 1 tasks in detail
4. **Use Quick Reference**: Keep [QUICK_REFERENCE.md](./QUICK_REFERENCE.md) open during implementation

### Commands to Start

```bash
# Navigate to project root
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c

# Initialize Astro (Phase 1, Task 1.1)
npm create astro@latest website

# Follow prompts:
# - TypeScript: Strict
# - Template: Minimal/Empty
# - Install dependencies: Yes

# Add integrations
cd website
npx astro add react
npx astro add tailwind
```

---

## Resources

### Internal Documentation

- [Research Findings](../.prompts/022-transpiler-website-research/transpiler-website-research.md) - Technology research that informed this plan
- [Existing Docs](../../docs/) - Content to be migrated
- [Real-World Examples](../../tests/real-world/) - 5 projects to showcase

### External References

- **Astro**: https://docs.astro.build
- **CodeMirror**: https://codemirror.net
- **Emscripten**: https://emscripten.org/docs/porting/pthreads.html
- **Vercel**: https://vercel.com/docs

---

## Progress Tracking

Use this checklist to track phase completion:

- [ ] **Phase 1**: Foundation & Setup (3-4 days)
  - [ ] Astro initialized
  - [ ] Vercel deployed
  - [ ] Headers verified
  - [ ] Landing page live

- [ ] **Phase 2**: WebAssembly Integration (4-5 days)
  - [ ] WASM compiled
  - [ ] Loader implemented
  - [ ] CI/CD configured
  - [ ] Threading verified

- [ ] **Phase 3**: Interactive Playground (5-6 days)
  - [ ] CodeMirror installed
  - [ ] Split editor working
  - [ ] Examples added
  - [ ] Playground page live

- [ ] **Phase 4**: Documentation Migration (4-5 days)
  - [ ] Docs structure created
  - [ ] Content migrated
  - [ ] Navigation working
  - [ ] Links validated

- [ ] **Phase 5**: Gallery & Polish (3-4 days)
  - [ ] Examples showcased
  - [ ] Performance optimized
  - [ ] SEO/accessibility complete
  - [ ] Production launched

---

## Support & Questions

### Open Questions (Decisions Needed)

1. **Custom Domain**: Use Vercel subdomain or configure custom domain?
2. **Analytics**: Vercel Analytics, Google Analytics, or Plausible?
3. **Mobile Playground**: Full editing support or desktop-only?
4. **Versioning**: Support multiple transpiler versions on website?

### Contact

For questions or clarifications during implementation:
- Review [VERIFICATION.md](./VERIFICATION.md) for requirements coverage
- Check [QUICK_REFERENCE.md](./QUICK_REFERENCE.md) for common solutions
- Consult [transpiler-website-plan.md](./transpiler-website-plan.md) for detailed guidance

---

## Document History

| Date | Version | Changes |
|------|---------|---------|
| 2025-12-19 | 1.0 | Initial plan created, all 4 documents delivered |

---

**Status**: ✅ READY FOR PHASE 1 EXECUTION

**Next Action**: Initialize Astro project in `website/` directory

*Plan created with Claude Code | December 2025*

# Transpiler Website - Quick Reference

**Status**: Ready for Implementation
**Timeline**: 4-5 weeks | 19-24 days
**Start Date**: TBD
**Target Launch**: TBD

---

## Phase Overview

| Phase | Duration | Key Deliverable |
|-------|----------|----------------|
| **1. Foundation** | 3-4 days | Astro + Vercel deployment with COOP/COEP headers |
| **2. WASM** | 4-5 days | Transpiler compiled to multi-threaded WebAssembly |
| **3. Playground** | 5-6 days | Interactive code editor with real-time transpilation |
| **4. Documentation** | 4-5 days | Complete docs migrated to MDX with navigation |
| **5. Gallery & Polish** | 3-4 days | 5 examples showcased, Lighthouse 90+ scores |

---

## Tech Stack Decisions (Locked)

- **Framework**: Astro 4.x (component islands)
- **Editor**: CodeMirror 6 (NOT Monaco - 6x smaller)
- **Deployment**: Vercel (NOT GitHub Pages - native headers)
- **Architecture**: Monorepo (website/ in main repo)
- **Headers**: COEP: credentialless + COOP: same-origin

---

## Critical Commands

### Phase 1: Initialize Astro
```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c
npm create astro@latest website
cd website
npx astro add react
npx astro add tailwind
```

### Phase 2: Build WASM
```bash
# Create scripts/build-wasm.sh
emcc src/*.cpp -o website/public/wasm/transpiler.js \
  -pthread -sPTHREAD_POOL_SIZE=navigator.hardwareConcurrency \
  -sPROXY_TO_PTHREAD -sMALLOC=mimalloc -O3 -s WASM=1
```

### Phase 3: Install CodeMirror
```bash
cd website
npm install @codemirror/state @codemirror/view \
  @codemirror/lang-cpp @codemirror/theme-one-dark
```

### Verify Deployment
```javascript
// Browser console
console.log('Cross-origin isolated:', crossOriginIsolated);
// Should be: true
```

---

## File Structure Checklist

```
website/
├── public/
│   ├── wasm/                 ← Phase 2: WASM artifacts
│   └── examples/             ← Phase 3: Code snippets
├── src/
│   ├── components/
│   │   ├── CodePlayground.tsx    ← Phase 3
│   │   └── CodeEditor.tsx        ← Phase 3
│   ├── pages/
│   │   ├── index.astro           ← Phase 1
│   │   ├── playground.astro      ← Phase 3
│   │   ├── docs/                 ← Phase 4
│   │   └── examples/             ← Phase 5
│   └── utils/
│       ├── wasm-loader.ts        ← Phase 2
│       └── transpiler-api.ts     ← Phase 2
├── vercel.json               ← Phase 1: Headers config
└── package.json              ← Phase 1
```

---

## vercel.json Template

```json
{
  "headers": [
    {
      "source": "/:path*",
      "headers": [
        {
          "key": "Cross-Origin-Opener-Policy",
          "value": "same-origin"
        },
        {
          "key": "Cross-Origin-Embedder-Policy",
          "value": "credentialless"
        }
      ]
    }
  ]
}
```

---

## Success Checkpoints

**Phase 1**:
- [ ] Astro site deployed to Vercel
- [ ] `crossOriginIsolated === true` in console
- [ ] Landing page renders correctly

**Phase 2**:
- [ ] WASM files generated (transpiler.js, .wasm, .worker.js)
- [ ] CI/CD builds WASM automatically
- [ ] Test transpilation works

**Phase 3**:
- [ ] Playground transpiles C++ to C
- [ ] 5+ example snippets working
- [ ] Error handling functional

**Phase 4**:
- [ ] All docs/ content migrated to MDX
- [ ] Sidebar navigation works
- [ ] No broken links

**Phase 5**:
- [ ] 5 real-world examples showcased
- [ ] Lighthouse Performance: 90+
- [ ] SEO and accessibility: 95+

---

## Common Issues & Solutions

**Issue**: crossOriginIsolated is false
**Solution**: Check vercel.json deployed, verify headers in Network tab

**Issue**: WASM fails to load
**Solution**: Check CORS headers, verify .wasm file in public/wasm/

**Issue**: Playground is slow
**Solution**: Add loading spinner, implement debouncing (500ms)

**Issue**: CodeMirror bundle too large
**Solution**: Code splitting configured in astro.config.mjs

---

## Resources

**Full Plan**: `transpiler-website-plan.md` (952 lines)
**Summary**: `SUMMARY.md` (executive overview)
**Research**: `../022-transpiler-website-research/transpiler-website-research.md`

**External Docs**:
- Astro: https://docs.astro.build
- CodeMirror: https://codemirror.net
- Emscripten: https://emscripten.org/docs/porting/pthreads.html
- Vercel: https://vercel.com/docs

---

**Next Action**: Execute Phase 1 - Initialize Astro project in `website/` directory

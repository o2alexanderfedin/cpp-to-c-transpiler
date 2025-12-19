# Research Verification Checklist

## Completeness Check ✓

- [x] All enumerated frameworks documented with WebAssembly support evidence
  - Astro: Full WebAssembly support, headers via platform config
  - Next.js: WebAssembly support but static export header limitation identified
  - Docusaurus: WebAssembly support, headers via platform config
  - VitePress: WebAssembly support (Vite-based), headers via platform config

- [x] Each git submodule approach evaluated against ALL requirements
  - Website as submodule
  - Transpiler as submodule
  - Monorepo (no submodules)
  - Artifacts-only approach
  - All evaluated with pros/cons and best-for scenarios

- [x] Official documentation cited for critical claims (especially COOP/COEP)
  - MDN: SharedArrayBuffer, COOP/COEP headers
  - web.dev: COOP/COEP explainer
  - Emscripten: pthreads documentation
  - Framework official docs: All frameworks referenced

- [x] Contradictory information resolved or flagged
  - COEP: require-corp vs credentialless - recommended credentialless for compatibility
  - No unresolved contradictions

## Source Verification ✓

- [x] Primary claims backed by official/authoritative sources
  - All framework capabilities: Official docs
  - WebAssembly requirements: Emscripten + MDN + web.dev
  - Deployment platforms: Official platform documentation
  - Code editor comparison: npm-compare + Replit/Sourcegraph case studies

- [x] Version numbers and dates included where relevant
  - Research date: 2025-12-19
  - Browser support: December 2021 baseline
  - All search queries used 2025 for recent info

- [x] Actual URLs provided (not just "search for X")
  - All sources include full URLs in findings
  - Code examples reference specific documentation

- [x] Distinguish verified facts from assumptions
  - Verified claims section in metadata
  - Assumptions section explicitly lists solo developer context, etc.

## Blind Spots Review ✓

- [x] Are there static site generators I didn't investigate?
  - Considered Hugo, Eleventy - excluded due to JavaScript/WebAssembly ecosystem fit
  - Focused on JavaScript-based frameworks for best WebAssembly integration

- [x] Did I check for multiple deployment platforms?
  - GitHub Pages: Yes (service worker workaround)
  - Vercel: Yes (native headers)
  - Netlify: Yes (native headers)
  - Cloudflare Pages: Yes (native headers, threading limitation noted)

- [x] Did I verify COOP/COEP header support claims with actual docs?
  - Vercel: Verified with official docs (vercel.json)
  - Netlify: Verified with official docs (netlify.toml, _headers)
  - Cloudflare: Verified with official docs (_headers)
  - GitHub Pages: Verified NO native support + service worker workaround

- [x] Did I look for recent WebAssembly multi-threading updates?
  - Used 2025 search queries
  - Found March 2025 article on COOP/COEP for static hosting
  - Emscripten latest documentation consulted

## Critical Claims Audit ✓

For statements like "X doesn't support Y":

- [x] Next.js static export doesn't support headers
  - Verified: Next.js official docs state headers() only works with server, not static export
  - Source: https://nextjs.org/docs/app/guides/static-exports

- [x] GitHub Pages doesn't support custom headers
  - Verified: Community discussion confirms no native support
  - Workaround documented: service worker approach
  - Source: https://github.com/orgs/community/discussions/13309

- [x] Cloudflare Workers don't support threading
  - Verified: Cloudflare docs state Workers run in single thread, no Web Worker API
  - Source: https://developers.cloudflare.com/workers/runtime-apis/webassembly/

- [x] CodeMirror 6 is 6-8x smaller than Monaco
  - Verified: Replit case study shows 51.17 MB → 8.23 MB (6x reduction)
  - Source: https://blog.replit.com/codemirror

## Success Criteria Verification ✓

- [x] Top 3 framework options clearly ranked with rationale
  1. Astro (recommended)
  2. Docusaurus (if versioning needed)
  3. VitePress (if Vue preferred)
  Next.js explicitly NOT recommended due to static export limitation

- [x] WebAssembly multi-threading feasibility conclusively determined
  - Feasible: Yes, with COOP/COEP headers
  - Browser support: Widely available since December 2021
  - Compilation: Emscripten with -pthread flag
  - Deployment: Native header support required (Vercel/Netlify recommended)

- [x] COOP/COEP header configuration approach documented for each framework
  - All frameworks: Require platform-specific configuration
  - Vercel: vercel.json (code example provided)
  - Netlify: netlify.toml or _headers (code examples provided)
  - Cloudflare: _headers file (documented)
  - GitHub Pages: Service worker workaround (documented with trade-offs)

- [x] Git submodule best practice identified with pros/cons
  - Recommendation: Monorepo (no submodules) for solo developer
  - Alternative: Artifacts-only for production
  - All 4 approaches documented with pros/cons and best-for scenarios

- [x] Deployment platform comparison with WASM support matrix
  - Comparison matrix provided with 5 criteria
  - Each platform rated on header support, WASM multi-threading, bandwidth, DX, build features
  - Best-for recommendations included

- [x] Code examples for critical configurations
  - Vercel header config (vercel.json)
  - Netlify header config (netlify.toml + _headers)
  - Emscripten compilation flags
  - Cross-origin isolation verification
  - CodeMirror 6 setup
  - Astro configuration
  - GitHub Actions workflow

- [x] Ready for planning phase to design architecture
  - SUMMARY.md created with next step: transpiler-website-plan.md
  - All decisions and blockers identified
  - Implementation path outlined

## Quality Assurance ✓

- Research date verified: 2025-12-19
- All search queries used correct year (2025)
- Sources from 2024-2025 prioritized for evolving topics
- Official documentation used for all framework/platform claims
- Real-world case studies validate recommendations
- Negative claims double-checked with official sources
- Assumptions explicitly stated
- Open questions identified for user clarification
- Dependencies documented
- Confidence levels provided for each research area

## Deliverables ✓

- [x] transpiler-website-research.md (1798 lines, 68K, comprehensive findings)
- [x] SUMMARY.md (38 lines, 3.1K, executive summary with next steps)
- [x] Code examples for all critical configurations
- [x] Recommendations ranked by priority
- [x] Metadata with confidence levels, sources, verified claims

**Research Status: COMPLETE**
**Ready for: Planning phase (transpiler-website-plan.md)**

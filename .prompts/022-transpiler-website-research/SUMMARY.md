# Transpiler Website Technology Research

**Astro + Vercel + CodeMirror 6 recommended for optimal WebAssembly multi-threading with zero-config native headers**

## Key Findings

- **Framework Winner: Astro** - Component islands architecture provides best balance of static performance and interactive playground flexibility, with full WebAssembly support and no header configuration limitations (unlike Next.js static exports)

- **Critical Deployment Requirement: Native COOP/COEP Headers** - WebAssembly multi-threading absolutely requires Cross-Origin-Opener-Policy: same-origin and Cross-Origin-Embedder-Policy: credentialless headers. Vercel and Netlify provide native support via configuration files; GitHub Pages requires service worker workaround with page reload penalty.

- **Code Editor: CodeMirror 6 Dominates** - 6-8x smaller bundle size than Monaco (300KB vs 2+ MB), validated by Sourcegraph and Replit migrations. For C++ to C transpilation demo, Monaco's VS Code features are overkill while CodeMirror 6 provides sufficient syntax highlighting with superior performance.

- **Repository Architecture: Monorepo Simplest** - For solo developer, website/ directory in main hupyy-cpp-to-c repository eliminates submodule complexity while keeping documentation in sync with code. Git submodules add unnecessary coordination overhead.

## Decisions Needed

**Framework Selection**: Astro recommended, but verify if documentation versioning is required. If yes, Docusaurus's built-in versioning feature might swing decision despite being less flexible for custom playground components.

**Deployment Platform**: Vercel (recommended for ease) vs Netlify (equivalent capabilities) - choose based on preference. Both provide native header support, preview deployments, and generous free tiers (100 GB bandwidth).

**Alternative consideration**: Cloudflare Pages offers unlimited bandwidth on free tier but has less mature Astro ecosystem support compared to Vercel/Netlify.

## Blockers

**Browser Compatibility**: SharedArrayBuffer requires modern browsers (Chrome, Firefox, Safari, Edge December 2021+). Documentation site should detect and warn users on older browsers.

**Third-Party Resources**: COEP headers can break external resources (fonts, analytics, embeds) without proper CORS/CORP headers. Using COEP: credentialless instead of require-corp mitigates this, but testing with all third-party integrations is critical before production deployment.

**Emscripten Build Requirements**: Transpiler must be compilable with Emscripten pthread support. Verify current build system can add -pthread, -sPROXY_TO_PTHREAD, and -sMALLOC=mimalloc flags without conflicts.

## Next Step

Create transpiler-website-plan.md to architect the selected Astro + Vercel + CodeMirror 6 solution with:
- Detailed component structure (Playground, Examples Gallery, Getting Started, API Reference)
- WASM build integration into CI/CD pipeline
- Header verification and cross-origin isolation testing strategy
- Progressive enhancement plan for browsers without SharedArrayBuffer support
- Performance budgets (target < 3s initial load, < 500ms transpilation for small examples)

# Implement: WebAssembly Library (All Phases)

## Objective

Implement the complete WebAssembly library for the hupyy-cpp-to-c transpiler following the phased plan, including dual builds (Cloudflare minimal + website full), JavaScript/TypeScript glue code, NPM package, Cloudflare Worker deployment, website integration, and comprehensive documentation.

## Context

**Research Findings:**
@.prompts/032-wasm-library-research/wasm-library-research.md

**Implementation Plan:**
@.prompts/033-wasm-library-plan/wasm-library-plan.md

**Project State:**
- Version: v1.22.0 (Phases 1-5 complete)
- Build system: CMake
- Website: Astro-based (@website/)
- Target directory: Create new `wasm/` directory in project root

## Implementation Requirements

### Directory Structure to Create

```
wasm/
├── CMakeLists.txt               # WASM build configuration
├── emscripten-toolchain.cmake   # Emscripten CMake toolchain
├── bindings/
│   ├── minimal.cpp              # embind for minimal build
│   └── full.cpp                 # embind for full build
├── glue/
│   ├── src/
│   │   ├── index.ts             # Main entry point
│   │   ├── transpiler.ts        # Transpiler class
│   │   ├── types.ts             # TypeScript types
│   │   ├── errors.ts            # Error handling
│   │   └── utils.ts             # Helpers
│   ├── package.json
│   ├── tsconfig.json
│   └── README.md
├── cloudflare-worker/
│   ├── src/
│   │   └── index.ts             # Worker entry point
│   ├── wrangler.toml
│   └── package.json
├── tests/
│   ├── unit/
│   ├── integration/
│   └── e2e/
├── docs/
│   ├── README.md                # Main documentation
│   ├── API.md                   # TypeScript API reference
│   ├── CLOUDFLARE.md            # Worker deployment
│   ├── WEBSITE.md               # Astro integration
│   ├── BUILDING.md              # Build from source
│   └── EXAMPLES.md              # Usage examples
├── .github/
│   └── workflows/
│       └── wasm-build.yml       # CI/CD pipeline
├── scripts/
│   ├── build-minimal.sh         # Build minimal WASM
│   ├── build-full.sh            # Build full WASM
│   └── size-check.sh            # Validate bundle sizes
└── README.md                    # Overview
```

## Implementation Phases

### Phase 1: Build System Setup

**Tasks:**
1. Create `wasm/` directory structure
2. Create `wasm/CMakeLists.txt` with dual targets (minimal + full)
3. Create `wasm/emscripten-toolchain.cmake`
4. Configure build flags based on plan
5. Create build scripts (`scripts/build-minimal.sh`, `scripts/build-full.sh`)
6. Test minimal build with basic C++ code
7. Measure baseline WASM size

**Implementation details from plan:**
- Use Emscripten flags from research (e.g., `-Oz`, `-s MODULARIZE=1`)
- Link only necessary Clang/LLVM libraries
- Conditional compilation for ACSL annotators
- Separate output directories for minimal/full

**Verification:**
- [ ] `wasm-minimal` target builds successfully
- [ ] `wasm-full` target builds successfully
- [ ] Minimal build size meets Cloudflare limit (< 2MB compressed)
- [ ] WASM files are valid (check with `wasm-validate`)

**Files created:**
- `wasm/CMakeLists.txt`
- `wasm/emscripten-toolchain.cmake`
- `wasm/scripts/build-minimal.sh`
- `wasm/scripts/build-full.sh`
- `wasm/scripts/size-check.sh`

---

### Phase 2: JavaScript/TypeScript API

**Tasks:**
1. Create `wasm/bindings/minimal.cpp` with embind definitions
2. Create `wasm/bindings/full.cpp` with embind definitions
3. Create TypeScript wrapper (`wasm/glue/src/`)
4. Implement error handling across WASM boundary
5. Create type definitions (`types.ts`)
6. Implement async initialization pattern
7. Add memory management (dispose pattern)
8. Build TypeScript to JS with bundler

**embind C++ example:**
```cpp
// wasm/bindings/minimal.cpp
#include <emscripten/bind.h>
#include "Transpiler.h"

using namespace emscripten;

EMSCRIPTEN_BINDINGS(cpptoc_minimal) {
  class_<Transpiler>("Transpiler")
    .constructor<>()
    .function("transpile", &Transpiler::transpile)
    .function("getErrors", &Transpiler::getErrors)
    .function("getWarnings", &Transpiler::getWarnings);

  class_<TranspileResult>("TranspileResult")
    .property("cCode", &TranspileResult::cCode)
    .property("hasErrors", &TranspileResult::hasErrors);
}
```

**TypeScript wrapper example:**
```typescript
// wasm/glue/src/transpiler.ts
export class Transpiler {
  private instance: any;
  private disposed = false;

  private constructor(instance: any) {
    this.instance = instance;
  }

  static async create(options?: {minimal?: boolean}): Promise<Transpiler> {
    const Module = options?.minimal
      ? await import('../dist/minimal/cpptoc.js')
      : await import('../dist/full/cpptoc.js');
    const instance = new Module.Transpiler();
    return new Transpiler(instance);
  }

  transpile(code: string, options?: TranspileOptions): TranspileResult {
    if (this.disposed) throw new Error('Transpiler disposed');
    // Call WASM transpile, handle errors
  }

  dispose() {
    this.instance.delete();
    this.disposed = true;
  }
}
```

**Verification:**
- [ ] embind compiles without errors
- [ ] TypeScript API imports WASM successfully
- [ ] Transpile call works end-to-end
- [ ] Error handling works across boundary
- [ ] Memory cleanup works (no leaks)

**Files created:**
- `wasm/bindings/minimal.cpp`
- `wasm/bindings/full.cpp`
- `wasm/glue/src/index.ts`
- `wasm/glue/src/transpiler.ts`
- `wasm/glue/src/types.ts`
- `wasm/glue/src/errors.ts`
- `wasm/glue/src/utils.ts`
- `wasm/glue/package.json`
- `wasm/glue/tsconfig.json`

---

### Phase 3: NPM Package

**Tasks:**
1. Create package.json with dual exports (minimal/full)
2. Configure bundler (Rollup/Vite) for WASM
3. Build TypeScript → JS
4. Bundle WASM files with JS
5. Generate .d.ts type declarations
6. Write package README
7. Test local install (`npm link`)
8. Publish to NPM (@hupyy/cpptoc-wasm)

**package.json structure:**
```json
{
  "name": "@hupyy/cpptoc-wasm",
  "version": "1.22.0",
  "type": "module",
  "exports": {
    "./minimal": {
      "types": "./dist/minimal/index.d.ts",
      "import": "./dist/minimal/index.js"
    },
    "./full": {
      "types": "./dist/full/index.d.ts",
      "import": "./dist/full/index.js"
    }
  },
  "files": ["dist/", "README.md", "LICENSE"],
  "scripts": {
    "build": "tsc && rollup -c",
    "test": "vitest"
  },
  "devDependencies": {
    "typescript": "^5.3.0",
    "rollup": "^4.0.0",
    "@rollup/plugin-typescript": "^11.0.0",
    "vitest": "^1.0.0"
  }
}
```

**Verification:**
- [ ] Package builds successfully
- [ ] Both minimal and full exports work
- [ ] TypeScript types are correct
- [ ] `npm pack` produces valid tarball
- [ ] Local install works
- [ ] Imports work in test project

**Files created:**
- `wasm/glue/package.json` (complete)
- `wasm/glue/rollup.config.js`
- `wasm/glue/README.md`

---

### Phase 4: Cloudflare Worker

**Tasks:**
1. Create Worker directory structure
2. Implement Worker entry point (`index.ts`)
3. Configure wrangler.toml
4. Implement request/response handling
5. Add error responses
6. Configure WASM binding
7. Test locally with Wrangler
8. Measure size and cold start time
9. Deploy to Cloudflare

**Worker implementation:**
```typescript
// wasm/cloudflare-worker/src/index.ts
import { Transpiler } from '@hupyy/cpptoc-wasm/minimal';

export default {
  async fetch(request: Request): Promise<Response> {
    if (request.method !== 'POST') {
      return new Response('Method not allowed', { status: 405 });
    }

    try {
      const { code, options } = await request.json();
      const transpiler = await Transpiler.create({ minimal: true });
      const result = transpiler.transpile(code, options);
      transpiler.dispose();

      return new Response(JSON.stringify(result), {
        headers: { 'Content-Type': 'application/json' }
      });
    } catch (error) {
      return new Response(JSON.stringify({ error: error.message }), {
        status: 500,
        headers: { 'Content-Type': 'application/json' }
      });
    }
  }
};
```

**wrangler.toml:**
```toml
name = "cpptoc-transpiler"
main = "src/index.ts"
compatibility_date = "2024-01-01"

[build]
command = "npm run build"

[[rules]]
type = "CompiledWasm"
globs = ["**/*.wasm"]
```

**Verification:**
- [ ] Worker builds successfully
- [ ] Local testing with `wrangler dev` works
- [ ] WASM size fits Cloudflare limits
- [ ] Cold start time acceptable (< 200ms)
- [ ] Transpile request/response works
- [ ] Error handling works

**Files created:**
- `wasm/cloudflare-worker/src/index.ts`
- `wasm/cloudflare-worker/wrangler.toml`
- `wasm/cloudflare-worker/package.json`
- `wasm/cloudflare-worker/tsconfig.json`

---

### Phase 5: Website Integration

**Tasks:**
1. Create Astro playground component
2. Integrate code editor (Monaco or CodeMirror)
3. Implement WASM loading in component
4. Create output display
5. Add example selector
6. Implement sharing/permalink
7. Add inline transpiler for docs
8. Test in actual website

**Playground component:**
```astro
---
// website/src/components/Transpiler/TranspilerPlayground.astro
const base = import.meta.env.BASE_URL;
---

<div class="transpiler-playground">
  <div class="editor-panel">
    <div id="cpp-editor"></div>
  </div>
  <div class="output-panel">
    <div id="c-output"></div>
    <div id="acsl-output"></div>
  </div>
</div>

<script>
  import { Transpiler } from '@hupyy/cpptoc-wasm/full';
  import * as monaco from 'monaco-editor';

  // Initialize Monaco editor
  // Initialize Transpiler
  // Handle transpile on change
</script>
```

**Verification:**
- [ ] Playground renders correctly
- [ ] Code editor works (syntax highlighting, autocomplete)
- [ ] Transpile button triggers WASM transpiler
- [ ] Output displays correctly
- [ ] ACSL annotations shown
- [ ] Examples load correctly
- [ ] Sharing/permalink works

**Files created:**
- `website/src/components/Transpiler/TranspilerPlayground.astro`
- `website/src/components/Transpiler/CodeEditor.tsx`
- `website/src/components/Transpiler/OutputDisplay.tsx`
- `website/src/components/Transpiler/useTranspiler.ts`
- `website/src/components/Examples/InlineTranspiler.astro`

---

### Phase 6: Testing & CI

**Tasks:**
1. Create unit tests for TypeScript API
2. Create integration tests for transpilation
3. Create bundle size regression tests
4. Create E2E tests for playground (Playwright)
5. Create E2E tests for Worker
6. Configure GitHub Actions workflow
7. Add size checks to CI
8. Add automated NPM publishing
9. Add Cloudflare deployment to CI

**Test structure:**
```typescript
// wasm/tests/unit/api.test.ts
import { describe, it, expect } from 'vitest';
import { Transpiler } from '@hupyy/cpptoc-wasm/minimal';

describe('Transpiler API', () => {
  it('should create transpiler instance', async () => {
    const transpiler = await Transpiler.create({ minimal: true });
    expect(transpiler).toBeDefined();
    transpiler.dispose();
  });

  it('should transpile simple code', async () => {
    const transpiler = await Transpiler.create({ minimal: true });
    const result = transpiler.transpile('int main() { return 0; }');
    expect(result.c).toContain('int main');
    expect(result.errors).toHaveLength(0);
    transpiler.dispose();
  });
});
```

**GitHub Actions workflow:**
```yaml
# .github/workflows/wasm-build.yml
name: Build WASM

on: [push, pull_request]

jobs:
  build:
    runs-on: ubuntu-latest
    container:
      image: emscripten/emsdk:latest
    steps:
      - uses: actions/checkout@v3
      - name: Build minimal
        run: cd wasm && ./scripts/build-minimal.sh
      - name: Build full
        run: cd wasm && ./scripts/build-full.sh
      - name: Check sizes
        run: cd wasm && ./scripts/size-check.sh
      - name: Run tests
        run: cd wasm && npm test
      - name: Publish to NPM
        if: startsWith(github.ref, 'refs/tags/')
        run: npm publish
        env:
          NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}
```

**Verification:**
- [ ] All unit tests pass
- [ ] All integration tests pass
- [ ] E2E tests pass
- [ ] Size checks pass (minimal < 2MB compressed)
- [ ] CI workflow runs successfully
- [ ] Automated publishing works

**Files created:**
- `wasm/tests/unit/api.test.ts`
- `wasm/tests/unit/bindings.test.ts`
- `wasm/tests/unit/errors.test.ts`
- `wasm/tests/integration/transpile.test.ts`
- `wasm/tests/integration/acsl.test.ts`
- `wasm/tests/integration/size.test.ts`
- `wasm/tests/e2e/playground.spec.ts`
- `wasm/tests/e2e/worker.spec.ts`
- `.github/workflows/wasm-build.yml`

---

### Phase 7: Documentation & Polish

**Tasks:**
1. Write main README
2. Write API reference
3. Write Cloudflare deployment guide
4. Write website integration guide
5. Write build from source guide
6. Create example gallery
7. Write troubleshooting guide
8. Add code comments
9. Final size optimization pass
10. Performance benchmarking

**Documentation structure:**

```markdown
# wasm/docs/README.md

# WebAssembly Transpiler Library

## Quick Start

### NPM Install
\`\`\`bash
npm install @hupyy/cpptoc-wasm
\`\`\`

### Minimal Build (Cloudflare)
\`\`\`typescript
import { Transpiler } from '@hupyy/cpptoc-wasm/minimal';

const transpiler = await Transpiler.create({ minimal: true });
const result = transpiler.transpile('int main() { return 0; }');
console.log(result.c);
transpiler.dispose();
\`\`\`

### Full Build (Website)
\`\`\`typescript
import { Transpiler } from '@hupyy/cpptoc-wasm/full';

const transpiler = await Transpiler.create();
const result = transpiler.transpile(cppCode, {
  acsl: {
    statements: true,
    typeInvariants: true,
    axiomatics: true,
    ghostCode: true,
    behaviors: true
  }
});
console.log(result.c);
console.log(result.acsl);
transpiler.dispose();
\`\`\`

## Guides
- [API Reference](API.md)
- [Cloudflare Workers](CLOUDFLARE.md)
- [Website Integration](WEBSITE.md)
- [Building from Source](BUILDING.md)
- [Examples](EXAMPLES.md)
```

**Verification:**
- [ ] All documentation complete
- [ ] Code examples work
- [ ] Screenshots included where helpful
- [ ] Troubleshooting covers common issues
- [ ] Performance benchmarks documented

**Files created:**
- `wasm/README.md`
- `wasm/docs/README.md`
- `wasm/docs/API.md`
- `wasm/docs/CLOUDFLARE.md`
- `wasm/docs/WEBSITE.md`
- `wasm/docs/BUILDING.md`
- `wasm/docs/EXAMPLES.md`
- `wasm/docs/TROUBLESHOOTING.md`

---

## Overall Success Criteria

**Build System:**
- [ ] Both minimal and full builds compile successfully
- [ ] Minimal build < 2MB compressed (Cloudflare compatible)
- [ ] Full build includes all Phase 1-5 ACSL annotators
- [ ] WASM files are valid and loadable

**API:**
- [ ] TypeScript API works for both minimal and full
- [ ] embind bindings expose all necessary functions
- [ ] Error handling works across WASM boundary
- [ ] Memory management (dispose) works without leaks

**NPM Package:**
- [ ] Package published to NPM as @hupyy/cpptoc-wasm
- [ ] Both minimal and full exports work
- [ ] TypeScript types are accurate
- [ ] Package is importable in Node.js and browsers

**Cloudflare Worker:**
- [ ] Worker deploys successfully
- [ ] Transpile API endpoint works
- [ ] Cold start < 200ms
- [ ] Error responses are proper JSON

**Website Integration:**
- [ ] Playground component works in Astro website
- [ ] Code editor has syntax highlighting
- [ ] Transpilation is instant (< 100ms for small code)
- [ ] ACSL output displayed correctly
- [ ] Examples work

**Testing:**
- [ ] All unit tests pass (API, bindings, errors)
- [ ] All integration tests pass (transpilation, ACSL, size)
- [ ] All E2E tests pass (playground, worker)
- [ ] Size regression tests prevent bloat

**CI/CD:**
- [ ] GitHub Actions workflow runs on push
- [ ] Automated size checks pass
- [ ] Automated NPM publishing works
- [ ] Cloudflare deployment automated

**Documentation:**
- [ ] README is comprehensive
- [ ] API reference is complete
- [ ] Deployment guides work end-to-end
- [ ] Examples are tested and work
- [ ] Troubleshooting covers common issues

## Output Specification

**Primary deliverable:** `wasm/` directory with complete implementation

**Summary file:** `.prompts/034-wasm-library-implement/SUMMARY.md`

**SUMMARY.md structure:**
```markdown
# WebAssembly Library Implementation Summary

**Dual-build WASM library complete: minimal (X.XMB) for Cloudflare + full (X.XMB) for website with TypeScript API**

## Version
v1.22.0

## Files Created
• wasm/CMakeLists.txt - Dual build configuration
• wasm/bindings/*.cpp - embind definitions
• wasm/glue/src/*.ts - TypeScript API
• wasm/cloudflare-worker/ - Worker deployment
• website/src/components/Transpiler/ - Playground components
• 50+ additional files (tests, docs, scripts)

## Key Achievements
• Minimal build: X.XMB compressed (Cloudflare compatible: yes/no)
• Full build: X.XMB compressed (all ACSL phases included)
• TypeScript API with complete type definitions
• Playground integration in Astro website
• CI/CD pipeline with automated publishing
• Comprehensive documentation

## Decisions Made
• embind chosen over manual ccall (better TypeScript support)
• Monaco editor for playground (better mobile than CodeMirror)
• Rollup for bundling (smaller output than Webpack)
• [Other significant decisions]

## Issues Encountered
• [Any challenges and how they were resolved]

## Performance
• Minimal WASM load time: Xms
• Full WASM load time: Xms
• Transpile time (100 LOC): Xms
• Cloudflare cold start: Xms

## Next Steps
• Monitor bundle sizes in CI
• Gather user feedback on API
• Consider lazy-loading ACSL phases
• Performance optimization opportunities
```

## Notes

- Use parallel subtasks for independent phases (e.g., Worker + Website in parallel)
- Track progress with TodoWrite tool
- Commit after each phase completion
- Test thoroughly before proceeding to next phase
- Document any deviations from plan
- Update plan if significant changes needed

## Execution Strategy

Given the large scope (7 phases), recommend:
1. Execute phases sequentially with verification after each
2. Allow for iteration if issues discovered
3. Create checkpoints after Phases 2, 4, and 6
4. User approval before final deployment (Phase 7)

OR:

Execute all phases autonomously following the plan, with final summary reporting all results.

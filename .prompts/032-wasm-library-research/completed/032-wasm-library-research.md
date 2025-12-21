# Research: WebAssembly Library Compilation for C++ to C Transpiler

## Objective

Research and document the optimal approach for compiling the hupyy-cpp-to-c transpiler to WebAssembly, enabling browser-based usage with two deployment targets:

1. **Cloudflare Workers** - Optimized, minimal build (~2MB target)
2. **Project Website** - Full-featured build with all ACSL Phase 1-5 annotations

This research will inform architecture decisions, build configuration, JavaScript/TypeScript API design, and deployment strategies.

## Context

**Project State:**
- Phases 1-5 complete (v1.22.0): Statement Annotations, Type Invariants, Axiomatic Definitions, Ghost Code, Function Behaviors
- Technology stack: C++17, Clang/LLVM 15+, CMake build system
- Existing website: Astro-based (@.prompts/022-transpiler-website-research/transpiler-website-research.md)
- Target use cases: Interactive playground, documentation examples, NPM package, standalone web tool

**Requirements:**
- **Dual builds**: Minimal (Cloudflare) + Full (website)
- **TypeScript support**: First-class TS types and developer experience
- **Bundle optimization**: Research Cloudflare Workers limits (10MB script size, 1MB after compression)
- **Compatibility**: Check current website stack for constraints (@website/package.json, @website/astro.config.mjs)

## Research Requirements

### 1. Emscripten Toolchain Analysis

**Investigate:**
- Latest stable Emscripten version (3.1.50+)
- Build flags for optimal WASM output
  - `-O3` vs `-Oz` for size optimization
  - `--closure 1` for JS minification
  - `-s MODULARIZE=1` for ES6 module export
  - `-s EXPORT_ES6=1` for modern bundlers
  - `-s ALLOW_MEMORY_GROWTH=1` for dynamic allocation
  - `-s NO_FILESYSTEM=1` if filesystem not needed
  - `-s WASM_ASYNC_COMPILATION=1` for streaming compilation
- Clang/LLVM WASM backend compatibility
  - Can we compile Clang LibTooling to WASM?
  - LLVM libraries required (libclangAST, libclangBasic, etc.)
  - Size impact of Clang dependencies

**Output:**
```xml
<emscripten_analysis>
  <recommended_version></recommended_version>
  <build_flags>
    <flag name="" description="" size_impact=""></flag>
  </build_flags>
  <clang_compatibility>
    <feasible>yes/no</feasible>
    <caveats></caveats>
    <size_estimate></size_estimate>
  </clang_compatibility>
</emscripten_analysis>
```

### 2. Bundle Size Optimization

**Analyze:**
- Core transpiler size (without ACSL annotators)
- Each ACSL annotator size (Phase 1-5)
- Clang/LLVM dependency footprint
- Compression ratios (gzip, brotli)
- Cloudflare Workers limits:
  - 10MB uncompressed script size limit
  - 1MB compressed script size limit (with gzip compression)
  - 3MB compressed with Brotli compression
  - Startup CPU time limits

**Strategy Research:**
- **Code splitting**: Can ACSL annotators be lazy-loaded?
- **Tree shaking**: Which Clang libraries can be excluded?
- **Dead code elimination**: Linker optimizations
- **Module bundling**: Separate WASM modules vs single bundle
- **Dynamic linking**: Feasibility in WASM context

**Cloudflare Compatibility Investigation:**
- Test with sample WASM build (create minimal "hello world" Emscripten build)
- Measure compressed size vs Worker limits
- Research Cloudflare's WASM support (Workers Runtime API)
- Check for known issues with large WASM modules

**Output:**
```xml
<size_analysis>
  <core_transpiler>
    <uncompressed></uncompressed>
    <gzip></gzip>
    <brotli></brotli>
  </core_transpiler>
  <acsl_annotators>
    <phase1_statements size_kb=""></phase1_statements>
    <phase2_type_invariants size_kb=""></phase2_type_invariants>
    <phase3_axiomatics size_kb=""></phase3_axiomatics>
    <phase4_ghost_code size_kb=""></phase4_ghost_code>
    <phase5_behaviors size_kb=""></phase5_behaviors>
  </acsl_annotators>
  <cloudflare_feasibility>
    <minimal_build>
      <fits_limits>yes/no</fits_limits>
      <size_estimate></size_estimate>
    </minimal_build>
    <full_build>
      <fits_limits>yes/no</fits_limits>
      <size_estimate></size_estimate>
      <fallback_strategy></fallback_strategy>
    </full_build>
  </cloudflare_feasibility>
</size_analysis>
```

### 3. JavaScript/TypeScript API Design

**Research:**
- Emscripten's `embind` for C++ ↔ JS bindings
- Alternative: Manual Emscripten `ccall`/`cwrap` API
- TypeScript declaration generation
  - Automatic from `embind` definitions?
  - Manual `.d.ts` authoring?

**API Design Considerations:**
```typescript
// Example ideal API
import { transpile, TranspileOptions } from 'cpptoc-wasm';

const result = await transpile(cppCode, {
  acsl: {
    statements: true,
    typeInvariants: true,
    axiomatics: true,
    ghostCode: false,
    behaviors: true
  },
  target: 'c11',
  optimize: true
});

// result: { c: string, acsl: string, errors: Error[], warnings: Warning[] }
```

**Requirements:**
- Synchronous vs asynchronous API (WASM instantiation is async)
- Error handling and reporting
- Progress callbacks for large files
- Module initialization patterns
- Memory management (create/destroy instances)

**Output:**
```xml
<api_design>
  <binding_strategy>embind|manual</binding_strategy>
  <typescript_generation>automatic|manual</typescript_generation>
  <api_pattern>
    <initialization></initialization>
    <transpile_call></transpile_call>
    <error_handling></error_handling>
    <memory_management></memory_management>
  </api_pattern>
</api_design>
```

### 4. Build System Integration

**CMake + Emscripten Integration:**
- `emcmake cmake` workflow
- CMake toolchain file for Emscripten
- Handling LLVM/Clang dependencies in Emscripten build
- Separate build targets: `wasm-minimal`, `wasm-full`

**Example CMakeLists.txt modifications needed:**
```cmake
if(EMSCRIPTEN)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fexceptions")
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -s MODULARIZE=1 -s EXPORT_ES6=1")

  # Minimal build (core only)
  add_executable(cpptoc-wasm-minimal ...)
  target_link_libraries(cpptoc-wasm-minimal PRIVATE cpptoc_core)

  # Full build (all ACSL)
  add_executable(cpptoc-wasm-full ...)
  target_link_libraries(cpptoc-wasm-full PRIVATE cpptoc_core acsl_all)
endif()
```

**Output:**
```xml
<build_integration>
  <cmake_changes>
    <required_modifications></required_modifications>
    <emscripten_toolchain></emscripten_toolchain>
  </cmake_changes>
  <build_targets>
    <minimal description=""></minimal>
    <full description=""></full>
  </build_targets>
</build_integration>
```

### 5. Website Compatibility Check

**Check existing website:**
- Read @website/package.json - Identify bundler (Vite, Webpack, etc.)
- Read @website/astro.config.mjs - Check Astro configuration
- Identify compatibility constraints:
  - ESM vs CommonJS
  - Browser targets (ES2020+?)
  - Build tool limitations

**WASM Loading Patterns for Astro:**
- Static import vs dynamic import
- Streaming compilation support
- Service worker caching strategies
- Lazy loading for playground component

**Output:**
```xml
<website_compatibility>
  <bundler></bundler>
  <module_format>esm|cjs|both</module_format>
  <browser_targets></browser_targets>
  <loading_strategy>
    <recommended></recommended>
    <fallback></fallback>
  </loading_strategy>
</website_compatibility>
```

### 6. NPM Package Structure

**Research:**
- Package layout for dual builds (minimal + full)
- Entry points configuration in package.json
- Bundler-friendly structure
- TypeScript types distribution

**Example structure:**
```
cpptoc-wasm/
├── dist/
│   ├── minimal/
│   │   ├── cpptoc.js
│   │   ├── cpptoc.wasm
│   │   └── cpptoc.d.ts
│   ├── full/
│   │   ├── cpptoc.js
│   │   ├── cpptoc.wasm
│   │   └── cpptoc.d.ts
│   └── index.d.ts
├── package.json
├── README.md
└── LICENSE
```

**package.json exports:**
```json
{
  "name": "@hupyy/cpptoc-wasm",
  "exports": {
    "./minimal": {
      "types": "./dist/minimal/cpptoc.d.ts",
      "import": "./dist/minimal/cpptoc.js"
    },
    "./full": {
      "types": "./dist/full/cpptoc.d.ts",
      "import": "./dist/full/cpptoc.js"
    }
  }
}
```

**Output:**
```xml
<npm_package>
  <structure></structure>
  <entry_points></entry_points>
  <type_definitions></type_definitions>
</npm_package>
```

### 7. Deployment & Hosting Strategy

**Cloudflare Workers Deployment:**
- Wrangler configuration
- WASM module bindings
- Environment variables for feature flags
- Cold start performance

**Website CDN Deployment:**
- Static file hosting (WASM + JS)
- Cache headers for WASM files
- Streaming compilation setup
- Fallback strategies

**Output:**
```xml
<deployment>
  <cloudflare_workers>
    <wrangler_config></wrangler_config>
    <bindings></bindings>
    <limitations></limitations>
  </cloudflare_workers>
  <website_cdn>
    <hosting_strategy></hosting_strategy>
    <caching></caching>
  </website_cdn>
</deployment>
```

## Research Sources

**Official Documentation:**
- Emscripten: https://emscripten.org/docs/
- Cloudflare Workers: https://developers.cloudflare.com/workers/
- WebAssembly: https://webassembly.org/
- Clang LibTooling: https://clang.llvm.org/docs/LibTooling.html

**Examples & Case Studies:**
- Search for "Clang WASM" examples
- Research existing C++ → WASM transpilers
- Cloudflare Workers WASM examples
- Large WASM projects (e.g., ffmpeg.wasm, sql.js)

**Size Benchmarks:**
- Research typical LLVM/Clang WASM sizes
- Compression ratio expectations
- Comparable WASM projects

## Output Specification

**File:** `.prompts/032-wasm-library-research/wasm-library-research.md`

**Structure:**
```xml
<research_output>
  <confidence>0-100%</confidence>

  <!-- All sections from Research Requirements above -->
  <emscripten_analysis>...</emscripten_analysis>
  <size_analysis>...</size_analysis>
  <api_design>...</api_design>
  <build_integration>...</build_integration>
  <website_compatibility>...</website_compatibility>
  <npm_package>...</npm_package>
  <deployment>...</deployment>

  <recommendations>
    <minimal_build>
      <approach></approach>
      <estimated_size></estimated_size>
      <cloudflare_feasible>yes/no</cloudflare_feasible>
    </minimal_build>
    <full_build>
      <approach></approach>
      <estimated_size></estimated_size>
      <deployment_strategy></deployment_strategy>
    </full_build>
  </recommendations>

  <dependencies>
    <tools>
      <tool name="" version=""></tool>
    </tools>
    <prerequisites></prerequisites>
  </dependencies>

  <open_questions>
    <question priority="high|medium|low"></question>
  </open_questions>

  <assumptions>
    <assumption basis="documented|inferred|assumed"></assumption>
  </assumptions>

  <next_steps>
    <step>Create detailed build plan</step>
    <step>Prototype minimal WASM build</step>
    <step>Measure actual sizes</step>
  </next_steps>
</research_output>
```

**Also create:** `.prompts/032-wasm-library-research/SUMMARY.md`

**SUMMARY.md structure:**
```markdown
# WebAssembly Library Research Summary

**[One substantive sentence describing the key finding]**

## Version
v1 (initial research)

## Key Findings
• [Most important discovery about feasibility]
• [Critical size/performance finding]
• [Cloudflare compatibility determination]
• [TypeScript/API approach recommendation]

## Decisions Needed
• [Any architectural decisions requiring user input]
• [Build strategy choices]

## Blockers
• [External dependencies or unknowns]
• [Technical limitations discovered]

## Next Step
Create wasm-library-plan.md with build configuration and implementation roadmap
```

## Verification Checklist

Before completing, verify:

- [ ] Emscripten version and build flags researched with official docs
- [ ] Cloudflare Workers limits verified from official documentation
- [ ] Size estimates based on comparable projects or calculations
- [ ] Website compatibility checked against actual @website/ files
- [ ] All XML sections populated with substantive findings
- [ ] Confidence level assigned with justification
- [ ] Sources consulted listed with URLs
- [ ] Critical claims verified (Cloudflare limits, Emscripten features)

## Quality Assurance

**Before submission:**

1. **Distinguish verified vs inferred:**
   - Verified: From official docs, measured benchmarks
   - Inferred: Logical conclusions from verified facts
   - Assumed: Best guesses requiring validation

2. **Size estimates:**
   - Provide ranges, not single numbers
   - Show calculation basis
   - Note compression assumptions

3. **Recommendations:**
   - Present pros/cons for each approach
   - Clear rationale for preferred option
   - Acknowledge trade-offs

## Success Criteria

Research is complete when:
- Cloudflare feasibility definitively determined (yes/no with evidence)
- Size estimates for both builds provided (with ranges)
- Build approach recommended (with alternatives documented)
- TypeScript API pattern chosen (embind vs manual)
- All open questions documented for planning phase
- SUMMARY.md provides actionable next step

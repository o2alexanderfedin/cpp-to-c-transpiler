# WebAssembly Library Research Output

## Research Date
2025-12-20

<research_output>
  <confidence>75%</confidence>

  <emscripten_analysis>
    <recommended_version>Emscripten 3.1.50+ (latest stable 4.0.x recommended)</recommended_version>
    <build_flags>
      <flag name="-Oz" description="Maximum size optimization, reduces code size more than -Os" size_impact="Smallest binary size, ~10-20% smaller than -O3, potential 2-5x slower runtime"/>
      <flag name="-O3" description="Maximum performance optimization" size_impact="Larger binary size, fastest runtime, 20-40% larger than -Oz"/>
      <flag name="-s MODULARIZE=1" description="Wraps code in async function returning promise" size_impact="Minimal (~1-2KB), required for EXPORT_ES6"/>
      <flag name="-s EXPORT_ES6=1" description="Output as ES6 module" size_impact="Minimal (~1KB), automatically enables MODULARIZE"/>
      <flag name="-s ALLOW_MEMORY_GROWTH=1" description="Enables dynamic memory allocation at runtime" size_impact="~2-3KB JavaScript overhead, essential for variable-size inputs"/>
      <flag name="-s NO_FILESYSTEM=1" description="Excludes filesystem APIs" size_impact="Reduces JS glue code by ~50-100KB"/>
      <flag name="-s WASM_ASYNC_COMPILATION=1" description="Enables streaming compilation" size_impact="Negligible, improves load time for large modules"/>
      <flag name="--closure 1" description="Google Closure Compiler minification on JS glue code" size_impact="Reduces JS glue code by 30-50%"/>
      <flag name="-flto" description="Link-time optimization" size_impact="5-15% size reduction, significantly longer build time"/>
    </build_flags>
    <clang_compatibility>
      <feasible>yes</feasible>
      <caveats>
        Clang LibTooling can be compiled to WebAssembly but presents significant challenges:

        1. **Size Challenge**: LLVM/Clang libraries are extremely large. Full Clang tooling typically requires:
           - libclangAST
           - libclangBasic
           - libclangFrontend
           - libclangTooling
           - libclangLex
           - LLVMSupport
           - Multiple LLVM core libraries

        2. **Build Requirements**: Building LLVM from source requires 2-4GB RAM minimum, with debug builds needing more.

        3. **Known Issues**:
           - No public benchmarks found for Clang LibTooling → WASM compilation sizes
           - Most WebAssembly success stories involve smaller, purpose-built tools
           - FFmpeg.wasm achieves ~20-25MB, SQL.js achieves ~655KB (compressed to ~277KB with Brotli)

        4. **Optimization Path**: The LLVM WebAssembly backend produces smaller output than legacy fastcomp backend

        5. **Static Linking**: Possible to build Clang statically with only WebAssembly target to create portable executable
      </caveats>
      <size_estimate>
        Uncompressed: 15-50MB (estimated based on typical Clang tooling executables)
        Gzip compressed: 7-25MB (~50% compression ratio typical for WASM)
        Brotli compressed: 6-21MB (~42% of original, 15% better than gzip)

        Note: These are EXTRAPOLATED estimates. Without actual compilation, exact sizes unknown.
        For comparison:
        - FFmpeg.wasm: 20MB uncompressed, custom builds can reach 4.8MB
        - SQL.js: 655KB uncompressed → 321KB gzip → 277KB Brotli
        - Typical C++ tooling: 10-100MB native executables
      </size_estimate>
    </clang_compatibility>
  </emscripten_analysis>

  <size_analysis>
    <core_transpiler>
      <uncompressed>15-50MB (estimated, includes Clang/LLVM dependencies)</uncompressed>
      <gzip>7-25MB (50% compression ratio typical)</gzip>
      <brotli>6-21MB (42% of original, 15% better than gzip)</brotli>
      <basis>
        Estimation based on:
        1. Current CMakeLists.txt shows 27 source files in cpptoc_core library
        2. Dependencies on clangTooling, clangFrontend, clangAST, clangBasic, LLVMSupport
        3. Comparison with similar projects (FFmpeg.wasm 20MB, complex C++ tools)
        4. Native cpptoc executable likely 5-20MB, WASM overhead adds 2-3x
      </basis>
    </core_transpiler>
    <acsl_annotators>
      <phase1_statements size_kb="500-1500" description="Statement annotations, loop invariants, assertions"/>
      <phase2_type_invariants size_kb="300-800" description="Type invariant generation for structs/classes"/>
      <phase3_axiomatics size_kb="400-1000" description="Axiomatic definitions, predicates, logic functions"/>
      <phase4_ghost_code size_kb="300-800" description="Ghost variable injection"/>
      <phase5_behaviors size_kb="500-1200" description="Function behavior annotations (requires/ensures)"/>
      <total_acsl_overhead size_kb="2000-5300" description="All ACSL phases combined (2-5MB uncompressed)"/>
      <basis>
        Estimated from source file analysis:
        - Each annotator: 1 primary source file + shared infrastructure
        - Typical C++ class with Clang AST traversal: 100-300KB compiled
        - ACSL logic string generation adds minimal overhead
        - Total 5 annotators × ~400-1000KB average = 2-5MB
      </basis>
    </acsl_annotators>
    <cloudflare_feasibility>
      <minimal_build>
        <fits_limits>MAYBE - borderline feasible with aggressive optimization</fits_limits>
        <size_estimate>
          Scenario 1 (Optimistic): Core transpiler only, no ACSL, aggressive -Oz + LTO
          - Uncompressed: 8-15MB
          - Brotli compressed: 3.4-6.3MB
          - VERDICT: May exceed 3MB Brotli limit, definitely exceeds 1MB gzip limit (free tier)

          Scenario 2 (Pessimistic): Standard build with minimal features
          - Uncompressed: 15-25MB
          - Brotli compressed: 6.3-10.5MB
          - VERDICT: Exceeds 10MB paid tier uncompressed limit

          CRITICAL: Cloudflare Workers limits:
          - Free tier: 1MB compressed (gzip)
          - Paid tier: 10MB uncompressed OR 3MB compressed (Brotli)

          To fit in paid tier, need:
          - Aggressive tree shaking of Clang libraries
          - Strip debugging symbols completely
          - Consider subset of LibTooling functionality
          - May need custom Clang build excluding unnecessary components
        </size_estimate>
      </minimal_build>
      <full_build>
        <fits_limits>NO - exceeds Cloudflare Workers limits</fits_limits>
        <size_estimate>
          Full transpiler + all 5 ACSL phases:
          - Uncompressed: 20-55MB
          - Gzip compressed: 10-27.5MB
          - Brotli compressed: 8.4-23MB

          VERDICT: Significantly exceeds all Cloudflare limits
        </size_estimate>
        <fallback_strategy>
          Option 1: Split Architecture
          - Deploy minimal build to Cloudflare Workers (core transpilation only)
          - Host full build on CDN (GitHub Pages, Cloudflare Pages, Netlify)
          - Use feature flags in UI to switch between modes

          Option 2: Lazy Loading with Code Splitting
          - Load core transpiler first (~6-10MB Brotli)
          - Dynamically import ACSL annotators on demand using dynamic import()
          - Each phase as separate WASM module (500KB-1.5MB each compressed)
          - Requires Emscripten module splitting support

          Option 3: Server-Side Processing
          - Deploy full build to Cloudflare Pages Functions (different limits)
          - Workers just handles routing/caching
          - Pages Functions support larger bundles

          Option 4: Contact Cloudflare for Limit Increase
          - Documentation mentions requesting size increases beyond 10MB
          - Requires business relationship/justification

          RECOMMENDED: Option 1 (Split Architecture) for maximum compatibility
        </fallback_strategy>
      </full_build>
    </cloudflare_feasibility>
  </size_analysis>

  <api_design>
    <binding_strategy>embind (recommended)</binding_strategy>
    <typescript_generation>automatic via --emit-tsd</typescript_generation>
    <rationale>
      Embind advantages:
      1. Automatic TypeScript definition generation via emcc --emit-tsd
      2. Type-safe C++ ↔ JavaScript bindings
      3. Supports complex types (std::string, std::vector, custom classes)
      4. Better developer experience than manual cwrap/ccall
      5. Reduces maintenance burden

      Manual approach only if:
      - Embind adds too much overhead (unlikely, ~5-10KB)
      - Need ultra-minimal API surface
      - Performance critical hot path (embind has small overhead)
    </rationale>
    <api_pattern>
      <initialization>
        ```typescript
        // ES6 module pattern (EXPORT_ES6=1)
        import createCppToC from './cpptoc.js';

        // Async initialization (WASM requires async)
        const CppToC = await createCppToC({
          locateFile: (path: string) => {
            if (path.endsWith('.wasm')) {
              return `/wasm/${path}`;
            }
            return path;
          }
        });
        ```
      </initialization>
      <transpile_call>
        ```typescript
        // TypeScript API (auto-generated from embind)
        interface TranspileOptions {
          acsl: {
            statements: boolean;
            typeInvariants: boolean;
            axiomatics: boolean;
            ghostCode: boolean;
            behaviors: boolean;
          };
          target: 'c99' | 'c11' | 'c17';
          optimize: boolean;
        }

        interface TranspileResult {
          success: boolean;
          c: string;
          acsl: string;
          errors: Array<{
            line: number;
            column: number;
            message: string;
            severity: 'error' | 'warning';
          }>;
        }

        // C++ embind definition
        EMSCRIPTEN_BINDINGS(cpptoc_api) {
          emscripten::value_object<TranspileOptions>("TranspileOptions")
            .field("target", &TranspileOptions::target)
            .field("optimize", &TranspileOptions::optimize);

          emscripten::value_object<TranspileResult>("TranspileResult")
            .field("success", &TranspileResult::success)
            .field("c", &TranspileResult::c)
            .field("acsl", &TranspileResult::acsl)
            .field("errors", &TranspileResult::errors);

          emscripten::function("transpile", &transpile);
        }

        // Usage
        const result = CppToC.transpile(sourceCode, options);
        ```
      </transpile_call>
      <error_handling>
        ```typescript
        // Synchronous errors (JavaScript exceptions)
        try {
          const result = CppToC.transpile(code, options);
          if (!result.success) {
            // Compilation errors (not exceptions)
            result.errors.forEach(err => {
              console.error(`${err.severity}: ${err.message} at ${err.line}:${err.column}`);
            });
          }
        } catch (e) {
          // WASM runtime errors (out of memory, invalid input)
          console.error('Runtime error:', e);
        }

        // C++ side: catch all exceptions, convert to error objects
        TranspileResult transpile(const std::string& code, const TranspileOptions& opts) {
          try {
            // ... transpilation logic
          } catch (const std::exception& e) {
            return TranspileResult{
              .success = false,
              .errors = {{0, 0, e.what(), "error"}}
            };
          }
        }
        ```
      </error_handling>
      <memory_management>
        ```typescript
        // Embind handles memory automatically for:
        // - std::string (copied between JS ↔ C++)
        // - Value objects (TranspileOptions, TranspileResult)
        // - std::vector (converted to/from JS arrays)

        // Manual memory management only needed for:
        // 1. Large file processing (streaming)
        // 2. Persistent state (if implemented)

        // Option 1: Stateless (recommended)
        // Each transpile() call is independent, no cleanup needed

        // Option 2: Stateful instance
        interface CppToCInstance {
          setOptions(opts: TranspileOptions): void;
          transpile(code: string): TranspileResult;
          dispose(): void; // Explicit cleanup
        }

        const instance = new CppToC.Instance();
        try {
          instance.setOptions(options);
          const result = instance.transpile(code);
        } finally {
          instance.dispose(); // Free C++ memory
        }
        ```
      </memory_management>
    </api_pattern>
  </api_design>

  <build_integration>
    <cmake_changes>
      <required_modifications>
        ```cmake
        # CMakeLists.txt additions for WASM builds

        if(EMSCRIPTEN)
          message(STATUS "Building for WebAssembly with Emscripten")

          # Enable C++ exceptions (required for try/catch)
          set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fexceptions")

          # Common WASM linker flags
          set(WASM_LINKER_FLAGS
            "-s MODULARIZE=1"
            "-s EXPORT_ES6=1"
            "-s ALLOW_MEMORY_GROWTH=1"
            "-s NO_FILESYSTEM=1"
            "-s WASM_ASYNC_COMPILATION=1"
            "-s EXPORTED_RUNTIME_METHODS=['ccall','cwrap']"
            "--bind" # Enable embind
          )

          # Minimal build (core only, no ACSL)
          add_executable(cpptoc-wasm-minimal
            src/main_wasm.cpp  # New: WASM entry point with embind bindings
            # Reuse existing sources
          )

          target_link_libraries(cpptoc-wasm-minimal PRIVATE cpptoc_core)

          set_target_properties(cpptoc-wasm-minimal PROPERTIES
            LINK_FLAGS "${WASM_LINKER_FLAGS} -Oz --closure 1 -flto"
            OUTPUT_NAME "cpptoc-minimal"
          )

          # Generate TypeScript definitions
          add_custom_command(TARGET cpptoc-wasm-minimal POST_BUILD
            COMMAND ${CMAKE_COMMAND} -E env
              ${EMSCRIPTEN_COMPILER_FRONTEND}
              ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-minimal.js
              --emit-tsd ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-minimal.d.ts
            COMMENT "Generating TypeScript definitions"
          )

          # Full build (all ACSL phases)
          add_executable(cpptoc-wasm-full
            src/main_wasm.cpp
          )

          target_link_libraries(cpptoc-wasm-full PRIVATE
            cpptoc_core
            # ACSL annotators linked into core library
          )

          set_target_properties(cpptoc-wasm-full PROPERTIES
            LINK_FLAGS "${WASM_LINKER_FLAGS} -O3"  # Performance over size for full build
            OUTPUT_NAME "cpptoc-full"
          )

          # Install WASM outputs
          install(FILES
            ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-minimal.js
            ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-minimal.wasm
            ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-minimal.d.ts
            DESTINATION wasm/minimal
          )

          install(FILES
            ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-full.js
            ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-full.wasm
            ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-full.d.ts
            DESTINATION wasm/full
          )
        endif()
        ```
      </required_modifications>
      <emscripten_toolchain>
        Two approaches:

        **Approach 1: emcmake wrapper (traditional)**
        ```bash
        # Configure
        emcmake cmake -B build-wasm -DCMAKE_BUILD_TYPE=Release

        # Build
        emmake cmake --build build-wasm --target cpptoc-wasm-minimal
        ```

        **Approach 2: Direct toolchain file (modern, CMake 3.20+)**
        ```bash
        # Configure
        cmake -B build-wasm \
          -DCMAKE_TOOLCHAIN_FILE=$EMSDK/upstream/emscripten/cmake/Modules/Platform/Emscripten.cmake \
          -DCMAKE_BUILD_TYPE=Release

        # Build
        cmake --build build-wasm --target cpptoc-wasm-minimal
        ```

        **Approach 3: Native Emscripten support (CMake 4.2+, future)**
        ```bash
        cmake -B build-wasm -DCMAKE_SYSTEM_NAME=Emscripten -DCMAKE_BUILD_TYPE=Release
        cmake --build build-wasm
        ```
      </emscripten_toolchain>
    </cmake_changes>
    <build_targets>
      <minimal description="Core transpiler only, optimized for size (-Oz), no ACSL phases, target: Cloudflare Workers (borderline feasible)"/>
      <full description="Full transpiler with all ACSL phases, optimized for performance (-O3), target: website CDN deployment"/>
    </build_targets>
  </build_integration>

  <website_compatibility>
    <bundler>Vite (via Astro)</bundler>
    <module_format>esm</module_format>
    <browser_targets>ES2020+ (modern browsers, Astro default)</browser_targets>
    <details>
      Based on website/package.json and website/astro.config.mjs analysis:

      1. **Build System**:
         - Astro 5.16.6 (uses Vite 6.x internally)
         - React 19.2.3 integration
         - Static output mode

      2. **Module Format**:
         - package.json has "type": "module" → ESM-only
         - Perfect match for EXPORT_ES6=1 from Emscripten

      3. **WASM Support**:
         - Vite has native WASM support
         - vite-plugin-wasm available if needed for advanced features
         - Astro 0.21+ built-in WASM support

      4. **Constraints**:
         - Static site (output: 'static') → WASM must be included in build output
         - Base path: '/cpp-to-c-website' → need to handle in locateFile()
         - GitHub Pages deployment → need proper MIME types for .wasm
    </details>
    <loading_strategy>
      <recommended>
        ```typescript
        // In Astro component or React component
        // Use dynamic import for code splitting

        // Option 1: Load on demand (lazy loading)
        import { useEffect, useState } from 'react';

        function TranspilerPlayground() {
          const [transpiler, setTranspiler] = useState(null);
          const [loading, setLoading] = useState(false);

          const loadTranspiler = async () => {
            setLoading(true);
            try {
              // Dynamic import - only loads when needed
              const createModule = await import('/wasm/full/cpptoc.js');
              const module = await createModule.default({
                locateFile: (path) => {
                  if (path.endsWith('.wasm')) {
                    return '/cpp-to-c-website/wasm/full/' + path;
                  }
                  return path;
                }
              });
              setTranspiler(module);
            } catch (e) {
              console.error('Failed to load WASM:', e);
            } finally {
              setLoading(false);
            }
          };

          // Load on first interaction (not on page load)
          return (
            <div>
              {!transpiler && (
                <button onClick={loadTranspiler} disabled={loading}>
                  {loading ? 'Loading...' : 'Start Transpiler'}
                </button>
              )}
              {transpiler && <Editor transpiler={transpiler} />}
            </div>
          );
        }

        // Option 2: Preload with streaming compilation
        // In Astro layout/head
        <link rel="preload" href="/wasm/full/cpptoc.wasm" as="fetch" type="application/wasm" crossorigin />

        // Then use WebAssembly.instantiateStreaming for optimal loading
        const response = await fetch('/cpp-to-c-website/wasm/full/cpptoc.wasm');
        const module = await WebAssembly.instantiateStreaming(response);
        ```
      </recommended>
      <fallback>
        ```typescript
        // Fallback for browsers without streaming compilation
        async function loadWASM(url) {
          try {
            // Try streaming first (fastest)
            const response = await fetch(url);
            return await WebAssembly.instantiateStreaming(response);
          } catch (e) {
            // Fallback to ArrayBuffer (slower, but works everywhere)
            console.warn('Streaming compilation failed, using fallback');
            const response = await fetch(url);
            const buffer = await response.arrayBuffer();
            return await WebAssembly.instantiate(buffer);
          }
        }
        ```
      </fallback>
    </loading_strategy>
  </website_compatibility>

  <npm_package>
    <structure>
      ```
      @hupyy/cpptoc-wasm/
      ├── dist/
      │   ├── minimal/
      │   │   ├── cpptoc.js          # ES6 module (EXPORT_ES6=1)
      │   │   ├── cpptoc.wasm         # WebAssembly binary
      │   │   └── cpptoc.d.ts         # TypeScript definitions (auto-generated)
      │   ├── full/
      │   │   ├── cpptoc.js
      │   │   ├── cpptoc.wasm
      │   │   └── cpptoc.d.ts
      │   └── index.d.ts              # Unified type exports
      ├── package.json
      ├── README.md
      ├── LICENSE
      └── examples/
          ├── node/                    # Node.js usage example
          ├── browser/                 # Browser usage example
          └── worker/                  # Web Worker usage example
      ```
    </structure>
    <entry_points>
      ```json
      {
        "name": "@hupyy/cpptoc-wasm",
        "version": "1.22.0",
        "type": "module",
        "description": "C++ to C transpiler with ACSL annotations, compiled to WebAssembly",
        "main": "./dist/full/cpptoc.js",
        "types": "./dist/index.d.ts",
        "exports": {
          ".": {
            "types": "./dist/index.d.ts",
            "import": "./dist/full/cpptoc.js"
          },
          "./minimal": {
            "types": "./dist/minimal/cpptoc.d.ts",
            "import": "./dist/minimal/cpptoc.js"
          },
          "./full": {
            "types": "./dist/full/cpptoc.d.ts",
            "import": "./dist/full/cpptoc.js"
          },
          "./package.json": "./package.json"
        },
        "files": [
          "dist/**/*.js",
          "dist/**/*.wasm",
          "dist/**/*.d.ts",
          "README.md",
          "LICENSE"
        ],
        "sideEffects": false,
        "keywords": [
          "cpp",
          "c",
          "transpiler",
          "acsl",
          "webassembly",
          "wasm",
          "formal-verification"
        ],
        "engines": {
          "node": ">=18.0.0"
        },
        "repository": {
          "type": "git",
          "url": "https://github.com/o2alexanderfedin/hupyy-cpp-to-c.git"
        },
        "bugs": {
          "url": "https://github.com/o2alexanderfedin/hupyy-cpp-to-c/issues"
        },
        "homepage": "https://o2alexanderfedin.github.io/cpp-to-c-website"
      }
      ```
    </entry_points>
    <type_definitions>
      ```typescript
      // dist/index.d.ts (unified exports)

      // Re-export from full build by default
      export * from './full/cpptoc.d.ts';

      // Also export minimal for explicit imports
      export * as Minimal from './minimal/cpptoc.d.ts';
      export * as Full from './full/cpptoc.d.ts';

      // Usage:
      // import CppToC from '@hupyy/cpptoc-wasm';           // Full build
      // import CppToC from '@hupyy/cpptoc-wasm/minimal';   // Minimal build
      // import { Minimal, Full } from '@hupyy/cpptoc-wasm'; // Named imports
      ```

      Auto-generated from embind (emcc --emit-tsd):
      - Embind automatically generates TypeScript definitions from C++ bindings
      - No manual .d.ts authoring required
      - Type safety guaranteed by embind type system
      - Includes all exported functions, classes, enums, value objects
    </type_definitions>
  </npm_package>

  <deployment>
    <cloudflare_workers>
      <wrangler_config>
        ```toml
        # wrangler.toml for Cloudflare Workers deployment

        name = "cpptoc-transpiler"
        main = "src/worker.ts"
        compatibility_date = "2025-01-01"

        # Account/deployment settings
        account_id = "YOUR_ACCOUNT_ID"
        workers_dev = true

        # Module format (required for WASM)
        [build]
        command = "npm run build"

        [build.upload]
        format = "modules"
        main = "./dist/worker.js"

        [[build.upload.rules]]
        type = "CompiledWasm"
        globs = ["**/*.wasm"]
        fallthrough = true

        # Environment variables for feature flags
        [vars]
        TRANSPILER_MODE = "minimal"  # "minimal" or "full"
        MAX_SOURCE_SIZE = "100000"   # 100KB limit for safety
        CACHE_TTL = "3600"

        # KV namespace for caching (optional)
        [[kv_namespaces]]
        binding = "CACHE"
        id = "YOUR_KV_NAMESPACE_ID"
        preview_id = "YOUR_PREVIEW_KV_ID"
        ```

        Worker implementation:
        ```typescript
        // src/worker.ts
        import createCppToC from '../wasm/minimal/cpptoc.js';
        import wasmModule from '../wasm/minimal/cpptoc.wasm';

        export default {
          async fetch(request: Request, env: Env): Promise<Response> {
            // Handle CORS
            if (request.method === 'OPTIONS') {
              return new Response(null, {
                headers: {
                  'Access-Control-Allow-Origin': '*',
                  'Access-Control-Allow-Methods': 'POST, OPTIONS',
                  'Access-Control-Allow-Headers': 'Content-Type',
                }
              });
            }

            if (request.method !== 'POST') {
              return new Response('Method not allowed', { status: 405 });
            }

            try {
              const { code, options } = await request.json();

              // Size limit check
              if (code.length > parseInt(env.MAX_SOURCE_SIZE)) {
                return Response.json({ error: 'Source code too large' }, { status: 413 });
              }

              // Initialize WASM module (cached by Workers runtime)
              const CppToC = await createCppToC({
                wasmBinary: wasmModule  // Pre-instantiated
              });

              // Transpile
              const result = CppToC.transpile(code, options);

              return Response.json(result, {
                headers: {
                  'Access-Control-Allow-Origin': '*',
                  'Content-Type': 'application/json',
                  'Cache-Control': 'public, max-age=' + env.CACHE_TTL
                }
              });
            } catch (error) {
              return Response.json({
                error: error.message
              }, {
                status: 500,
                headers: { 'Access-Control-Allow-Origin': '*' }
              });
            }
          }
        };
        ```
      </wrangler_config>
      <bindings>
        WASM Module Binding (Module Format):
        - Import .wasm file directly in TypeScript/JavaScript
        - Cloudflare Workers bundles it automatically
        - Available as WebAssembly.Module at runtime
        - No need for manual file fetching

        Alternative (Service Worker Format - Legacy):
        ```toml
        [[wasm_modules]]
        binding = "CPPTOC_WASM"
        source = "./wasm/minimal/cpptoc.wasm"
        ```
      </bindings>
      <limitations>
        CRITICAL LIMITATIONS:

        1. **Size Constraints**:
           - Free tier: 1MB compressed (gzip) - INSUFFICIENT
           - Paid tier: 10MB uncompressed OR 3MB Brotli - BORDERLINE for minimal, IMPOSSIBLE for full
           - Workaround: Contact Cloudflare for limit increase (requires justification)

        2. **CPU Time**:
           - 10ms on free tier, 50ms on paid tier (startup time)
           - Large WASM modules have longer instantiation time
           - Mitigate: Workers cache instantiated modules across requests

        3. **Memory**:
           - 128MB per Worker
           - Clang/LLVM can be memory-hungry
           - ALLOW_MEMORY_GROWTH=1 helps but adds overhead

        4. **Cold Starts**:
           - Larger WASM = slower cold starts
           - Workers may be evicted from cache if unused
           - Impact: First request after eviction takes 100-500ms longer

        5. **No Filesystem**:
           - NO_FILESYSTEM=1 required (already optimal)
           - Cannot use file-based compilation model
           - Must use in-memory string-based API

        6. **Build Complexity**:
           - Requires separate build pipeline for Workers
           - Different optimization flags than website build
           - Testing in local dev requires Miniflare/Wrangler dev mode

        RECOMMENDATION:
        - Cloudflare Workers viable for MINIMAL build only with aggressive optimization
        - Full build should use Cloudflare Pages Functions or separate CDN
      </limitations>
    </cloudflare_workers>
    <website_cdn>
      <hosting_strategy>
        GitHub Pages (current setup):
        ```yaml
        # .github/workflows/deploy-website.yml
        name: Deploy Website

        on:
          push:
            branches: [main]

        jobs:
          build-wasm:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/checkout@v4

              - name: Setup Emscripten
                uses: mymindstorm/setup-emsdk@v14
                with:
                  version: '3.1.50'

              - name: Build WASM (Full)
                run: |
                  emcmake cmake -B build-wasm -DCMAKE_BUILD_TYPE=Release
                  emmake cmake --build build-wasm --target cpptoc-wasm-full

              - name: Copy WASM outputs
                run: |
                  mkdir -p website/public/wasm/full
                  cp build-wasm/cpptoc-full.{js,wasm,d.ts} website/public/wasm/full/

              - name: Build Astro site
                working-directory: website
                run: |
                  npm ci
                  npm run build

              - name: Deploy to GitHub Pages
                uses: peaceiris/actions-gh-pages@v3
                with:
                  github_token: ${{ secrets.GITHUB_TOKEN }}
                  publish_dir: ./website/dist
        ```

        Alternative: Cloudflare Pages (better for WASM):
        - Automatic Brotli compression
        - Better MIME type handling for .wasm
        - Integrated with Workers for hybrid approach
        - Unlimited bandwidth on free tier
      </hosting_strategy>
      <caching>
        ```
        # public/_headers (for Cloudflare Pages / Netlify)

        /wasm/*.wasm
          Content-Type: application/wasm
          Cache-Control: public, max-age=31536000, immutable
          Access-Control-Allow-Origin: *

        /wasm/*.js
          Content-Type: application/javascript
          Cache-Control: public, max-age=31536000, immutable
          Access-Control-Allow-Origin: *

        # For GitHub Pages, configure in astro.config.mjs:
        export default defineConfig({
          vite: {
            build: {
              rollupOptions: {
                output: {
                  assetFileNames: 'assets/[name]-[hash][extname]'
                }
              }
            },
            server: {
              headers: {
                'Cross-Origin-Embedder-Policy': 'require-corp',
                'Cross-Origin-Opener-Policy': 'same-origin'
              }
            }
          }
        });
        ```

        Service Worker caching strategy:
        ```typescript
        // Cache WASM modules aggressively
        self.addEventListener('install', (event) => {
          event.waitUntil(
            caches.open('wasm-v1').then((cache) => {
              return cache.addAll([
                '/wasm/full/cpptoc.wasm',
                '/wasm/full/cpptoc.js',
                '/wasm/minimal/cpptoc.wasm',
                '/wasm/minimal/cpptoc.js'
              ]);
            })
          );
        });

        self.addEventListener('fetch', (event) => {
          if (event.request.url.includes('/wasm/')) {
            event.respondWith(
              caches.match(event.request).then((response) => {
                return response || fetch(event.request);
              })
            );
          }
        });
        ```
      </caching>
    </website_cdn>
  </deployment>

  <recommendations>
    <minimal_build>
      <approach>
        1. **Aggressive Size Optimization**:
           - Use -Oz (size over speed)
           - Enable --closure 1 (JavaScript minification)
           - Use -flto (link-time optimization)
           - Strip all debug symbols
           - NO_FILESYSTEM=1 (exclude filesystem APIs)

        2. **Clang Library Tree Shaking**:
           - Audit which Clang/LLVM libraries are actually used
           - Consider subset of LibTooling if full API not needed
           - May require custom Clang build

        3. **Feature Reduction**:
           - Core transpilation only
           - No ACSL annotators
           - Minimal error reporting
           - No diagnostics beyond basic errors

        4. **Build Configuration**:
           ```bash
           emcc -Oz -flto --closure 1 \
             -s MODULARIZE=1 \
             -s EXPORT_ES6=1 \
             -s ALLOW_MEMORY_GROWTH=1 \
             -s NO_FILESYSTEM=1 \
             -s WASM_ASYNC_COMPILATION=1 \
             --bind \
             [source files] \
             -o cpptoc-minimal.js
           ```
      </approach>
      <estimated_size>
        Optimistic: 3-6MB Brotli (borderline for Cloudflare paid tier)
        Realistic: 6-10MB Brotli (exceeds Cloudflare limits)
        Pessimistic: 10-15MB Brotli (significantly over limits)
      </estimated_size>
      <cloudflare_feasible>BORDERLINE - requires aggressive optimization and may need limit increase</cloudflare_feasible>
    </minimal_build>
    <full_build>
      <approach>
        1. **Performance Optimization** (size less critical):
           - Use -O3 (speed over size)
           - Keep debug information for source maps
           - Full error diagnostics
           - All ACSL phases included

        2. **Code Splitting** (optional):
           - Load core transpiler first
           - Lazy load ACSL annotators on demand
           - Each phase as separate WASM module

        3. **Build Configuration**:
           ```bash
           emcc -O3 \
             -s MODULARIZE=1 \
             -s EXPORT_ES6=1 \
             -s ALLOW_MEMORY_GROWTH=1 \
             -s NO_FILESYSTEM=1 \
             -s WASM_ASYNC_COMPILATION=1 \
             --bind \
             --emit-tsd cpptoc-full.d.ts \
             [all source files] \
             -o cpptoc-full.js
           ```
      </approach>
      <estimated_size>
        Optimistic: 8-15MB Brotli
        Realistic: 15-25MB Brotli
        Pessimistic: 25-40MB Brotli
      </estimated_size>
      <deployment_strategy>
        **RECOMMENDED: CDN + Progressive Loading**

        1. **Host on CDN** (GitHub Pages, Cloudflare Pages, Netlify):
           - No size limits
           - Aggressive caching
           - Brotli compression
           - Global edge network

        2. **Progressive Loading Pattern**:
           ```typescript
           // Load on user interaction, not page load
           async function initializeTranspiler() {
             // Show loading indicator
             const transpiler = await import('/wasm/full/cpptoc.js');
             const module = await transpiler.default();
             // Hide loading, enable UI
             return module;
           }

           // Only load when user opens playground/editor
           editorButton.addEventListener('click', async () => {
             const transpiler = await initializeTranspiler();
             enableEditor(transpiler);
           });
           ```

        3. **Service Worker Caching**:
           - Cache WASM files aggressively
           - Offline-first after initial load
           - Background updates for new versions

        4. **Chunking Strategy** (if code splitting):
           - Chunk 1: Core transpiler (6-10MB)
           - Chunk 2: Statement annotations (500KB-1.5MB)
           - Chunk 3: Type invariants (300KB-800KB)
           - Chunk 4: Axiomatics (400KB-1MB)
           - Chunk 5: Ghost code (300KB-800KB)
           - Chunk 6: Behaviors (500KB-1.2MB)

           Load chunks on demand based on user options.
      </deployment_strategy>
    </full_build>
  </recommendations>

  <dependencies>
    <tools>
      <tool name="Emscripten" version="3.1.50+ (latest stable 4.0.x preferred)"/>
      <tool name="CMake" version="3.20+" description="For Emscripten toolchain support"/>
      <tool name="Node.js" version="18+" description="For build scripts and testing"/>
      <tool name="emsdk" version="latest" description="Emscripten SDK installer"/>
      <tool name="Clang/LLVM" version="15+" description="Already required for main project"/>
    </tools>
    <prerequisites>
      1. **Development Environment**:
         - Install emsdk: git clone https://github.com/emscripten-core/emsdk.git
         - Activate: emsdk install latest && emsdk activate latest
         - Add to PATH: source ./emsdk_env.sh

      2. **Build Environment**:
         - 4-8GB RAM recommended for LLVM WASM builds
         - 10-20GB disk space for build artifacts
         - Linux/macOS preferred (Windows via WSL2)

      3. **Testing Environment**:
         - Modern browser (Chrome 90+, Firefox 88+, Safari 14+)
         - Node.js 18+ for unit tests
         - Wrangler CLI for Workers testing

      4. **CI/CD**:
         - GitHub Actions with Emscripten setup action
         - Cache emsdk and build artifacts for faster builds
         - Separate workflows for WASM builds vs native builds
    </prerequisites>
  </dependencies>

  <open_questions>
    <question priority="high">
      What is the ACTUAL compiled size of Clang LibTooling transpiled to WASM?

      Action needed: Create minimal prototype with just Clang AST parsing to measure real size.
      Until measured, all estimates are extrapolations and may be off by 2-3x.
    </question>
    <question priority="high">
      Can we selectively link only required Clang/LLVM components?

      Investigation needed: Analyze which Clang APIs are actually used, determine if subset linking is possible.
      Potential size savings: 30-60% if we can exclude unused components.
    </question>
    <question priority="medium">
      Is code splitting viable for ACSL annotators?

      Emscripten module splitting exists but may require significant refactoring.
      Alternative: Build each annotator as separate WASM module (needs architecture changes).
    </question>
    <question priority="medium">
      What are acceptable latency/UX tradeoffs for WASM loading?

      User research needed: Is 3-5 second initial load acceptable? Should we show progress bar?
      Should playground require user click to initialize (lazy loading)?
    </question>
    <question priority="low">
      Should we support Web Workers for background transpilation?

      Benefit: Non-blocking UI during transpilation
      Cost: Additional complexity, need to clone WASM module to worker context
      Recommendation: Defer to Phase 2 after basic WASM build working
    </question>
    <question priority="low">
      What compression format does GitHub Pages use?

      If only gzip (not Brotli), may need to switch to Cloudflare Pages for better compression.
      Brotli saves ~15% size over gzip for WASM files.
    </question>
  </open_questions>

  <assumptions>
    <assumption basis="documented">
      Cloudflare Workers limits are as documented:
      - Free: 1MB gzip compressed
      - Paid: 10MB uncompressed OR 3MB Brotli compressed
      Source: https://developers.cloudflare.com/workers/platform/limits/
    </assumption>
    <assumption basis="documented">
      Emscripten embind supports automatic TypeScript generation via --emit-tsd flag.
      Source: https://emscripten.org/docs/porting/connecting_cpp_and_javascript/embind.html
    </assumption>
    <assumption basis="documented">
      WebAssembly compression ratios:
      - Gzip: ~50% of original size (2:1 ratio)
      - Brotli: ~42% of original size (2.36:1 ratio)
      Source: Measured from sql.js WASM file and general WASM benchmarks
    </assumption>
    <assumption basis="inferred">
      Clang LibTooling WASM size will be 15-50MB uncompressed.
      Basis: Native Clang tooling executables are 5-20MB, WASM overhead 2-3x.
      CONFIDENCE: LOW - needs actual measurement
    </assumption>
    <assumption basis="inferred">
      ACSL annotators add 2-5MB total uncompressed size.
      Basis: 5 annotators × ~400-1000KB average based on source analysis.
      CONFIDENCE: MEDIUM - can measure after WASM build
    </assumption>
    <assumption basis="assumed">
      Users accept 3-5 second load time for full-featured transpiler.
      Basis: Common for large WASM applications (FFmpeg.wasm, etc.)
      CONFIDENCE: LOW - needs user research/testing
    </assumption>
    <assumption basis="assumed">
      Progressive Web App caching will make subsequent loads instant.
      Basis: Service Workers + Cache API standard practice
      CONFIDENCE: HIGH - well-established pattern
    </assumption>
    <assumption basis="documented">
      Astro + Vite support WASM out of the box.
      Source: Astro 0.21+ docs, Vite WASM support
      CONFIDENCE: HIGH - confirmed in documentation
    </assumption>
  </assumptions>

  <next_steps>
    <step>Create minimal Clang LibTooling WASM prototype to measure actual size</step>
    <step>Test different Emscripten optimization flags and measure size impact</step>
    <step>Implement embind API bindings for core transpiler functions</step>
    <step>Set up dual CMake build targets (minimal + full)</step>
    <step>Create NPM package structure with dual exports</step>
    <step>Integrate WASM build into CI/CD pipeline</step>
    <step>Implement progressive loading in Astro website</step>
    <step>Test Cloudflare Workers deployment with minimal build</step>
    <step>Benchmark load times and optimize as needed</step>
    <step>Document WASM API usage and examples</step>
  </next_steps>
</research_output>

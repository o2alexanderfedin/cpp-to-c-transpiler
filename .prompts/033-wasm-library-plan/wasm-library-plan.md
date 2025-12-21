# WebAssembly Library Implementation Plan

## Plan Date
2025-12-20

<plan_output>
  <confidence>85%</confidence>

  <build_system_plan>
    <cmake_structure>
      <file path="CMakeLists.txt" changes="modify">
        Add EMSCRIPTEN detection block at end of file (after existing targets)
        Configure dual WASM build targets with appropriate optimization flags
        Set up embind linkage and TypeScript generation
      </file>
      <file path="src/main_wasm.cpp" changes="new">
        Create new entry point for WASM builds with embind API bindings
        Implement TranspileOptions, TranspileResult structs
        Export transpile() function with embind
        Handle exceptions and convert to error objects
      </file>
      <file path="cmake/EmscriptenToolchain.cmake" changes="new">
        Optional: Custom toolchain file for consistent Emscripten builds
        Define common WASM flags and settings
        Can be omitted if using emcmake wrapper
      </file>
    </cmake_structure>
    <targets>
      <target name="wasm-minimal">
        <sources>
          src/main_wasm.cpp (embind entry point)
          Core transpiler sources (excluding ACSL annotators):
            - CppToCVisitor.cpp
            - CppToCConsumer.cpp
            - CppToCFrontendAction.cpp
            - CodeGenerator.cpp
            - BuildConfiguration.cpp
            - FileOutputManager.cpp
            - IncludeGuardGenerator.cpp
            - DependencyGraphVisualizer.cpp
            - All supporting infrastructure files
        </sources>
        <libraries>
          Clang/LLVM libraries (minimal set):
            - clangTooling
            - clangFrontend
            - clangDriver
            - clangSerialization
            - clangCodeGen
            - clangParse
            - clangSema
            - clangAnalysis
            - clangEdit
            - clangAST
            - clangLex
            - clangBasic
            - LLVMSupport
          Standard library:
            - stdc++
        </libraries>
        <compile_flags>
          -std=c++17
          -fexceptions (required for C++ exception handling)
          -DEMSCRIPTEN (preprocessor define)
          -DWASM_MINIMAL_BUILD (exclude ACSL features)
        </compile_flags>
        <link_flags>
          # Module format
          -s MODULARIZE=1 (wrap in async function)
          -s EXPORT_ES6=1 (ES6 module output)
          -s EXPORT_NAME=createCppToC (custom module name)

          # Memory management
          -s ALLOW_MEMORY_GROWTH=1 (dynamic heap)
          -s INITIAL_MEMORY=33554432 (32MB initial, tunable)
          -s MAXIMUM_MEMORY=268435456 (256MB max, tunable)

          # Size optimization (aggressive)
          -Oz (optimize for size)
          --closure 1 (Google Closure Compiler on JS glue)
          -flto (link-time optimization)
          -s AGGRESSIVE_VARIABLE_ELIMINATION=1

          # Features
          -s NO_FILESYSTEM=1 (exclude filesystem APIs)
          -s NO_EXIT_RUNTIME=1 (keep runtime alive)
          -s WASM_ASYNC_COMPILATION=1 (streaming compilation)
          -s EXPORTED_RUNTIME_METHODS=['UTF8ToString','stringToUTF8']

          # Embind
          --bind (enable embind)
          --emit-tsd cpptoc-minimal.d.ts (TypeScript definitions)

          # Exception handling
          -s EXCEPTION_CATCHING_ALLOWED=['..'] (catch all exceptions)
          -fexceptions

          # Debug info (minimal)
          -s ASSERTIONS=0 (disable runtime assertions for size)
          -s STACK_OVERFLOW_CHECK=0 (disable for size)
        </link_flags>
      </target>
      <target name="wasm-full">
        <sources>
          All sources from wasm-minimal, plus ACSL annotators:
            - ACSLStatementAnnotator.cpp (Phase 1)
            - ACSLTypeInvariantGenerator.cpp (Phase 2)
            - ACSLAxiomaticBuilder.cpp (Phase 3)
            - ACSLGhostCodeInjector.cpp (Phase 4)
            - ACSLBehaviorAnnotator.cpp (Phase 5)
            - ACSLGenerator.cpp
            - ACSLFunctionAnnotator.cpp
            - ACSLClassAnnotator.cpp
            - ACSLLoopAnnotator.cpp
        </sources>
        <libraries>
          Same as wasm-minimal (all ACSL code links against same Clang libraries)
        </libraries>
        <compile_flags>
          -std=c++17
          -fexceptions
          -DEMSCRIPTEN
          (no WASM_MINIMAL_BUILD - include all ACSL features)
        </compile_flags>
        <link_flags>
          # Module format (same as minimal)
          -s MODULARIZE=1
          -s EXPORT_ES6=1
          -s EXPORT_NAME=createCppToC

          # Memory management (larger for ACSL)
          -s ALLOW_MEMORY_GROWTH=1
          -s INITIAL_MEMORY=67108864 (64MB initial)
          -s MAXIMUM_MEMORY=536870912 (512MB max)

          # Performance optimization (not size)
          -O3 (optimize for speed)
          -s AGGRESSIVE_VARIABLE_ELIMINATION=1

          # Features
          -s NO_FILESYSTEM=1
          -s NO_EXIT_RUNTIME=1
          -s WASM_ASYNC_COMPILATION=1
          -s EXPORTED_RUNTIME_METHODS=['UTF8ToString','stringToUTF8']

          # Embind
          --bind
          --emit-tsd cpptoc-full.d.ts

          # Exception handling
          -s EXCEPTION_CATCHING_ALLOWED=['..']
          -fexceptions

          # Debug info (more verbose for development)
          -s ASSERTIONS=1 (enable runtime assertions)
          -s STACK_OVERFLOW_CHECK=1 (enable stack checks)
          -g1 (minimal debug info, line numbers)
        </link_flags>
      </target>
    </targets>
  </build_system_plan>

  <api_implementation_plan>
    <bindings>
      <embind_file path="src/main_wasm.cpp">
        <exports>
          ```cpp
          #include &lt;emscripten/bind.h&gt;
          #include &lt;string&gt;
          #include &lt;vector&gt;

          // Option structures
          struct ACSLOptions {
              bool statements = false;
              bool typeInvariants = false;
              bool axiomatics = false;
              bool ghostCode = false;
              bool behaviors = false;
          };

          struct TranspileOptions {
              ACSLOptions acsl;
              std::string target = "c99"; // c89, c99, c11, c17
              bool optimize = false;
          };

          // Diagnostic/error structures
          struct Diagnostic {
              int line = 0;
              int column = 0;
              std::string message;
              std::string severity; // "error", "warning", "note"
          };

          // Result structure
          struct TranspileResult {
              bool success = false;
              std::string c;
              std::string acsl;
              std::vector&lt;Diagnostic&gt; diagnostics;
          };

          // Main transpile function
          TranspileResult transpile(const std::string&amp; cppCode, const TranspileOptions&amp; options) {
              TranspileResult result;
              try {
                  // Create in-memory virtual file system
                  // Parse C++ code using Clang
                  // Run transpilation visitor
                  // Collect diagnostics
                  // Return result

                  // Implementation calls existing transpiler logic
                  // (requires refactoring main.cpp logic into library function)

              } catch (const std::exception&amp; e) {
                  result.success = false;
                  result.diagnostics.push_back({0, 0, e.what(), "error"});
              }
              return result;
          }

          // Version info
          std::string getVersion() {
              return "1.22.0";
          }

          // Embind bindings
          EMSCRIPTEN_BINDINGS(cpptoc_api) {
              using namespace emscripten;

              value_object&lt;ACSLOptions&gt;("ACSLOptions")
                  .field("statements", &amp;ACSLOptions::statements)
                  .field("typeInvariants", &amp;ACSLOptions::typeInvariants)
                  .field("axiomatics", &amp;ACSLOptions::axiomatics)
                  .field("ghostCode", &amp;ACSLOptions::ghostCode)
                  .field("behaviors", &amp;ACSLOptions::behaviors);

              value_object&lt;TranspileOptions&gt;("TranspileOptions")
                  .field("acsl", &amp;TranspileOptions::acsl)
                  .field("target", &amp;TranspileOptions::target)
                  .field("optimize", &amp;TranspileOptions::optimize);

              value_object&lt;Diagnostic&gt;("Diagnostic")
                  .field("line", &amp;Diagnostic::line)
                  .field("column", &amp;Diagnostic::column)
                  .field("message", &amp;Diagnostic::message)
                  .field("severity", &amp;Diagnostic::severity);

              value_object&lt;TranspileResult&gt;("TranspileResult")
                  .field("success", &amp;TranspileResult::success)
                  .field("c", &amp;TranspileResult::c)
                  .field("acsl", &amp;TranspileResult::acsl)
                  .field("diagnostics", &amp;TranspileResult::diagnostics);

              register_vector&lt;Diagnostic&gt;("DiagnosticVector");

              function("transpile", &amp;transpile);
              function("getVersion", &amp;getVersion);
          }
          ```
        </exports>
        <memory_management>
          Automatic memory management via embind:
          - std::string: Copied between C++ heap and JavaScript strings
          - std::vector: Converted to/from JavaScript arrays automatically
          - value_objects: Copied by value (no manual cleanup needed)

          Manual management only for:
          - Clang AST nodes (managed by Clang's ASTContext)
          - Large intermediate buffers (use RAII/smart pointers)

          No explicit dispose() needed for stateless API.
          Each transpile() call is independent, cleanup automatic.
        </memory_management>
      </embind_file>
    </bindings>
    <typescript_wrapper>
      <files>
        <file path="wasm-glue/src/index.ts" purpose="Main entry point, re-exports from generated .d.ts">
          ```typescript
          // Re-export auto-generated types and functions
          export * from '../dist/minimal/cpptoc';
          export * from '../dist/full/cpptoc';

          // Convenience wrapper (optional)
          import createCppToCMinimal from '../dist/minimal/cpptoc.js';
          import createCppToCFull from '../dist/full/cpptoc.js';

          export { createCppToCMinimal, createCppToCFull };
          ```
        </file>
        <file path="wasm-glue/src/types.ts" purpose="Additional TypeScript utilities and helpers">
          ```typescript
          // Export type guards
          export function isTranspileError(result: TranspileResult): boolean {
              return !result.success || result.diagnostics.some(d => d.severity === 'error');
          }

          // Export default options
          export const DEFAULT_OPTIONS: TranspileOptions = {
              acsl: {
                  statements: true,
                  typeInvariants: true,
                  axiomatics: false,
                  ghostCode: false,
                  behaviors: true
              },
              target: 'c99',
              optimize: false
          };
          ```
        </file>
      </files>
      <initialization_pattern>
        ```typescript
        // Usage example
        import createCppToC from '@hupyy/cpptoc-wasm/full';

        // Async initialization (WASM loading)
        const module = await createCppToC({
            // Optional: custom WASM file location
            locateFile: (path: string) => {
                if (path.endsWith('.wasm')) {
                    return `/wasm/full/${path}`;
                }
                return path;
            },
            // Optional: progress callback for large WASM
            onRuntimeInitialized: () => {
                console.log('WASM runtime ready');
            }
        });

        // Use transpiler
        const result = module.transpile(cppCode, {
            acsl: { statements: true, typeInvariants: true },
            target: 'c99',
            optimize: false
        });

        if (result.success) {
            console.log('C output:', result.c);
            console.log('ACSL output:', result.acsl);
        } else {
            console.error('Errors:', result.diagnostics);
        }
        ```
      </initialization_pattern>
      <error_handling>
        Two-level error handling:

        1. JavaScript exceptions (WASM initialization failures):
           - Network errors (WASM file not found)
           - Invalid WASM binary
           - Out of memory during initialization
           - Catch with try/catch around createCppToC()

        2. Transpilation errors (returned in TranspileResult):
           - C++ syntax errors
           - Unsupported features
           - Clang diagnostics
           - Check result.success and result.diagnostics

        Never throw exceptions from transpile() - all errors in result object.
      </error_handling>
    </typescript_wrapper>
    <build_process>
      1. CMake builds WASM targets → generates .js, .wasm, .d.ts files
      2. Copy generated files to wasm-glue/dist/ directories
      3. TypeScript compiler (tsc) builds wrapper code
      4. Bundle with rollup/esbuild (optional, for NPM package)
      5. Output structure:
         ```
         dist/
         ├── minimal/
         │   ├── cpptoc.js
         │   ├── cpptoc.wasm
         │   └── cpptoc.d.ts (generated by emcc --emit-tsd)
         ├── full/
         │   ├── cpptoc.js
         │   ├── cpptoc.wasm
         │   └── cpptoc.d.ts
         └── index.d.ts (wrapper types)
         ```
    </build_process>
  </api_implementation_plan>

  <npm_package_plan>
    <package_json>
      ```json
      {
        "name": "@hupyy/cpptoc-wasm",
        "version": "1.22.0",
        "description": "C++ to C transpiler with ACSL formal specification annotations, compiled to WebAssembly",
        "type": "module",
        "author": "Alexander Fedin",
        "license": "MIT",
        "repository": {
          "type": "git",
          "url": "https://github.com/o2alexanderfedin/hupyy-cpp-to-c.git"
        },
        "homepage": "https://o2alexanderfedin.github.io/cpp-to-c-website",
        "bugs": {
          "url": "https://github.com/o2alexanderfedin/hupyy-cpp-to-c/issues"
        },
        "keywords": [
          "cpp",
          "c",
          "transpiler",
          "acsl",
          "formal-verification",
          "webassembly",
          "wasm",
          "clang",
          "llvm"
        ],
        "main": "./dist/full/cpptoc.js",
        "types": "./dist/index.d.ts",
        "exports": {
          ".": {
            "types": "./dist/index.d.ts",
            "import": "./dist/full/cpptoc.js",
            "default": "./dist/full/cpptoc.js"
          },
          "./minimal": {
            "types": "./dist/minimal/cpptoc.d.ts",
            "import": "./dist/minimal/cpptoc.js",
            "default": "./dist/minimal/cpptoc.js"
          },
          "./full": {
            "types": "./dist/full/cpptoc.d.ts",
            "import": "./dist/full/cpptoc.js",
            "default": "./dist/full/cpptoc.js"
          },
          "./package.json": "./package.json"
        },
        "files": [
          "dist/**/*.js",
          "dist/**/*.wasm",
          "dist/**/*.d.ts",
          "README.md",
          "LICENSE",
          "CHANGELOG.md"
        ],
        "sideEffects": false,
        "engines": {
          "node": ">=18.0.0"
        },
        "scripts": {
          "build": "npm run build:wasm && npm run build:types",
          "build:wasm": "bash scripts/build-wasm.sh",
          "build:types": "tsc --project tsconfig.build.json",
          "test": "vitest run",
          "test:watch": "vitest watch",
          "test:size": "node scripts/check-size.js",
          "prepublishOnly": "npm run build && npm run test && npm run test:size"
        },
        "devDependencies": {
          "typescript": "^5.7.0",
          "vitest": "^2.1.0",
          "@types/node": "^22.0.0"
        }
      }
      ```
    </package_json>
    <bundled_files>
      <file path="dist/minimal/cpptoc.js" purpose="Emscripten-generated JS glue code for minimal build"/>
      <file path="dist/minimal/cpptoc.wasm" purpose="WebAssembly binary for minimal build (core transpiler only)"/>
      <file path="dist/minimal/cpptoc.d.ts" purpose="TypeScript definitions auto-generated by emcc --emit-tsd"/>
      <file path="dist/full/cpptoc.js" purpose="Emscripten-generated JS glue code for full build"/>
      <file path="dist/full/cpptoc.wasm" purpose="WebAssembly binary for full build (all ACSL phases)"/>
      <file path="dist/full/cpptoc.d.ts" purpose="TypeScript definitions for full build"/>
      <file path="dist/index.d.ts" purpose="Unified TypeScript exports and utilities"/>
      <file path="README.md" purpose="Installation, usage, API documentation"/>
      <file path="LICENSE" purpose="MIT license"/>
      <file path="CHANGELOG.md" purpose="Version history"/>
    </bundled_files>
    <documentation>
      <readme_sections>
        <section>Installation (npm install, CDN usage via unpkg/jsdelivr)</section>
        <section>Quick Start (minimal code example)</section>
        <section>API Reference (TranspileOptions, TranspileResult, functions)</section>
        <section>Usage Examples (Node.js, Browser, React, Vue, Astro)</section>
        <section>Build Variants (minimal vs full, when to use each)</section>
        <section>Browser Compatibility (Chrome 92+, Firefox 90+, Safari 15.2+)</section>
        <section>Performance Considerations (initial load time, caching strategies)</section>
        <section>Troubleshooting (common errors, debugging tips)</section>
        <section>Building from Source (for contributors)</section>
        <section>Contributing (link to main repo guidelines)</section>
        <section>License (MIT)</section>
      </readme_sections>
    </documentation>
  </npm_package_plan>

  <cloudflare_deployment_plan>
    <worker_structure>
      <file path="cloudflare-worker/src/index.ts" purpose="Worker entry point, handles HTTP requests">
        ```typescript
        import createCppToC from '../wasm/minimal/cpptoc.js';
        import wasmModule from '../wasm/minimal/cpptoc.wasm';

        interface Env {
            MAX_SOURCE_SIZE: string;
            CACHE_TTL: string;
            CACHE: KVNamespace; // Optional KV for result caching
        }

        export default {
            async fetch(request: Request, env: Env): Promise&lt;Response&gt; {
                // CORS preflight
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

                    // Size limit
                    if (code.length > parseInt(env.MAX_SOURCE_SIZE || '100000')) {
                        return Response.json({ error: 'Source code too large (max 100KB)' }, { status: 413 });
                    }

                    // Check cache (optional)
                    const cacheKey = `transpile:${hashCode(code)}:${JSON.stringify(options)}`;
                    if (env.CACHE) {
                        const cached = await env.CACHE.get(cacheKey);
                        if (cached) {
                            return new Response(cached, {
                                headers: {
                                    'Content-Type': 'application/json',
                                    'X-Cache': 'HIT',
                                    'Access-Control-Allow-Origin': '*'
                                }
                            });
                        }
                    }

                    // Initialize WASM (cached by Workers runtime across requests)
                    const module = await createCppToC({ wasmBinary: wasmModule });

                    // Transpile
                    const result = module.transpile(code, options);

                    const responseBody = JSON.stringify(result);

                    // Cache result (optional)
                    if (env.CACHE && result.success) {
                        await env.CACHE.put(cacheKey, responseBody, {
                            expirationTtl: parseInt(env.CACHE_TTL || '3600')
                        });
                    }

                    return new Response(responseBody, {
                        headers: {
                            'Content-Type': 'application/json',
                            'Access-Control-Allow-Origin': '*',
                            'Cache-Control': `public, max-age=${env.CACHE_TTL || '3600'}`
                        }
                    });
                } catch (error) {
                    return Response.json({
                        success: false,
                        diagnostics: [{ line: 0, column: 0, message: error.message, severity: 'error' }]
                    }, {
                        status: 500,
                        headers: { 'Access-Control-Allow-Origin': '*' }
                    });
                }
            }
        };

        function hashCode(str: string): string {
            let hash = 0;
            for (let i = 0; i < str.length; i++) {
                hash = ((hash << 5) - hash) + str.charCodeAt(i);
                hash |= 0;
            }
            return hash.toString(36);
        }
        ```
      </file>
      <file path="cloudflare-worker/wrangler.toml" purpose="Cloudflare Workers configuration">
        ```toml
        name = "cpptoc-transpiler"
        main = "src/index.ts"
        compatibility_date = "2025-01-01"

        # Module Workers (required for WASM)
        [build]
        command = "npm run build"

        [build.upload]
        format = "modules"

        [[build.upload.rules]]
        type = "CompiledWasm"
        globs = ["**/*.wasm"]
        fallthrough = true

        # Environment variables
        [vars]
        MAX_SOURCE_SIZE = "100000"  # 100KB
        CACHE_TTL = "3600"          # 1 hour

        # Optional: KV namespace for caching
        [[kv_namespaces]]
        binding = "CACHE"
        id = "" # Fill in after creating KV namespace

        # Development overrides
        [env.dev]
        vars = { MAX_SOURCE_SIZE = "50000", CACHE_TTL = "60" }
        ```
      </file>
      <file path="cloudflare-worker/package.json" purpose="Worker build configuration">
        ```json
        {
          "name": "cpptoc-worker",
          "version": "1.22.0",
          "private": true,
          "type": "module",
          "scripts": {
            "dev": "wrangler dev",
            "deploy": "wrangler deploy",
            "build": "tsc && node scripts/copy-wasm.js"
          },
          "devDependencies": {
            "wrangler": "^3.90.0",
            "typescript": "^5.7.0",
            "@cloudflare/workers-types": "^4.20250114.0"
          }
        }
        ```
      </file>
    </worker_structure>
    <wrangler_config>
      Module Workers format (modern, recommended):
      - Direct import of .wasm files
      - Automatic bundling by Wrangler
      - Type-safe with @cloudflare/workers-types

      WASM binding handled automatically:
      - Import .wasm file as WebAssembly.Module
      - Pass to createCppToC({ wasmBinary })
      - Workers runtime caches instantiated module
    </wrangler_config>
    <request_handling>
      POST /
      Request body: { code: string, options: TranspileOptions }
      Response: TranspileResult (JSON)

      Rate limiting: Use Cloudflare Rate Limiting rules
      Authentication: Optional API key via headers
      Size limits: 100KB source code (configurable)
      Timeout: 50ms CPU time limit (paid tier)
    </request_handling>
    <caching>
      Two-level caching:

      1. Workers KV (optional, for result caching):
         - Key: hash(code + options)
         - Value: TranspileResult JSON
         - TTL: 1 hour (configurable)
         - Reduces redundant transpilation

      2. Cloudflare CDN edge cache:
         - Cache-Control: public, max-age=3600
         - Vary: Accept-Encoding
         - Same code + options = same result (deterministic)

      WASM module caching:
      - Workers runtime caches instantiated WASM
      - Cold starts: ~100-500ms (WASM instantiation)
      - Warm requests: &lt;10ms (cached module)
    </caching>
  </cloudflare_deployment_plan>

  <website_integration_plan>
    <components>
      <component path="website/src/components/Transpiler/TranspilerPlayground.astro" purpose="Main playground page component">
        Server-side rendered shell, loads React playground client-side
      </component>
      <component path="website/src/components/Transpiler/CodeEditor.tsx" purpose="Split-pane code editor with WASM transpiler">
        React component with CodeMirror 6
        Left pane: C++ input
        Right pane: C output (top) + ACSL output (bottom)
        Real-time transpilation on input change (debounced)
      </component>
      <component path="website/src/components/Transpiler/OutputDisplay.tsx" purpose="Transpiled code display with syntax highlighting">
        Syntax-highlighted C and ACSL output
        Copy to clipboard button
        Download as file button
        Error/warning display
      </component>
      <component path="website/src/components/Transpiler/OptionsPanel.tsx" purpose="Transpiler options UI">
        ACSL phase toggles (statements, type invariants, axiomatics, ghost code, behaviors)
        Target C standard selector (c89, c99, c11, c17)
        Optimization toggle
      </component>
      <component path="website/src/components/Transpiler/useTranspiler.ts" purpose="React hook for WASM module lifecycle">
        Handles async WASM loading
        Provides transpile() function
        Loading state management
        Error handling
      </component>
      <component path="website/src/components/Examples/InlineExample.astro" purpose="Inline code example with transpile button">
        Embeddable in documentation pages
        Click to transpile → opens modal with results
        Uses same WASM module as playground
      </component>
    </components>
    <wasm_loading>
      Strategy: Lazy loading on user interaction

      ```typescript
      // useTranspiler.ts
      import { useState, useEffect, useCallback } from 'react';
      import type { TranspileOptions, TranspileResult } from '@hupyy/cpptoc-wasm/full';

      export function useTranspiler() {
          const [module, setModule] = useState(null);
          const [loading, setLoading] = useState(false);
          const [error, setError] = useState(null);

          const loadModule = useCallback(async () => {
              if (module) return; // Already loaded

              setLoading(true);
              setError(null);

              try {
                  // Dynamic import - only loads when called
                  const createCppToC = (await import('/wasm/full/cpptoc.js')).default;

                  const wasmModule = await createCppToC({
                      locateFile: (path) => {
                          if (path.endsWith('.wasm')) {
                              return '/cpp-to-c-website/wasm/full/' + path;
                          }
                          return path;
                      },
                      onRuntimeInitialized: () => {
                          console.log('WASM runtime initialized');
                      }
                  });

                  setModule(wasmModule);
              } catch (e) {
                  setError(e.message);
                  console.error('Failed to load WASM:', e);
              } finally {
                  setLoading(false);
              }
          }, [module]);

          const transpile = useCallback((code: string, options: TranspileOptions): TranspileResult | null => {
              if (!module) {
                  console.warn('WASM module not loaded');
                  return null;
              }
              return module.transpile(code, options);
          }, [module]);

          return { transpile, loadModule, loading, error, ready: !!module };
      }
      ```

      Preloading (optional, for faster first use):
      ```astro
      ---
      // In playground page head
      ---
      &lt;link rel="preload" href="/wasm/full/cpptoc.wasm" as="fetch" type="application/wasm" crossorigin /&gt;
      ```
    </wasm_loading>
    <editor_integration>
      CodeMirror 6 (modern, React-friendly):

      ```typescript
      import { EditorView, basicSetup } from 'codemirror';
      import { cpp } from '@codemirror/lang-cpp';
      import { oneDark } from '@codemirror/theme-one-dark';

      function CodeEditor({ value, onChange, readOnly = false }) {
          const editorRef = useRef(null);

          useEffect(() => {
              const view = new EditorView({
                  doc: value,
                  extensions: [
                      basicSetup,
                      cpp(),
                      oneDark,
                      EditorView.updateListener.of((update) => {
                          if (update.docChanged && onChange) {
                              onChange(update.state.doc.toString());
                          }
                      }),
                      EditorView.editable.of(!readOnly)
                  ],
                  parent: editorRef.current
              });

              return () => view.destroy();
          }, []);

          return &lt;div ref={editorRef} /&gt;;
      }
      ```

      Alternative: Monaco Editor (VS Code-like, heavier):
      - Richer features (IntelliSense, minimap)
      - Larger bundle size (~2MB vs ~200KB for CodeMirror)
      - Recommendation: Start with CodeMirror, evaluate Monaco if needed
    </editor_integration>
    <documentation_examples>
      Inline transpilation in docs:

      ```astro
      ---
      // In documentation MDX file
      import InlineExample from '@components/Examples/InlineExample.astro';
      ---

      ## Example: Class with Invariants

      &lt;InlineExample code={`
      class Counter {
          int value;
          // Invariant: value is always non-negative
      public:
          void increment() { value++; }
          int getValue() const { return value; }
      };
      `} acsl={{ typeInvariants: true }} /&gt;

      Click "Transpile" to see the generated C code with ACSL annotations.
      ```

      Example gallery with predefined snippets:
      - Basic class → C struct
      - Virtual functions → function pointers
      - Templates → specialized implementations
      - Exceptions → setjmp/longjmp
      - RAII → explicit cleanup
      - Each with transpile button + result display
    </documentation_examples>
  </website_integration_plan>

  <testing_plan>
    <test_framework>Vitest (fast, Vite-native, ESM-first)</test_framework>
    <test_categories>
      <category name="Unit Tests" coverage="API bindings, TypeScript wrappers, embind correctness">
        Files:
        - tests/unit/api.test.ts (transpile function, options, results)
        - tests/unit/types.test.ts (TypeScript type checking)
        - tests/unit/errors.test.ts (error handling, diagnostics)

        Approach:
        - Load WASM module once in beforeAll()
        - Test various input/output combinations
        - Verify result structure matches types
        - Test error conditions (invalid C++, unsupported features)
        - Mock WASM module for isolated wrapper tests
      </category>
      <category name="Integration Tests" coverage="End-to-end transpilation, ACSL generation, multi-phase workflows">
        Files:
        - tests/integration/transpile.test.ts (basic transpilation)
        - tests/integration/acsl-phase1.test.ts (statement annotations)
        - tests/integration/acsl-phase2.test.ts (type invariants)
        - tests/integration/acsl-phase3.test.ts (axiomatics)
        - tests/integration/acsl-phase4.test.ts (ghost code)
        - tests/integration/acsl-phase5.test.ts (behaviors)
        - tests/integration/size.test.ts (bundle size verification)

        Approach:
        - Real WASM module (no mocks)
        - Test complete transpilation workflows
        - Verify C output compiles (optional: invoke C compiler)
        - Check ACSL annotation correctness
        - Size regression tests (fail if WASM exceeds thresholds)
      </category>
      <category name="E2E Tests" coverage="Browser automation, website playground, Cloudflare Worker deployment">
        Files:
        - tests/e2e/playground.spec.ts (Playwright test for website)
        - tests/e2e/worker.spec.ts (Miniflare test for Cloudflare Worker)

        Approach:
        - Playwright for browser automation
        - Test playground UI interaction
        - Verify WASM loads and transpiles in browser
        - Test Worker API with Miniflare (local Cloudflare Workers simulator)
        - Cross-browser testing (Chrome, Firefox, Safari)
      </category>
      <category name="Performance Tests" coverage="Load time, transpilation speed, memory usage">
        Files:
        - tests/perf/load-time.test.ts
        - tests/perf/transpile-speed.test.ts
        - tests/perf/memory-usage.test.ts

        Metrics:
        - WASM instantiation time (&lt;2s target)
        - Transpilation throughput (lines/second)
        - Memory growth over repeated transpilations
        - Benchmark against native executable (acceptable: 2-5x slower)
      </category>
    </test_categories>
    <ci_integration>
      GitHub Actions workflow:

      ```yaml
      name: WASM Build and Test

      on: [push, pull_request]

      jobs:
        build-and-test:
          runs-on: ubuntu-latest
          steps:
            - uses: actions/checkout@v4

            - name: Setup Emscripten
              uses: mymindstorm/setup-emsdk@v14
              with:
                version: '3.1.50'

            - name: Setup Node.js
              uses: actions/setup-node@v4
              with:
                node-version: '18'
                cache: 'npm'

            - name: Build WASM (Minimal)
              run: |
                emcmake cmake -B build-wasm-minimal -DCMAKE_BUILD_TYPE=Release
                emmake cmake --build build-wasm-minimal --target cpptoc-wasm-minimal

            - name: Build WASM (Full)
              run: |
                emcmake cmake -B build-wasm-full -DCMAKE_BUILD_TYPE=Release
                emmake cmake --build build-wasm-full --target cpptoc-wasm-full

            - name: Check sizes
              run: |
                ls -lh build-wasm-minimal/cpptoc-minimal.wasm
                ls -lh build-wasm-full/cpptoc-full.wasm
                gzip -c build-wasm-minimal/cpptoc-minimal.wasm | wc -c
                brotli -c build-wasm-full/cpptoc-full.wasm | wc -c

            - name: Install NPM dependencies
              run: npm ci

            - name: Run unit tests
              run: npm run test:unit

            - name: Run integration tests
              run: npm run test:integration

            - name: Size regression check
              run: npm run test:size

            - name: Upload artifacts
              uses: actions/upload-artifact@v4
              with:
                name: wasm-builds
                path: |
                  build-wasm-minimal/cpptoc-minimal.*
                  build-wasm-full/cpptoc-full.*
      ```
    </ci_integration>
  </testing_plan>

  <documentation_plan>
    <structure>
      <doc path="README.md" audience="NPM package users, quick start">
        Sections: Installation, Quick Start, API Reference, Examples, Browser Compatibility, Troubleshooting
      </doc>
      <doc path="docs/INSTALLATION.md" audience="Developers integrating WASM library">
        NPM installation, CDN usage (unpkg, jsdelivr), manual download, version pinning
      </doc>
      <doc path="docs/API.md" audience="TypeScript/JavaScript developers">
        Complete API reference with TypeScript signatures
        Generated from --emit-tsd output
        Examples for each function/interface
      </doc>
      <doc path="docs/EXAMPLES.md" audience="Integration developers">
        Node.js usage, Browser usage, React integration, Vue integration, Astro integration
        Web Worker usage, Service Worker caching
      </doc>
      <doc path="docs/CLOUDFLARE.md" audience="Cloudflare Workers developers">
        Worker deployment guide, wrangler.toml configuration, size optimization tips
        KV caching setup, rate limiting, authentication
      </doc>
      <doc path="docs/WEBSITE.md" audience="Website contributors">
        Astro integration guide, component architecture, WASM loading strategy
        CodeMirror setup, progressive loading implementation
      </doc>
      <doc path="docs/BUILDING.md" audience="Contributors building from source">
        Prerequisites (Emscripten, CMake, Node.js), build instructions
        CMake options, troubleshooting build errors, cross-compilation tips
      </doc>
      <doc path="docs/TROUBLESHOOTING.md" audience="All users encountering issues">
        Common errors (WASM load failures, CORS issues, memory errors)
        Debugging techniques, browser console diagnostics
        Size optimization strategies, performance tuning
      </doc>
      <doc path="CHANGELOG.md" audience="All users tracking versions">
        Version history, breaking changes, migration guides
        Format: Keep a Changelog (keepachangelog.com)
      </doc>
    </structure>
    <examples>
      <example scenario="Basic Node.js transpilation">
        ```javascript
        import createCppToC from '@hupyy/cpptoc-wasm/full';

        const module = await createCppToC();
        const result = module.transpile('class Foo { int x; };', {
            acsl: { typeInvariants: true },
            target: 'c99',
            optimize: false
        });

        console.log(result.c);
        ```
      </example>
      <example scenario="React playground component">
        Full CodeEditor + OutputDisplay integration example
      </example>
      <example scenario="Cloudflare Worker API">
        POST request/response handling with caching
      </example>
      <example scenario="Progressive loading with fallback">
        Lazy load + service worker cache + offline support
      </example>
    </examples>
    <generation_tools>
      TypeDoc (for API reference from TypeScript):
      - Auto-generate from .d.ts files
      - Integrate into website documentation
      - Command: typedoc --out docs/api dist/index.d.ts

      Markdown (for guides and tutorials):
      - Hand-written, version-controlled
      - Hosted on website docs section
      - Format: GitHub Flavored Markdown

      JSDoc (inline code documentation):
      - Document wrapper functions in TypeScript
      - Extracted by TypeDoc
    </generation_tools>
  </documentation_plan>

  <build_pipeline_plan>
    <ci_workflow>
      Three workflows:

      1. wasm-build.yml (build and test WASM)
      2. npm-publish.yml (publish to NPM on tag)
      3. deploy-worker.yml (deploy to Cloudflare Workers)
    </ci_workflow>
    <build_steps>
      <step name="Setup Emscripten" purpose="Install and activate Emscripten SDK">
        Uses: mymindstorm/setup-emsdk@v14
        Version: 3.1.50 (configurable)
        Cache: emsdk installation across runs
      </step>
      <step name="Build WASM Minimal" purpose="Compile core transpiler to WASM (size-optimized)">
        Commands:
        - emcmake cmake -B build-wasm-minimal -DCMAKE_BUILD_TYPE=Release
        - emmake cmake --build build-wasm-minimal --target cpptoc-wasm-minimal
        Output: cpptoc-minimal.js, cpptoc-minimal.wasm, cpptoc-minimal.d.ts
      </step>
      <step name="Build WASM Full" purpose="Compile full transpiler with ACSL to WASM (performance-optimized)">
        Commands:
        - emcmake cmake -B build-wasm-full -DCMAKE_BUILD_TYPE=Release
        - emmake cmake --build build-wasm-full --target cpptoc-wasm-full
        Output: cpptoc-full.js, cpptoc-full.wasm, cpptoc-full.d.ts
      </step>
      <step name="Size Check" purpose="Verify WASM sizes don't exceed thresholds">
        Check uncompressed, gzip, brotli sizes
        Fail if minimal > 25MB uncompressed or > 10MB Brotli
        Warn if full > 60MB uncompressed or > 25MB Brotli
      </step>
      <step name="Test" purpose="Run unit, integration, E2E tests">
        Commands:
        - npm run test:unit
        - npm run test:integration
        - npm run test:e2e (with Playwright)
      </step>
      <step name="Package" purpose="Create NPM package structure">
        Copy WASM artifacts to dist/
        Build TypeScript wrapper
        Generate package.json, README
      </step>
      <step name="Publish to NPM" purpose="Publish package to npm registry (on git tag)">
        Trigger: git tag v1.22.0
        Auth: NPM_TOKEN secret
        Command: npm publish --access public
      </step>
      <step name="Deploy to Cloudflare Workers" purpose="Deploy minimal build to Workers (optional)">
        Trigger: main branch push (after WASM build)
        Auth: CLOUDFLARE_API_TOKEN secret
        Command: wrangler deploy
      </step>
    </build_steps>
    <release_process>
      Versioning: Sync with main project (currently v1.22.0)

      Release steps:
      1. Update version in package.json, CMakeLists.txt, CHANGELOG.md
      2. Commit: git commit -m "chore: bump version to v1.22.0"
      3. Tag: git tag v1.22.0
      4. Push: git push && git push --tags
      5. GitHub Actions automatically:
         - Builds WASM artifacts
         - Runs tests
         - Publishes to NPM
         - Creates GitHub Release with artifacts
      6. Manual: Deploy Cloudflare Worker (if needed)

      Pre-release checklist:
      - [ ] All tests pass
      - [ ] Size regression check passes
      - [ ] CHANGELOG.md updated
      - [ ] Documentation up to date
      - [ ] Browser compatibility tested

      Versioning strategy:
      - Major: Breaking API changes
      - Minor: New ACSL phases, features
      - Patch: Bug fixes, size optimizations
    </release_process>
  </build_pipeline_plan>

  <implementation_phases>
    <phase number="1" name="Build System Setup &amp; Prototype">
      <tasks>
        <task priority="high">
          <description>Create minimal WASM prototype to measure actual size</description>
          <files_to_create>
            src/main_wasm_minimal.cpp (barebones Clang AST parsing only)
          </files_to_create>
          <files_to_modify>
            CMakeLists.txt (add minimal WASM target)
          </files_to_modify>
          <success_criteria>
            - Successful WASM compilation
            - Measured size: uncompressed, gzip, brotli
            - Compare to estimates (15-25MB uncompressed expected)
            - Determine Cloudflare Workers feasibility (3MB Brotli limit)
          </success_criteria>
        </task>
        <task priority="high">
          <description>Configure CMake for dual WASM builds (minimal + full)</description>
          <files_to_create>
            None (optional: cmake/EmscriptenToolchain.cmake)
          </files_to_create>
          <files_to_modify>
            CMakeLists.txt (add EMSCRIPTEN detection, two targets)
          </files_to_modify>
          <success_criteria>
            - emcmake cmake successfully configures project
            - cpptoc-wasm-minimal target builds with -Oz, --closure, -flto
            - cpptoc-wasm-full target builds with -O3
            - Both generate .js, .wasm, .d.ts files
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Set up Emscripten development environment</description>
          <files_to_create>
            .emscripten (config file)
            scripts/build-wasm.sh (build helper script)
          </files_to_create>
          <files_to_modify>
            README.md (add WASM build instructions)
          </files_to_modify>
          <success_criteria>
            - emsdk installed and activated
            - WASM build script works on clean checkout
            - Documentation covers prerequisites
          </success_criteria>
        </task>
      </tasks>
      <deliverables>
        <deliverable>Working WASM build targets in CMakeLists.txt</deliverable>
        <deliverable>Actual size measurements (validate estimates)</deliverable>
        <deliverable>Build script and documentation</deliverable>
      </deliverables>
      <verification>
        <check>Run: emcmake cmake -B build-wasm &amp;&amp; emmake cmake --build build-wasm</check>
        <check>Verify: cpptoc-minimal.wasm and cpptoc-full.wasm exist</check>
        <check>Measure: gzip -c cpptoc-minimal.wasm | wc -c (should be &lt; 10MB for viability)</check>
      </verification>
    </phase>

    <phase number="2" name="JavaScript/TypeScript API Implementation">
      <tasks>
        <task priority="high">
          <description>Implement embind bindings in src/main_wasm.cpp</description>
          <files_to_create>
            src/main_wasm.cpp (embind API definitions)
            include/WASMInterface.h (optional: shared types)
          </files_to_create>
          <files_to_modify>
            CMakeLists.txt (link --bind, --emit-tsd)
          </files_to_modify>
          <success_criteria>
            - TranspileOptions, TranspileResult, Diagnostic structs defined
            - transpile() function implemented and exported
            - getVersion() function exported
            - TypeScript .d.ts auto-generated by emcc
            - embind compiles without errors
          </success_criteria>
        </task>
        <task priority="high">
          <description>Refactor main.cpp logic into reusable transpile function</description>
          <files_to_create>
            src/TranspilerAPI.cpp (library-style transpile function)
            include/TranspilerAPI.h (public API header)
          </files_to_create>
          <files_to_modify>
            src/main.cpp (call TranspilerAPI instead of inline logic)
            src/main_wasm.cpp (call TranspilerAPI::transpile)
          </files_to_modify>
          <success_criteria>
            - TranspilerAPI::transpile(code, options) returns structured result
            - No filesystem I/O (in-memory only)
            - Works for both native CLI and WASM
            - All diagnostics captured in result object
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Create TypeScript wrapper package</description>
          <files_to_create>
            wasm-glue/src/index.ts
            wasm-glue/src/types.ts
            wasm-glue/tsconfig.json
            wasm-glue/package.json
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - TypeScript compiles without errors
            - Re-exports auto-generated types from .d.ts
            - Provides helper utilities (type guards, defaults)
            - npm run build succeeds
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Implement error handling across WASM boundary</description>
          <files_to_create>
            tests/unit/errors.test.ts
          </files_to_create>
          <files_to_modify>
            src/main_wasm.cpp (try/catch around transpilation)
          </files_to_modify>
          <success_criteria>
            - C++ exceptions caught and converted to error diagnostics
            - No unhandled exceptions crash WASM
            - JavaScript receives structured error objects
            - Test coverage for error scenarios
          </success_criteria>
        </task>
      </tasks>
      <deliverables>
        <deliverable>Embind API bindings (src/main_wasm.cpp)</deliverable>
        <deliverable>Auto-generated TypeScript definitions (.d.ts)</deliverable>
        <deliverable>TypeScript wrapper package (wasm-glue/)</deliverable>
        <deliverable>Refactored transpiler API (src/TranspilerAPI.cpp)</deliverable>
      </deliverables>
      <verification>
        <check>Compile: emmake cmake --build build-wasm --target cpptoc-wasm-minimal</check>
        <check>Load WASM in Node.js: node -e "import('./cpptoc.js').then(m => console.log(m.getVersion()))"</check>
        <check>TypeScript types: tsc --noEmit (should succeed)</check>
        <check>Run unit tests: npm run test:unit</check>
      </verification>
    </phase>

    <phase number="3" name="NPM Package Configuration">
      <tasks>
        <task priority="high">
          <description>Create package.json with dual exports</description>
          <files_to_create>
            package.json (in root or wasm-package/)
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - Exports: . (full), ./minimal, ./full
            - Type definitions included
            - Files: dist/**/*.{js,wasm,d.ts}
            - ESM-only (type: module)
          </success_criteria>
        </task>
        <task priority="high">
          <description>Write comprehensive README.md</description>
          <files_to_create>
            README.md (package root)
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - Installation instructions (npm, CDN)
            - Quick start example
            - API reference summary
            - Browser compatibility table
            - Link to full documentation
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Set up build scripts for package</description>
          <files_to_create>
            scripts/build-package.sh
            scripts/copy-wasm.js
          </files_to_create>
          <files_to_modify>
            package.json (add scripts: build, test, prepublishOnly)
          </files_to_modify>
          <success_criteria>
            - npm run build: builds WASM + TypeScript
            - npm run test: runs all tests
            - npm run prepublishOnly: validates before publish
            - Scripts work on clean checkout
          </success_criteria>
        </task>
        <task priority="low">
          <description>Create example code snippets</description>
          <files_to_create>
            examples/node/basic.js
            examples/browser/index.html
            examples/react/App.tsx
          </files_to_create>
          <files_to_modify>
            README.md (link to examples/)
          </files_to_modify>
          <success_criteria>
            - Each example is self-contained and runnable
            - Covers common use cases
            - Includes comments explaining key steps
          </success_criteria>
        </task>
      </tasks>
      <deliverables>
        <deliverable>package.json with dual exports configured</deliverable>
        <deliverable>README.md with installation and usage</deliverable>
        <deliverable>Build scripts for packaging</deliverable>
        <deliverable>Example code for common scenarios</deliverable>
      </deliverables>
      <verification>
        <check>npm pack: creates tarball with correct files</check>
        <check>Unpack and test: npm install ./hupyy-cpptoc-wasm-1.22.0.tgz &amp;&amp; node test.js</check>
        <check>Check exports: import from '@hupyy/cpptoc-wasm', '@hupyy/cpptoc-wasm/minimal', '@hupyy/cpptoc-wasm/full'</check>
      </verification>
    </phase>

    <phase number="4" name="Cloudflare Workers Deployment (Optional)">
      <tasks>
        <task priority="high">
          <description>Implement Cloudflare Worker entry point</description>
          <files_to_create>
            cloudflare-worker/src/index.ts
            cloudflare-worker/wrangler.toml
            cloudflare-worker/package.json
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - Worker handles POST requests with code/options
            - Returns TranspileResult JSON
            - CORS headers configured
            - Size limits enforced (100KB default)
          </success_criteria>
        </task>
        <task priority="high">
          <description>Validate minimal build fits Cloudflare size limits</description>
          <files_to_create>
            scripts/check-cloudflare-size.sh
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - Measure cpptoc-minimal.wasm Brotli compressed size
            - If &gt; 3MB: document limitation, skip Workers deployment
            - If ≤ 3MB: proceed with deployment
            - Decision documented in deployment plan
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Test Worker locally with Wrangler dev</description>
          <files_to_create>
            cloudflare-worker/test/worker.test.ts
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - wrangler dev starts local server
            - POST /: transpiles code successfully
            - Response matches TranspileResult schema
            - Error handling tested (invalid input, too large)
          </success_criteria>
        </task>
        <task priority="low">
          <description>Set up KV caching (optional optimization)</description>
          <files_to_create>
            None
          </files_to_create>
          <files_to_modify>
            cloudflare-worker/wrangler.toml (add KV binding)
            cloudflare-worker/src/index.ts (cache lookups)
          </files_to_modify>
          <success_criteria>
            - KV namespace created via Wrangler
            - Cache hit/miss logged
            - Cache TTL configurable via env var
          </success_criteria>
        </task>
      </tasks>
      <deliverables>
        <deliverable>Cloudflare Worker implementation (cloudflare-worker/)</deliverable>
        <deliverable>Size validation report (fits or doesn't fit)</deliverable>
        <deliverable>Local testing with Wrangler</deliverable>
        <deliverable>Deployment guide (docs/CLOUDFLARE.md)</deliverable>
      </deliverables>
      <verification>
        <check>wrangler dev: worker runs locally</check>
        <check>curl -X POST http://localhost:8787/ -d '{...}': returns valid JSON</check>
        <check>wrangler deploy: deploys to Workers (if size permits)</check>
        <check>Test live URL: curl https://cpptoc-transpiler.username.workers.dev/</check>
      </verification>
    </phase>

    <phase number="5" name="Website Integration">
      <tasks>
        <task priority="high">
          <description>Create TranspilerPlayground React component</description>
          <files_to_create>
            website/src/components/Transpiler/TranspilerPlayground.astro
            website/src/components/Transpiler/CodeEditor.tsx
            website/src/components/Transpiler/OutputDisplay.tsx
            website/src/components/Transpiler/OptionsPanel.tsx
            website/src/components/Transpiler/useTranspiler.ts
          </files_to_create>
          <files_to_modify>
            website/src/pages/playground.astro (use TranspilerPlayground)
          </files_to_modify>
          <success_criteria>
            - Split-pane editor (C++ input, C output, ACSL output)
            - Real-time transpilation (debounced)
            - ACSL options toggles work
            - Error messages display correctly
          </success_criteria>
        </task>
        <task priority="high">
          <description>Implement WASM lazy loading in useTranspiler hook</description>
          <files_to_create>
            None (part of useTranspiler.ts)
          </files_to_create>
          <files_to_modify>
            website/src/components/Transpiler/useTranspiler.ts
          </files_to_modify>
          <success_criteria>
            - WASM loads on first playground visit (not page load)
            - Loading state displayed to user
            - Error handling for WASM load failures
            - Module cached for subsequent uses
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Integrate CodeMirror 6 for code editing</description>
          <files_to_create>
            None
          </files_to_create>
          <files_to_modify>
            website/src/components/Transpiler/CodeEditor.tsx
            website/package.json (add codemirror dependencies)
          </files_to_modify>
          <success_criteria>
            - C++ syntax highlighting
            - Line numbers, basic editing features
            - Theme matches website design
            - Read-only mode for output panes
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Copy WASM files to website public/ directory</description>
          <files_to_create>
            scripts/copy-wasm-to-website.sh
          </files_to_create>
          <files_to_modify>
            website/public/wasm/full/ (add cpptoc.js, cpptoc.wasm)
          </files_to_modify>
          <success_criteria>
            - WASM files accessible at /cpp-to-c-website/wasm/full/cpptoc.wasm
            - locateFile() correctly resolves paths
            - Works in both dev and production builds
          </success_criteria>
        </task>
        <task priority="low">
          <description>Create inline example component for documentation</description>
          <files_to_create>
            website/src/components/Examples/InlineExample.astro
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - Embeddable in MDX documentation pages
            - Click to transpile → modal with results
            - Reuses same WASM module as playground
          </success_criteria>
        </task>
      </tasks>
      <deliverables>
        <deliverable>TranspilerPlayground component (fully functional)</deliverable>
        <deliverable>CodeMirror integration</deliverable>
        <deliverable>WASM lazy loading implementation</deliverable>
        <deliverable>Inline example component for docs</deliverable>
      </deliverables>
      <verification>
        <check>npm run dev (in website/): playground loads without errors</check>
        <check>Type C++ code: transpiles in real-time</check>
        <check>Toggle ACSL options: output updates accordingly</check>
        <check>Check browser console: WASM loads successfully</check>
        <check>Test on mobile: responsive layout works</check>
      </verification>
    </phase>

    <phase number="6" name="Testing &amp; CI/CD">
      <tasks>
        <task priority="high">
          <description>Write unit tests for WASM API</description>
          <files_to_create>
            tests/unit/api.test.ts
            tests/unit/types.test.ts
            tests/unit/errors.test.ts
          </files_to_create>
          <files_to_modify>
            package.json (add vitest scripts)
          </files_to_modify>
          <success_criteria>
            - All API functions tested (transpile, getVersion)
            - Type safety verified
            - Error handling tested
            - Code coverage &gt; 80%
          </success_criteria>
        </task>
        <task priority="high">
          <description>Write integration tests for transpilation workflows</description>
          <files_to_create>
            tests/integration/transpile.test.ts
            tests/integration/acsl-phase1.test.ts
            tests/integration/acsl-phase2.test.ts
            tests/integration/acsl-phase3.test.ts
            tests/integration/acsl-phase4.test.ts
            tests/integration/acsl-phase5.test.ts
            tests/integration/size.test.ts
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - Each ACSL phase tested with real examples
            - Output correctness verified
            - Size regression tests (fail if &gt; thresholds)
            - Tests run in CI
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Create GitHub Actions workflow for WASM builds</description>
          <files_to_create>
            .github/workflows/wasm-build.yml
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - Workflow triggers on push/PR
            - Builds minimal and full WASM
            - Runs all tests
            - Uploads build artifacts
            - Size checks pass
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Write E2E tests for playground (Playwright)</description>
          <files_to_create>
            tests/e2e/playground.spec.ts
            playwright.config.ts
          </files_to_create>
          <files_to_modify>
            package.json (add playwright)
          </files_to_modify>
          <success_criteria>
            - Test loads playground page
            - Types code, verifies output appears
            - Tests ACSL option toggles
            - Cross-browser (Chrome, Firefox, Safari)
          </success_criteria>
        </task>
        <task priority="low">
          <description>Set up performance benchmarks</description>
          <files_to_create>
            tests/perf/load-time.test.ts
            tests/perf/transpile-speed.test.ts
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - Baseline metrics recorded
            - Regression detection (alert if &gt;20% slower)
            - Results logged in CI
          </success_criteria>
        </task>
      </tasks>
      <deliverables>
        <deliverable>Comprehensive test suite (unit, integration, E2E)</deliverable>
        <deliverable>GitHub Actions CI/CD workflow</deliverable>
        <deliverable>Size regression monitoring</deliverable>
        <deliverable>Performance benchmarks</deliverable>
      </deliverables>
      <verification>
        <check>npm run test: all tests pass</check>
        <check>GitHub Actions: green checkmark on commits</check>
        <check>Size check: minimal &lt; 25MB, full &lt; 60MB uncompressed</check>
        <check>E2E: npx playwright test (passes on all browsers)</check>
      </verification>
    </phase>

    <phase number="7" name="Documentation &amp; Release">
      <tasks>
        <task priority="high">
          <description>Write comprehensive documentation</description>
          <files_to_create>
            docs/INSTALLATION.md
            docs/API.md
            docs/EXAMPLES.md
            docs/CLOUDFLARE.md
            docs/WEBSITE.md
            docs/BUILDING.md
            docs/TROUBLESHOOTING.md
          </files_to_create>
          <files_to_modify>
            README.md (add links to docs)
          </files_to_modify>
          <success_criteria>
            - All use cases documented with examples
            - API reference complete (TypeDoc or manual)
            - Troubleshooting covers common errors
            - Building from source instructions tested
          </success_criteria>
        </task>
        <task priority="high">
          <description>Create NPM publish workflow</description>
          <files_to_create>
            .github/workflows/npm-publish.yml
          </files_to_create>
          <files_to_modify>
            package.json (add prepublishOnly script)
          </files_to_modify>
          <success_criteria>
            - Workflow triggers on git tag (v1.22.0)
            - Builds WASM, runs tests, publishes to NPM
            - Creates GitHub Release with artifacts
            - Dry run tested with npm pack
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Generate CHANGELOG.md</description>
          <files_to_create>
            CHANGELOG.md
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - Format: Keep a Changelog
            - Sections: Added, Changed, Fixed, Removed
            - Version 1.22.0 initial release documented
          </success_criteria>
        </task>
        <task priority="medium">
          <description>Create example gallery on website</description>
          <files_to_create>
            website/src/pages/examples.astro (expand existing)
            website/src/data/examples.ts (example code snippets)
          </files_to_create>
          <files_to_modify>
            None
          </files_to_modify>
          <success_criteria>
            - 5-10 curated examples
            - Each with transpile button and result display
            - Categories: Basic, Classes, Templates, ACSL
          </success_criteria>
        </task>
        <task priority="low">
          <description>Publish v1.22.0 release</description>
          <files_to_create>
            None
          </files_to_create>
          <files_to_modify>
            package.json (version: "1.22.0")
          </files_to_modify>
          <success_criteria>
            - NPM package published: @hupyy/cpptoc-wasm@1.22.0
            - GitHub Release created with WASM artifacts
            - Website updated with playground
            - Announcement (README, social media)
          </success_criteria>
        </task>
      </tasks>
      <deliverables>
        <deliverable>Complete documentation suite (docs/)</deliverable>
        <deliverable>NPM publish automation</deliverable>
        <deliverable>CHANGELOG.md</deliverable>
        <deliverable>Example gallery on website</deliverable>
        <deliverable>v1.22.0 release published</deliverable>
      </deliverables>
      <verification>
        <check>Read docs: complete and accurate</check>
        <check>npm install @hupyy/cpptoc-wasm: works</check>
        <check>import createCppToC from '@hupyy/cpptoc-wasm/full': loads correctly</check>
        <check>Website playground: fully functional</check>
        <check>GitHub Release: contains all artifacts</check>
      </verification>
    </phase>
  </implementation_phases>

  <dependencies>
    <external>
      <tool name="Emscripten" version="3.1.50+" install_command="git clone https://github.com/emscripten-core/emsdk.git &amp;&amp; cd emsdk &amp;&amp; ./emsdk install latest &amp;&amp; ./emsdk activate latest &amp;&amp; source ./emsdk_env.sh"/>
      <tool name="CMake" version="3.20+" install_command="brew install cmake (macOS) | apt install cmake (Ubuntu)"/>
      <tool name="Node.js" version="18+" install_command="https://nodejs.org/ or nvm install 18"/>
      <tool name="Clang/LLVM" version="15+" install_command="Already required for main project"/>
      <tool name="Wrangler" version="3.90+" install_command="npm install -g wrangler (optional, for Cloudflare Workers)"/>
      <tool name="Playwright" version="latest" install_command="npm install -D @playwright/test (for E2E tests)"/>
    </external>
    <internal>
      <dependency>Research findings from 032-wasm-library-research (size estimates, feasibility analysis)</dependency>
      <dependency>Existing transpiler codebase (src/, include/)</dependency>
      <dependency>Website infrastructure (Astro 5.16.6, React 19.2.3)</dependency>
      <dependency>CMake build system (CMakeLists.txt)</dependency>
    </internal>
  </dependencies>

  <risks>
    <risk severity="high">
      <description>Actual WASM size exceeds estimates, making Cloudflare Workers deployment impossible</description>
      <mitigation>
        Phase 1 prototype measures real size early
        If &gt; 3MB Brotli: document limitation, skip Workers, deploy only to CDN
        Investigate aggressive tree shaking of Clang libraries
        Fallback: Cloudflare Pages Functions (different size limits)
      </mitigation>
    </risk>
    <risk severity="high">
      <description>Clang LibTooling incompatibility with Emscripten WASM backend</description>
      <mitigation>
        Research shows Clang can compile to WASM (Emscripten uses Clang)
        Test minimal prototype in Phase 1 to validate
        If blockers found: explore alternative parsing libraries or custom AST
        Fallback: Server-side transpilation only (no browser WASM)
      </mitigation>
    </risk>
    <risk severity="medium">
      <description>WASM load time too slow (&gt;5 seconds) degrades user experience</description>
      <mitigation>
        Progressive loading: only on user interaction (lazy)
        Service Worker caching: instant on repeat visits
        Show progress indicator during load
        Optimize with -Oz, --closure, -flto
        Fallback: Precompile common examples server-side
      </mitigation>
    </risk>
    <risk severity="medium">
      <description>embind TypeScript generation incomplete or incorrect</description>
      <mitigation>
        Test --emit-tsd in Phase 2
        Manual .d.ts authoring if auto-generation insufficient
        TypeScript strict mode catches type mismatches
        Unit tests validate API contract
      </mitigation>
    </risk>
    <risk severity="low">
      <description>Cross-browser WASM compatibility issues</description>
      <mitigation>
        Target browsers: Chrome 92+, Firefox 90+, Safari 15.2+ (documented)
        Playwright E2E tests cover all major browsers
        Fallback: Server-side API for unsupported browsers
        Display compatibility warning on older browsers
      </mitigation>
    </risk>
    <risk severity="low">
      <description>NPM package distribution issues (WASM files not included or too large)</description>
      <mitigation>
        Test npm pack before publish
        Verify files array in package.json includes .wasm
        NPM allows packages up to 100MB (well within limits)
        CDN alternative: unpkg, jsdelivr for direct WASM access
      </mitigation>
    </risk>
  </risks>

  <open_questions>
    <question priority="high">
      <question>What is the actual compiled size of the minimal WASM build?</question>
      <impact>Determines Cloudflare Workers feasibility. If &gt; 3MB Brotli, Workers deployment not viable.</impact>
    </question>
    <question priority="high">
      <question>Can we selectively link only required Clang/LLVM components to reduce size?</question>
      <impact>Potential 30-60% size reduction if aggressive tree shaking works. Critical for Workers deployment.</impact>
    </question>
    <question priority="medium">
      <question>Should we implement code splitting for ACSL annotators as separate WASM modules?</question>
      <impact>Reduces initial load to core transpiler only. Adds complexity. Deferred to Phase 2 if needed.</impact>
    </question>
    <question priority="medium">
      <question>Is 3-5 second initial load time acceptable to users?</question>
      <impact>UX design decision. Mitigated by lazy loading, caching, progress indicators. User testing recommended.</impact>
    </question>
    <question priority="low">
      <question>Should we support Node.js WASM usage (not just browser)?</question>
      <impact>NPM package already ESM-compatible with Node.js 18+. Minimal additional work, worth supporting.</impact>
    </question>
    <question priority="low">
      <question>Do we need Web Worker support for background transpilation?</question>
      <impact>Improves UI responsiveness. Adds complexity. Deferred to post-v1.22.0 enhancement.</impact>
    </question>
  </open_questions>

  <assumptions>
    <assumption>
      <statement>Cloudflare Workers size limits are 10MB uncompressed OR 3MB Brotli compressed (paid tier)</statement>
      <basis>documented (Cloudflare official docs)</basis>
    </assumption>
    <assumption>
      <statement>Emscripten embind supports automatic TypeScript generation via --emit-tsd</statement>
      <basis>documented (Emscripten 3.1.25+ documentation)</basis>
    </assumption>
    <assumption>
      <statement>WASM compression ratio: ~50% gzip, ~42% Brotli</statement>
      <basis>research (measured from sql.js, FFmpeg.wasm)</basis>
    </assumption>
    <assumption>
      <statement>Clang LibTooling will compile to 15-50MB uncompressed WASM</statement>
      <basis>expert (extrapolated from native executable sizes, WASM overhead)</basis>
    </assumption>
    <assumption>
      <statement>ACSL annotators add 2-5MB total uncompressed</statement>
      <basis>expert (source file analysis, typical C++ class sizes)</basis>
    </assumption>
    <assumption>
      <statement>Users accept 3-5 second load time for full-featured transpiler</statement>
      <basis>expert (common for large WASM apps like FFmpeg.wasm)</basis>
    </assumption>
    <assumption>
      <statement>Astro + Vite support WASM without additional plugins</statement>
      <basis>documented (Astro 0.21+, Vite native WASM support)</basis>
    </assumption>
    <assumption>
      <statement>Service Worker caching makes subsequent loads instant</statement>
      <basis>documented (Service Workers + Cache API standard practice)</basis>
    </assumption>
  </assumptions>

  <next_steps>
    <step>Implement Phase 1: Build System Setup &amp; Prototype (measure actual WASM size)</step>
    <step>Validate Cloudflare Workers feasibility based on measured size</step>
    <step>Implement Phase 2: JavaScript/TypeScript API (embind bindings)</step>
    <step>Continue through phases 3-7 sequentially</step>
    <step>Publish v1.22.0 release to NPM</step>
  </next_steps>
</plan_output>

# Transpiler Website Technology Research

**Research Date**: 2025-12-19
**Purpose**: Select optimal tech stack for C++ to C transpiler documentation/demo website with WebAssembly multi-threading support

<research>
  <summary>
    Comprehensive research for C++ to C transpiler documentation/demo website with WebAssembly
    multi-threading support. Analyzed 4 static site generators, 4 deployment platforms, 2 code
    editors, and repository architecture patterns.

    **TOP RECOMMENDATIONS**:
    - Framework: **Astro** (component islands, flexibility, WebAssembly support, SEO-friendly)
    - Deployment: **Vercel** (native COOP/COEP headers, zero config, preview deployments)
    - Code Editor: **CodeMirror 6** (6-8x smaller than Monaco, excellent performance)
    - Repository: **Monorepo** (website/ directory in main repo - simpler for solo developer)
    - Headers: **COEP: credentialless + COOP: same-origin** (best third-party compatibility)

    **CRITICAL FINDINGS**:
    - WebAssembly multi-threading requires COOP/COEP headers (cross-origin isolation mandatory)
    - Next.js static exports DON'T support header configuration (dealbreaker)
    - GitHub Pages requires service worker workaround with poor UX (page reload on first visit)
    - Vercel and Netlify both provide native header support (no workarounds needed)
    - CodeMirror 6 validated by industry (Sourcegraph, Replit migrated from Monaco)
    - SharedArrayBuffer widely supported since December 2021 across all modern browsers

    **IMPLEMENTATION PATH**:
    1. Create website/ directory in hupyy-cpp-to-c (monorepo approach)
    2. Initialize Astro with React integration for interactive components
    3. Install CodeMirror 6 for split-pane code editor (C++ input | C output)
    4. Configure vercel.json with COOP/COEP headers
    5. Build transpiler WASM with Emscripten (-pthread, -sPROXY_TO_PTHREAD, -sMALLOC=mimalloc)
    6. Deploy to Vercel with automatic builds from git push

    All recommendations backed by official documentation, verified with real-world case studies,
    and optimized for solo developer workflow with emphasis on simplicity and best practices.
  </summary>

  <findings>

    <!-- ===================== -->
    <!-- FRAMEWORK COMPARISON  -->
    <!-- ===================== -->

    <finding category="frameworks" priority="critical">
      <framework name="Astro">
        <capabilities>
          <typescript>Full TypeScript support</typescript>
          <build_performance>Fast build times with Vite-based architecture</build_performance>
          <documentation_features>
            - Markdown and MDX support
            - Component islands architecture
            - Static site generation by default
          </documentation_features>
          <webassembly_support>
            - Can load and use WebAssembly modules
            - Middleware support for request/response manipulation
          </webassembly_support>
        </capabilities>

        <headers_configuration>
          <static_sites>
            - No built-in way to define custom HTTP headers for statically-generated pages
            - Requires platform-specific configuration files (_headers, netlify.toml, vercel.json)
            - Third-party plugin available: astro-static-headers captures headers during prerender
          </static_sites>
          <workarounds>
            - Middleware (only works for SSR/on-demand rendering, not static)
            - Platform configuration files (Netlify, Vercel, Cloudflare)
            - astro-static-headers integration for automatic config generation
          </workarounds>
          <sources>
            - https://docs.astro.build/en/guides/middleware/
            - https://github.com/abemedia/astro-static-headers
            - https://dev.to/cassidoo/three-ways-to-set-headers-with-netlify-and-astro-1iib
          </sources>
        </headers_configuration>

        <pros>
          + Component islands for optimal performance
          + Flexible - can use React, Vue, Svelte components
          + Excellent developer experience
          + Fast build times
          + SEO-friendly static output
        </pros>

        <cons>
          - Headers for static sites require platform-specific configuration
          - Less documentation-focused compared to Docusaurus
          - Requires additional setup for code playgrounds
        </cons>

        <recommendation>
          Excellent choice for custom documentation sites with flexibility, but requires
          platform-specific header configuration for WebAssembly multi-threading
        </recommendation>
      </framework>

      <framework name="Next.js">
        <capabilities>
          <typescript>First-class TypeScript support</typescript>
          <build_performance>Good performance with Turbopack (dev), moderate for large static exports</build_performance>
          <documentation_features>
            - MDX support via plugins
            - File-based routing
            - Image optimization
            - Can use Nextra for documentation sites
          </documentation_features>
          <webassembly_support>
            - Full WebAssembly support
            - Can use web workers
            - Dynamic WASM compilation NOT available in middleware
          </webassembly_support>
        </capabilities>

        <headers_configuration>
          <ssr_mode>
            - Excellent: next.config.js headers() function
            - Full control over headers per route
            ```javascript
            module.exports = {
              async headers() {
                return [{
                  source: '/:path*',
                  headers: [
                    { key: 'Cross-Origin-Opener-Policy', value: 'same-origin' },
                    { key: 'Cross-Origin-Embedder-Policy', value: 'require-corp' }
                  ]
                }]
              }
            }
            ```
          </ssr_mode>
          <static_export>
            - CRITICAL LIMITATION: Headers from next.config.js do NOT work with static exports
            - With output: 'export', headers configuration is ignored
            - Must rely on platform-specific configuration files
            - Headers are checked before filesystem which includes pages and /public files
          </static_export>
          <sources>
            - https://nextjs.org/docs/pages/api-reference/config/next-config-js/headers
            - https://nextjs.org/docs/app/guides/static-exports
          </sources>
        </headers_configuration>

        <pros>
          + Mature ecosystem with extensive documentation
          + Excellent TypeScript support
          + Large community and plugins
          + Can use Nextra for documentation sites
        </pros>

        <cons>
          - Headers configuration DOES NOT WORK for static exports (critical issue)
          - Heavier bundle size compared to alternatives
          - Overkill for pure documentation sites
          - SSR features unused if only doing static generation
        </cons>

        <recommendation>
          NOT recommended for this use case due to static export header limitations.
          Would require server-side rendering (defeating static site benefits) or
          platform-specific workarounds identical to simpler frameworks.
        </recommendation>
      </framework>

      <framework name="Docusaurus">
        <capabilities>
          <typescript>TypeScript support available (dedicated docs section)</typescript>
          <build_performance>Good performance with Webpack 5</build_performance>
          <documentation_features>
            - Built specifically for documentation sites
            - Full site searchability (built-in)
            - Document versioning
            - Internationalization (i18n)
            - MDX for interactive components
            - SEO friendly with static HTML
          </documentation_features>
          <webassembly_support>
            - Can use WebAssembly modules
            - WebAssembly syntax highlighting in code blocks
            - No specific WebAssembly playground plugin found
          </webassembly_support>
        </capabilities>

        <headers_configuration>
          <static_sites>
            - Similar to other static generators: requires platform-specific configuration
            - No built-in header configuration for static builds
            - Must use _headers, netlify.toml, vercel.json, etc.
          </static_sites>
          <sources>
            - https://docusaurus.io/docs
          </sources>
        </headers_configuration>

        <code_playground>
          <available_plugins>
            - @docusaurus/theme-live-codeblock: React/JSX live code execution
            - Uses react-live for interactive playgrounds
            - WebAssembly support limited to syntax highlighting, not execution
          </available_plugins>
          <sources>
            - https://docusaurus.io/docs/playground
            - https://docuxlab.com/blog/docusaurus-react-live-guide/
          </sources>
        </code_playground>

        <pros>
          + Purpose-built for documentation (best documentation features)
          + Excellent built-in search
          + Versioning support (useful for transpiler releases)
          + i18n support
          + Active community (Meta-backed)
        </pros>

        <cons>
          - Headers require platform configuration (same as others)
          - Live code playground focused on React, not WebAssembly
          - Heavier than minimalist options
          - Less flexible than Astro for custom components
        </cons>

        <recommendation>
          Best choice if documentation features (versioning, search, i18n) are priorities,
          but requires custom WebAssembly playground implementation and platform-specific
          header configuration.
        </recommendation>
      </framework>

      <framework name="VitePress">
        <capabilities>
          <typescript>Not explicitly covered in main docs (needs verification)</typescript>
          <build_performance>
            - Excellent runtime performance (near-perfect PageSpeed scores)
            - Fast initial load with pre-rendered HTML
            - Instant server start with Vite (sub-100ms reflection)
            - SPA navigation after initial load
          </build_performance>
          <documentation_features>
            - Built for technical documentation
            - Built-in Markdown extensions (frontmatter, tables, syntax highlighting)
            - Vue component integration
            - Default theme designed for docs
          </documentation_features>
          <webassembly_support>
            - Not mentioned in official docs
            - Vite-based, so should support WebAssembly
          </webassembly_support>
        </capabilities>

        <headers_configuration>
          <static_sites>
            - KNOWN ISSUE: VitePress does NOT respect server.headers in Vite config
            - Headers must be configured through platform-specific files
            - _headers file should be placed in public directory (docs/public/_headers)
            - Copied verbatim to output directory
          </static_sites>
          <cache_control>
            - Supports cache-control headers for static assets
            - Uses hashed filenames for cache-busting
          </cache_control>
          <sources>
            - https://vitepress.dev/guide/deploy
            - https://github.com/vuejs/vitepress/issues/2195
          </sources>
        </headers_configuration>

        <pros>
          + Lightweight and extremely fast
          + Excellent runtime performance
          + Vue-powered (if you prefer Vue over React)
          + Minimal configuration needed
          + Best PageSpeed scores
        </pros>

        <cons>
          - Does NOT respect Vite config headers (known limitation)
          - Smaller ecosystem compared to Next.js/Docusaurus
          - Less documentation about advanced features
          - Vue-centric (may not fit if team prefers React)
        </cons>

        <recommendation>
          Good choice for lightweight, fast documentation sites, but requires
          platform-specific header configuration and may have limited community
          resources for WebAssembly integration.
        </recommendation>
      </framework>
    </finding>

    <!-- ================================ -->
    <!-- WEBASSEMBLY MULTI-THREADING      -->
    <!-- ================================ -->

    <finding category="webassembly" priority="critical">
      <requirement type="security_headers">
        <overview>
          SharedArrayBuffer and WebAssembly multi-threading require cross-origin isolation,
          which is enforced through specific HTTP headers. This is a security measure
          implemented after Spectre vulnerability mitigations in 2018.
        </overview>

        <required_headers>
          <header name="Cross-Origin-Opener-Policy">
            <value>same-origin</value>
            <purpose>
              Creates separate browsing context groups, preventing cross-origin windows
              from directly accessing each other
            </purpose>
          </header>

          <header name="Cross-Origin-Embedder-Policy">
            <value>require-corp OR credentialless</value>
            <purpose>
              require-corp: Requires all embedded resources to opt-in via CORP headers
              credentialless: Alternative mode with better compatibility for third-party resources
            </purpose>
            <recommendation>Use credentialless for better third-party resource compatibility</recommendation>
          </header>
        </required_headers>

        <verification>
          <javascript>
            // Check if cross-origin isolation is enabled
            if (crossOriginIsolated) {
              const buffer = new SharedArrayBuffer(16);
              // Can use SharedArrayBuffer and WebAssembly threads
            }
          </javascript>
        </verification>

        <sources>
          - https://web.dev/articles/coop-coep
          - https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/SharedArrayBuffer
          - https://developer.mozilla.org/en-US/docs/Web/HTTP/Reference/Headers/Cross-Origin-Embedder-Policy
        </sources>
      </requirement>

      <requirement type="browser_compatibility">
        <status>Widely available since December 2021</status>
        <browsers>
          - Chrome: Full support
          - Firefox: Full support
          - Safari: Full support
          - Edge: Full support
        </browsers>
        <note>
          SharedArrayBuffer constructor visibility on global object is hidden without
          proper headers for web compatibility reasons
        </note>
        <sources>
          - https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/SharedArrayBuffer
        </sources>
      </requirement>

      <requirement type="emscripten_configuration">
        <compilation_flags>
          <flag>-pthread</flag>
          <description>Must be used when compiling AND linking</description>
          <detection>#ifdef __EMSCRIPTEN_PTHREADS__</detection>
        </compilation_flags>

        <worker_pool>
          <flag>-sPTHREAD_POOL_SIZE=&lt;expression&gt;</flag>
          <examples>
            - Fixed number: -sPTHREAD_POOL_SIZE=8
            - Dynamic: -sPTHREAD_POOL_SIZE=navigator.hardwareConcurrency
          </examples>
          <purpose>
            Pre-creates web workers before main() to avoid waiting for browser event iteration
          </purpose>
        </worker_pool>

        <best_practices>
          <practice name="PROXY_TO_PTHREAD">
            <flag>-sPROXY_TO_PTHREAD</flag>
            <purpose>
              Moves main() to a pthread, keeping browser main thread responsive for DOM/events
              Avoids deadlock issues
            </purpose>
          </practice>

          <practice name="Memory Allocator">
            <flag>-sMALLOC=mimalloc</flag>
            <purpose>
              Better multi-threaded performance vs default dlmalloc (single global lock)
            </purpose>
          </practice>

          <practice name="Deployment Headers">
            <critical>
              Pthreads code will NOT work in deployed environment unless COOP/COEP headers
              are correctly set
            </critical>
          </practice>
        </best_practices>

        <limitation>
          Cannot build one binary that works with and without multi-threading.
          Must create separate builds and select at runtime.
        </limitation>

        <sources>
          - https://emscripten.org/docs/porting/pthreads.html
        </sources>
      </requirement>

      <resource_implications>
        <cors_requirements>
          When COEP is enabled with require-corp, ALL subresources must include either:
          - CORP header: Cross-Origin-Resource-Policy: same-origin|same-site|cross-origin
          - CORS attributes: &lt;img crossorigin&gt;, &lt;script crossorigin&gt;

          Resources without proper headers will be BLOCKED.
        </cors_requirements>

        <third_party_resources>
          <problem>
            Third-party resources (CDNs, analytics, fonts) may not have appropriate CORP headers
          </problem>
          <solutions>
            - Use COEP: credentialless instead of require-corp (better compatibility)
            - Self-host all resources
            - Request third-party providers add CORP headers
          </solutions>
        </third_party_resources>
      </resource_implications>
    </finding>

    <!-- ========================= -->
    <!-- CODE EDITOR COMPARISON    -->
    <!-- ========================= -->

    <finding category="code_editors" priority="high">
      <comparison>
        <editor name="Monaco Editor">
          <overview>
            Powers VS Code. Comprehensive out-of-the-box features including TypeScript
            language services, IntelliSense, and full IDE-like experience.
          </overview>

          <bundle_size>
            <uncompressed>5-10 MB</uncompressed>
            <minified_gzipped>2-2.4 MB minimum (optimized)</minified_gzipped>
            <core_config>800 KB - 1 MB for basic setup</core_config>
            <real_world_example>
              Replit before migration: 51.17 MB uncompressed (5.01 MB gzipped)
              Even optimized: 2.4 MB download (40% of search page JavaScript)
            </real_world_example>
          </bundle_size>

          <performance>
            - Many optimizations built-in
            - Can feel clunky on low-powered machines
            - Heavy initial load time
            - Feature-rich but resource-intensive
          </performance>

          <pros>
            + VS Code compatibility
            + Advanced IntelliSense
            + TypeScript language services included
            + Comprehensive feature set out-of-box
            + Familiar to VS Code users
          </pros>

          <cons>
            - Large bundle size (2+ MB minimum)
            - Performance issues on low-end devices
            - Difficult to tree-shake unused features
            - Overkill for simple use cases
          </cons>

          <sources>
            - https://agenthicks.com/research/codemirror-vs-monaco-editor-comparison
            - https://sourcegraph.com/blog/migrating-monaco-codemirror
            - https://blog.replit.com/codemirror
          </sources>
        </editor>

        <editor name="CodeMirror 6">
          <overview>
            Modern, modular code editor with excellent performance and customization.
            Complete rewrite from CodeMirror 5 with focus on mobile, accessibility, and modularity.
          </overview>

          <bundle_size>
            <core>~300 KB for basic functionality</core>
            <minified_gzipped>124 KB (minimal setup)</minified_gzipped>
            <with_extensions>~1.26 MB gzipped with all extensions and language packages</with_extensions>
            <real_world_example>
              Replit after migration: 8.23 MB uncompressed (1.26 MB gzipped) with full features
              Compared to 51.17 MB with Monaco - ~6x smaller
            </real_world_example>
          </bundle_size>

          <performance>
            - Significantly more lightweight than Monaco
            - Very performant even on low-powered machines
            - Fast initial load
            - Efficient rendering
          </performance>

          <architecture>
            - Modular design allows including only necessary features
            - Excellent tree-shaking support
            - Can build minimal configurations
            - Extensible through plugin system
          </architecture>

          <pros>
            + 6-8x smaller bundle than Monaco
            + Excellent performance on all devices
            + Highly customizable and modular
            + Good mobile support
            + Active development
            + Can achieve ~300KB for basic editor
          </pros>

          <cons>
            - Less feature-complete out-of-box than Monaco
            - Requires more setup for advanced features
            - Smaller ecosystem than Monaco
            - May need custom language support
          </cons>

          <migration_examples>
            - Sourcegraph: Migrated from Monaco to CodeMirror 6
            - Replit: Migrated from Monaco to CodeMirror 6
            - Both cite performance and bundle size as key reasons
          </migration_examples>

          <sources>
            - https://agenthicks.com/research/codemirror-vs-monaco-editor-comparison
            - https://sourcegraph.com/blog/migrating-monaco-codemirror
            - https://blog.replit.com/codemirror
            - https://npm-compare.com/codemirror,monaco-editor
          </sources>
        </editor>

        <recommendation>
          <choice>CodeMirror 6</choice>
          <rationale>
            For a transpiler documentation site with code playground:

            1. Bundle size matters: Users want fast page loads. CodeMirror 6 is 6-8x smaller.
            2. Performance critical: Real-time transpilation + code editing + WASM execution
               requires efficient editor. CodeMirror 6 performs better.
            3. Mobile users: Documentation sites accessed on mobile. CodeMirror 6 better mobile support.
            4. Feature needs: Don't need full TypeScript IntelliSense for C++ to C transpilation demo.
               Syntax highlighting and basic editing sufficient.
            5. Industry trend: Major companies (Sourcegraph, Replit) migrating from Monaco to CodeMirror 6.

            Monaco only recommended if you need full VS Code compatibility or advanced TypeScript features.
          </rationale>
        </recommendation>
      </comparison>
    </finding>

    <!-- ========================== -->
    <!-- DEPLOYMENT PLATFORMS       -->
    <!-- ========================== -->

    <finding category="deployment" priority="critical">
      <platform name="GitHub Pages">
        <overview>
          Free static hosting for GitHub repositories. Widely used but has significant
          limitations for WebAssembly multi-threading due to lack of custom header support.
        </overview>

        <headers_support>
          <native_support>NONE - GitHub Pages does NOT provide control over HTTP headers</native_support>
          <critical_issue>
            Cannot set COOP/COEP headers natively, making it impossible to use
            SharedArrayBuffer and multi-threaded WebAssembly without workarounds
          </critical_issue>
        </headers_support>

        <workarounds>
          <service_worker_solution>
            <library>coi-serviceworker</library>
            <how_it_works>
              Service workers can set COOP/COEP headers client-side. The coi-serviceworker
              library by Guido Zuidhof implements this pattern.
            </how_it_works>
            <implementation>
              1. Include coi-serviceworker script in your HTML
              2. Script installs service worker on first page load
              3. Service worker intercepts requests and adds COOP/COEP headers
              4. Page reloads automatically on first visit to activate headers
            </implementation>
            <trade_offs>
              - Requires browser service worker support
              - Page reloads on first visit (poor UX)
              - Client-side JavaScript must execute
              - Adds complexity and potential points of failure
            </trade_offs>
            <sources>
              - https://blog.tomayac.com/2025/03/08/setting-coop-coep-headers-on-static-hosting-like-github-pages/
              - https://github.com/819460357/coi-serviceworker
              - https://dev.to/stefnotch/enabling-coop-coep-without-touching-the-server-2d3n
            </sources>
          </service_worker_solution>

          <community_discussion>
            Active GitHub discussion requesting this feature since many libraries
            (image editing, ML) require SharedArrayBuffer, making header support
            increasingly important. No timeline for native support from GitHub.

            Source: https://github.com/orgs/community/discussions/13309
          </community_discussion>
        </workarounds>

        <pros>
          + Free and unlimited bandwidth
          + Direct integration with GitHub repositories
          + Simple setup (push to gh-pages branch)
          + Good for open source projects
          + Custom domains supported
        </pros>

        <cons>
          - NO native header support (critical blocker)
          - Requires service worker workaround for WebAssembly multi-threading
          - Service worker solution has poor UX (page reload)
          - No build optimization features
          - Limited to static content
        </cons>

        <recommendation>
          NOT RECOMMENDED for WebAssembly multi-threading use case without accepting
          service worker workaround limitations. Only consider if you accept the
          page reload UX cost or don't need multi-threading.
        </recommendation>
      </platform>

      <platform name="Vercel">
        <overview>
          Modern hosting platform with excellent static site support and first-class
          Next.js integration. Provides full control over headers.
        </overview>

        <headers_support>
          <native_support>EXCELLENT - Full header configuration support</native_support>
          <configuration_method>
            Use vercel.json in repository root:
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
          </configuration_method>
          <route_specific>Can configure headers per route using source patterns</route_specific>
        </headers_support>

        <webassembly_support>
          <status>Full support for WebAssembly</status>
          <requirements>
            - HTTPS required (automatic on Vercel)
            - Configure COOP/COEP headers via vercel.json
            - SharedArrayBuffer works once headers are set
          </requirements>
          <documentation>
            - https://vercel.com/docs/functions/wasm
            - https://vercel.com/docs/concepts/edge-network/headers
          </documentation>
        </webassembly_support>

        <features>
          - Automatic HTTPS with certificates
          - Edge network for global performance
          - Preview deployments for every git push
          - Analytics and performance monitoring
          - Automatic builds from git
          - Environment variables support
          - Custom domains
        </features>

        <free_tier>
          <limits>
            - 100 GB bandwidth per month
            - Unlimited static sites
            - Commercial use allowed
            - Sufficient for documentation sites
          </limits>
        </free_tier>

        <pros>
          + Full header configuration support (no workarounds needed)
          + Excellent developer experience
          + Automatic preview deployments
          + Fast global CDN
          + Zero configuration for common frameworks
          + Great documentation
        </pros>

        <cons>
          - Bandwidth limits on free tier (generous but exists)
          - Vendor lock-in considerations
          - May be overkill for simple static sites
        </cons>

        <recommendation>
          HIGHLY RECOMMENDED for WebAssembly multi-threading. Native header support,
          excellent DX, and no workarounds needed. Best choice for production deployment.
        </recommendation>

        <sources>
          - https://vercel.com/kb/guide/fix-shared-array-buffer-not-defined-nextjs-react
          - https://vercel.com/guides/fix-shared-array-buffer-not-defined-nextjs-react
          - https://vercel.com/docs/functions/wasm
        </sources>
      </platform>

      <platform name="Netlify">
        <overview>
          Popular static hosting platform with strong JAMstack support. Excellent header
          configuration and build features.
        </overview>

        <headers_support>
          <native_support>EXCELLENT - Full header configuration support</native_support>
          <configuration_methods>
            <method name="netlify.toml">
              ```toml
              [[headers]]
                for = "/*"
                [headers.values]
                  Cross-Origin-Embedder-Policy = "credentialless"
                  Cross-Origin-Opener-Policy = "same-origin"
              ```
            </method>
            <method name="_headers file">
              Plain text file in public directory:
              ```
              /*
                Cross-Origin-Embedder-Policy: credentialless
                Cross-Origin-Opener-Policy: same-origin
              ```
            </method>
            <method name="Framework-specific">
              For Astro: Can use netlify.toml, _headers, or astro-static-headers plugin
            </method>
          </configuration_methods>
        </headers_support>

        <important_considerations>
          <breaking_changes>
            Enabling COOP/COEP headers can break other website aspects, particularly:
            - Firebase features
            - Third-party scripts without CORP headers
            - Embedded content from external sources

            Recommend using COEP: credentialless instead of require-corp for better compatibility.
          </breaking_changes>
        </important_considerations>

        <features>
          - Automatic HTTPS
          - Continuous deployment from git
          - Branch previews
          - Build plugins ecosystem
          - Forms handling
          - Functions (serverless)
          - Advanced caching control
          - Split testing
        </features>

        <free_tier>
          <limits>
            - 100 GB bandwidth per month
            - 300 build minutes per month
            - Unlimited sites
            - Commercial use allowed
          </limits>
        </free_tier>

        <pros>
          + Full header configuration (multiple methods)
          + Excellent build system
          + Advanced caching features
          + Great for JAMstack sites
          + Strong community and documentation
          + Build plugins for optimization
        </pros>

        <cons>
          - Build minutes limit on free tier
          - Headers can break third-party integrations
          - Slightly more complex configuration than Vercel
        </cons>

        <recommendation>
          HIGHLY RECOMMENDED. Equivalent to Vercel for WebAssembly use case with
          native header support. Choose based on preference or existing familiarity.
        </recommendation>

        <sources>
          - https://docs.netlify.com/manage/routing/headers/
          - https://answers.netlify.com/t/react-website-getting-sharedarraybuffer-error-due-to-coop-and-coep/41705
          - https://dev.to/cassidoo/three-ways-to-set-headers-with-netlify-and-astro-1iib
        </sources>
      </platform>

      <platform name="Cloudflare Pages">
        <overview>
          Modern static hosting on Cloudflare's global network. Fast performance with
          WebAssembly support, but has threading limitations.
        </overview>

        <headers_support>
          <native_support>GOOD - Supports custom headers via _headers file</native_support>
          <configuration_method>
            Create _headers file in static asset directory:
            ```
            /*
              Cross-Origin-Embedder-Policy: require-corp
              Cross-Origin-Opener-Policy: same-origin
            ```
            Parsed by Cloudflare Pages and applied to static asset responses.
          </configuration_method>
          <workaround_for_unsupported>
            If headers not supported directly, can use Cloudflare Worker to modify headers
          </workaround_for_unsupported>
        </headers_support>

        <webassembly_support>
          <static_pages>Full WebAssembly support for static content</static_pages>
          <pages_functions>
            WebAssembly supported in Pages Functions (compile Rust, Go, C to run in Cloudflare)
          </pages_functions>
          <threading_limitation>
            CRITICAL: Threading NOT possible in Workers - each Worker runs in single thread.
            Web Worker API NOT supported in Cloudflare Workers runtime.

            This may limit SharedArrayBuffer usefulness despite header support.
          </threading_limitation>
        </webassembly_support>

        <features>
          - Global CDN (Cloudflare network)
          - Automatic HTTPS
          - Git integration
          - Unlimited bandwidth (free tier!)
          - Pages Functions (edge computing)
          - Fast global performance
        </features>

        <free_tier>
          <limits>
            - UNLIMITED bandwidth
            - 500 builds per month
            - 100 custom domains
            - Unlimited sites
          </limits>
        </free_tier>

        <pros>
          + Unlimited bandwidth on free tier (unique advantage)
          + Headers configuration supported
          + Extremely fast global network
          + WebAssembly support for static content
          + Good documentation
        </pros>

        <cons>
          - Workers/Functions have NO threading support (critical for some use cases)
          - _headers file approach less flexible than Vercel/Netlify
          - Smaller community than Vercel/Netlify
          - May need Worker workaround for complex header scenarios
        </cons>

        <recommendation>
          RECOMMENDED WITH CAVEATS. Excellent for static WebAssembly content with
          unlimited bandwidth, but be aware that Cloudflare Workers don't support
          threading if you plan to use serverless functions. Fine for client-side
          multi-threaded WebAssembly in static pages.
        </recommendation>

        <sources>
          - https://developers.cloudflare.com/pages/configuration/headers/
          - https://community.cloudflare.com/t/how-could-i-make-the-html-support-sharedarraybuffer/581161
          - https://developers.cloudflare.com/workers/runtime-apis/webassembly/
          - https://blog.cloudflare.com/pages-functions-with-webassembly/
        </sources>
      </platform>

      <comparison_matrix>
        <criteria>
          <criterion name="Header Support">
            - Vercel: +++++ (native, vercel.json)
            - Netlify: +++++ (native, multiple methods)
            - Cloudflare Pages: ++++ (native, _headers file)
            - GitHub Pages: -- (service worker workaround only)
          </criterion>

          <criterion name="WebAssembly Multi-threading">
            - Vercel: +++++ (full support, no issues)
            - Netlify: +++++ (full support, no issues)
            - Cloudflare Pages: ++++ (static pages: yes, Workers: no threading)
            - GitHub Pages: +++ (works with service worker workaround)
          </criterion>

          <criterion name="Free Tier Bandwidth">
            - Cloudflare Pages: +++++ (unlimited!)
            - Vercel: ++++ (100 GB)
            - Netlify: ++++ (100 GB)
            - GitHub Pages: +++++ (unlimited)
          </criterion>

          <criterion name="Developer Experience">
            - Vercel: +++++ (excellent, preview deployments)
            - Netlify: +++++ (excellent, build plugins)
            - Cloudflare Pages: ++++ (good, fast)
            - GitHub Pages: +++ (simple but limited)
          </criterion>

          <criterion name="Build Features">
            - Netlify: +++++ (plugins, advanced caching)
            - Vercel: +++++ (automatic, framework-aware)
            - Cloudflare Pages: ++++ (good, git integration)
            - GitHub Pages: ++ (basic, no build optimization)
          </criterion>
        </criteria>

        <best_for>
          - Production WebAssembly site: Vercel or Netlify
          - Unlimited bandwidth needed: Cloudflare Pages
          - Simple open source project: GitHub Pages (with workaround)
          - Best overall: Vercel (ease) or Netlify (features)
        </best_for>
      </comparison_matrix>
    </finding>

    <!-- ======================== -->
    <!-- GIT SUBMODULE PATTERNS   -->
    <!-- ======================== -->

    <finding category="git_submodules" priority="high">
      <overview>
        Git submodules allow keeping one Git repository as a subdirectory of another.
        For a transpiler documentation site, submodules can manage the relationship
        between the main transpiler repository and the website repository.
      </overview>

      <architectural_approaches>
        <approach name="Website as Submodule">
          <structure>
            Main Repository: hupyy-cpp-to-c/
            ├── src/ (transpiler source)
            ├── docs/ (basic documentation)
            └── website/ (git submodule → separate repository)
                ├── package.json
                ├── src/
                └── public/
          </structure>

          <pros>
            + Website has independent version control
            + Can develop website without touching main repo
            + Website can be deployed independently
            + Different team can maintain website
            + Website repository stays clean and focused
          </pros>

          <cons>
            - Developers must remember to update submodule
            - CI/CD must handle submodule initialization
            - Extra step: git clone --recurse-submodules
          </cons>

          <best_for>
            Teams with separate documentation maintainers, or when website
            development cadence differs from transpiler development
          </best_for>
        </approach>

        <approach name="Website Contains Transpiler as Submodule">
          <structure>
            Website Repository: transpiler-website/
            ├── package.json
            ├── src/
            ├── public/
            └── transpiler/ (git submodule → main transpiler)
                ├── src/
                ├── include/
                └── build/
          </structure>

          <pros>
            + Website repository is self-contained
            + Can reference specific transpiler versions
            + Can build transpiler WASM as part of website build
            + Clear separation: website controls what version it uses
          </pros>

          <cons>
            - Must update submodule to get latest transpiler changes
            - Submodule update workflow required
            - CI must build transpiler WASM during website build
          </cons>

          <best_for>
            When website needs to build transpiler WASM from source,
            or when you want website to control which transpiler version it uses
          </best_for>
        </approach>

        <approach name="Monorepo (No Submodules)">
          <structure>
            Repository: hupyy-cpp-to-c/
            ├── transpiler/
            │   ├── src/
            │   └── include/
            └── website/
                ├── package.json
                ├── src/
                └── public/
          </structure>

          <pros>
            + Single repository, simpler for solo developer
            + No submodule complexity
            + Changes to transpiler and website in same commit
            + Easier to keep documentation in sync
            + Simpler CI/CD configuration
          </pros>

          <cons>
            - Repository size grows with both projects
            - Mixed concerns in single repository
            - Website deployments include transpiler history
          </cons>

          <best_for>
            Solo developers, when simplicity preferred over separation,
            or when documentation must stay in sync with code changes
          </best_for>
        </approach>

        <approach name="Artifacts-Only Approach">
          <structure>
            Website builds transpiler WASM from main repository during CI,
            stores artifacts (WASM files) in website repository or CDN.
            No submodules needed.
          </structure>

          <workflow>
            1. Transpiler CI builds WASM on release
            2. WASM artifacts published to GitHub Releases or CDN
            3. Website fetches WASM artifacts during build
            4. No direct repository dependency
          </workflow>

          <pros>
            + Cleanest separation
            + Website doesn't need transpiler source
            + Smaller website repository
            + Can use specific release versions
            + No submodule complexity
          </pros>

          <cons>
            - Requires artifact publishing infrastructure
            - Harder to test unreleased transpiler changes in website
            - Must version artifacts carefully
          </cons>

          <best_for>
            Production deployments where website should use stable releases,
            or when build artifacts are published to CDN/registry
          </best_for>
        </approach>
      </architectural_approaches>

      <best_practices>
        <practice name="Documentation">
          Always document submodules in README.md with setup instructions:
          ```bash
          # Clone with submodules
          git clone --recurse-submodules https://github.com/user/repo.git

          # Or initialize after clone
          git submodule update --init --recursive
          ```
        </practice>

        <practice name="Version Locking">
          Lock submodules to specific SHA, not floating branch references.
          Ensures all developers get same content. Update deliberately.
        </practice>

        <practice name="CI/CD Configuration">
          Ensure CI/CD runs submodule initialization:
          ```yaml
          - name: Checkout with submodules
            uses: actions/checkout@v3
            with:
              submodules: recursive
          ```
        </practice>

        <practice name="Avoid Nested Submodules">
          Submodules containing submodules become exponentially harder to manage.
          Keep architecture flat.
        </practice>

        <practice name="Team Communication">
          Team must understand submodule workflow:
          - When to update submodules
          - How to commit submodule updates
          - Testing before updating submodule reference
        </practice>

        <practice name="Keep .gitmodules in Sync">
          Run `git submodule update` after changes to ensure .gitmodules
          reflects working tree state.
        </practice>

        <sources>
          - https://git-scm.com/book/en/v2/Git-Tools-Submodules
          - https://gist.github.com/slavafomin/08670ec0c0e75b500edbaa5d43a5c93c
          - https://github.blog/open-source/git/working-with-submodules/
          - https://medium.com/@ifeanyiobiana/managing-git-submodules-effectively-375827bcef7c
        </sources>
      </best_practices>

      <recommendation>
        <choice>Monorepo (No Submodules) OR Artifacts-Only</choice>
        <rationale>
          For your solo developer scenario with hupyy-cpp-to-c:

          **Monorepo Approach** (Recommended for development):
          - Simpler workflow (you're solo)
          - Keep website and transpiler in one repo
          - Easier to keep docs in sync with code changes
          - No submodule complexity
          - Structure: hupyy-cpp-to-c/website/

          **Artifacts-Only** (Recommended for production):
          - Transpiler CI publishes WASM to GitHub Releases
          - Website fetches WASM artifacts during build
          - Clean separation
          - Website repository could be separate for deployment

          **NOT recommended**: Submodules add complexity without benefit for solo developer.
          Only consider if you want completely separate repositories and accept the workflow overhead.
        </rationale>
      </recommendation>
    </finding>

  </findings>

  <recommendations>

    <recommendation priority="critical" category="framework">
      <title>Static Site Generator: Astro</title>
      <choice>Astro</choice>
      <rationale>
        For a C++ to C transpiler documentation/demo website, Astro is the optimal choice:

        1. **Component Islands Architecture**: Allows mixing React components for code playground
           while keeping most of the site static for best performance

        2. **Framework Flexibility**: Can use CodeMirror 6 (React wrapper) for editor,
           custom React components for transpiler demo, while static content remains lightweight

        3. **Build Performance**: Vite-based, fast builds even as site grows

        4. **SEO**: Static HTML generation ensures search engines can index transpiler docs

        5. **WebAssembly Support**: Full WebAssembly module loading, no restrictions

        **Why NOT Docusaurus**: While excellent for pure documentation, Astro's flexibility
        better suits a site that's half documentation, half interactive playground.

        **Why NOT Next.js**: Static export header limitations are dealbreaker for WASM multi-threading.

        **Why NOT VitePress**: Vue-centric, smaller ecosystem for React-based code editors.
      </rationale>

      <implementation_steps>
        1. Create website/ directory in hupyy-cpp-to-c repository (monorepo approach)
        2. Initialize Astro project: npm create astro@latest
        3. Add React integration: npx astro add react
        4. Configure MDX support for documentation content
        5. Install CodeMirror 6 for code editor
        6. Create transpiler playground component
      </implementation_steps>
    </recommendation>

    <recommendation priority="critical" category="deployment">
      <title>Deployment Platform: Vercel</title>
      <choice>Vercel (Primary) or Netlify (Alternative)</choice>
      <rationale>
        **Vercel** is the top choice for deploying the transpiler website:

        1. **Native Header Support**: vercel.json provides clean COOP/COEP configuration
           without workarounds or service workers

        2. **Zero Configuration for Astro**: Vercel auto-detects Astro, builds correctly

        3. **Preview Deployments**: Every git push gets preview URL - excellent for testing
           WebAssembly features before merging

        4. **Performance**: Global CDN, automatic HTTPS, excellent speeds

        5. **Free Tier**: 100 GB bandwidth more than sufficient for documentation site

        **Netlify** is equally capable - choose based on preference. Both provide:
        - Native header support
        - Astro auto-detection
        - Preview deployments
        - Generous free tiers

        **NOT GitHub Pages**: Requires service worker workaround with poor UX (page reload)

        **NOT Cloudflare Pages**: While excellent (unlimited bandwidth!), Vercel/Netlify
        have better documentation and community support for Astro + WebAssembly use case
      </rationale>

      <implementation_steps>
        1. Create vercel.json in website/ directory with COOP/COEP headers
        2. Connect GitHub repository to Vercel
        3. Configure build command and output directory
        4. Set root directory to website/
        5. Deploy and verify crossOriginIsolated === true
      </implementation_steps>
    </recommendation>

    <recommendation priority="high" category="code_editor">
      <title>Code Editor: CodeMirror 6</title>
      <choice>CodeMirror 6</choice>
      <rationale>
        CodeMirror 6 is the clear winner for the transpiler playground:

        1. **Bundle Size**: 6-8x smaller than Monaco (300KB vs 2+ MB minimum)
           Critical for documentation site where users want fast page loads

        2. **Performance**: Lightweight, fast initial load, works great even on mobile

        3. **Sufficient Features**: C++ and C syntax highlighting available,
           don't need TypeScript IntelliSense or VS Code features

        4. **Industry Validation**: Sourcegraph and Replit both migrated FROM Monaco TO CodeMirror 6
           specifically citing performance and bundle size

        5. **Mobile Support**: Better mobile experience for users browsing docs on phones

        **Monaco** only makes sense if you need full VS Code feature parity,
        which is overkill for C++ to C transpiler demo.
      </rationale>

      <implementation_steps>
        1. Install CodeMirror 6: npm install @codemirror/state @codemirror/view
        2. Install C++ language support: npm install @codemirror/lang-cpp
        3. Create React wrapper component for CodeMirror
        4. Configure split pane: C++ input (left) | C output (right)
        5. Wire up transpiler WASM execution on input change
        6. Add syntax highlighting themes
      </implementation_steps>
    </recommendation>

    <recommendation priority="high" category="architecture">
      <title>Repository Structure: Monorepo</title>
      <choice>Monorepo (website/ directory in main repository)</choice>
      <rationale>
        For solo development of hupyy-cpp-to-c, monorepo is optimal:

        1. **Simplicity**: No submodule complexity, standard git workflow

        2. **Sync**: Documentation changes committed alongside transpiler changes

        3. **Single CI/CD**: One workflow builds transpiler WASM and deploys website

        4. **Testing**: Easy to test unreleased transpiler features in website

        5. **Solo Developer**: Submodules designed for team coordination - unnecessary overhead for solo work

        **Structure**:
        ```
        hupyy-cpp-to-c/
        ├── src/              (transpiler C++ source)
        ├── include/          (transpiler headers)
        ├── tests/            (transpiler tests)
        ├── docs/             (basic markdown docs)
        ├── website/          (Astro documentation/demo site)
        │   ├── src/
        │   ├── public/
        │   │   └── wasm/     (transpiler WASM artifacts)
        │   ├── astro.config.mjs
        │   └── package.json
        └── .github/
            └── workflows/
                └── deploy-website.yml
        ```

        **CI Workflow**:
        1. Build transpiler with Emscripten (pthread enabled)
        2. Copy WASM files to website/public/wasm/
        3. Build Astro site
        4. Deploy to Vercel

        **Alternative**: If repository grows too large, can extract website later
        using git filter-branch. Start simple, refactor if needed.
      </rationale>
    </recommendation>

    <recommendation priority="medium" category="features">
      <title>Website Feature Set</title>
      <features>
        <feature priority="critical">
          <name>Interactive Playground</name>
          <description>
            Split-pane editor with C++ input (left), C output (right).
            Real-time transpilation using WASM. Example code snippets.
          </description>
          <implementation>CodeMirror 6 + React + transpiler WASM module</implementation>
        </feature>

        <feature priority="critical">
          <name>Getting Started Guide</name>
          <description>
            Installation instructions, basic usage, first transpilation example.
            Should get users from zero to transpiling in 5 minutes.
          </description>
          <implementation>MDX pages in Astro</implementation>
        </feature>

        <feature priority="high">
          <name>Example Gallery</name>
          <description>
            Collection of C++ patterns and their C equivalents. Categories:
            - Classes to structs
            - Templates to macros
            - RAII to manual cleanup
            - Smart pointers to raw pointers
            - etc.
          </description>
          <implementation>MDX with embedded CodeMirror examples</implementation>
        </feature>

        <feature priority="high">
          <name>API Reference</name>
          <description>
            Documentation for command-line interface, configuration options,
            output formats, supported C++ features.
          </description>
          <implementation>Auto-generated from code + manual MDX pages</implementation>
        </feature>

        <feature priority="medium">
          <name>Architecture Documentation</name>
          <description>
            How the transpiler works internally. AST transformation pipeline,
            design decisions, contribution guide.
          </description>
          <implementation>MDX pages with diagrams (Mermaid)</implementation>
        </feature>

        <feature priority="low">
          <name>Blog</name>
          <description>
            Release announcements, technical deep-dives, use cases.
            Can be added later once core features complete.
          </description>
          <implementation>Astro content collections</implementation>
        </feature>
      </features>
    </recommendation>

    <recommendation priority="high" category="headers">
      <title>COOP/COEP Header Configuration</title>
      <recommended_values>
        <header>Cross-Origin-Opener-Policy: same-origin</header>
        <header>Cross-Origin-Embedder-Policy: credentialless</header>
      </recommended_values>
      <rationale>
        Use **credentialless** instead of **require-corp** for COEP:

        1. Better compatibility with third-party resources (fonts, analytics, CDNs)
        2. Less likely to break embedded content
        3. Achieves cross-origin isolation for SharedArrayBuffer
        4. Recommended by web.dev for new implementations

        **require-corp** would require ALL resources to have CORP headers,
        which can break Google Fonts, analytics scripts, etc.
      </rationale>
    </recommendation>

  </recommendations>

  <code_examples>

    <example name="Vercel Header Configuration">
      <file>website/vercel.json</file>
      <language>json</language>
      <code>
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
      </code>
      <description>
        Complete vercel.json configuration for WebAssembly multi-threading support.
        Apply headers to all routes using /:path* pattern.
      </description>
    </example>

    <example name="Netlify Header Configuration">
      <file>website/netlify.toml</file>
      <language>toml</language>
      <code>
[[headers]]
  for = "/*"
  [headers.values]
    Cross-Origin-Embedder-Policy = "credentialless"
    Cross-Origin-Opener-Policy = "same-origin"
      </code>
      <description>
        Alternative: netlify.toml configuration for same header setup on Netlify.
      </description>
    </example>

    <example name="Netlify _headers File">
      <file>website/public/_headers</file>
      <language>text</language>
      <code>
/*
  Cross-Origin-Embedder-Policy: credentialless
  Cross-Origin-Opener-Policy: same-origin
      </code>
      <description>
        Alternative: _headers file approach for Netlify (simpler, placed in public directory).
      </description>
    </example>

    <example name="Emscripten Compilation for Multi-threading">
      <file>CMakeLists.txt or build script</file>
      <language>bash</language>
      <code>
# Compile transpiler to WebAssembly with pthread support
emcc src/*.cpp \
  -o website/public/wasm/transpiler.js \
  -pthread \
  -sPTHREAD_POOL_SIZE=navigator.hardwareConcurrency \
  -sPROXY_TO_PTHREAD \
  -sMALLOC=mimalloc \
  -sEXPORTED_FUNCTIONS='["_transpile","_malloc","_free"]' \
  -sEXPORTED_RUNTIME_METHODS='["ccall","cwrap"]' \
  -O3 \
  -s WASM=1
      </code>
      <description>
        Emscripten compilation command with all recommended flags for multi-threaded
        WebAssembly. Outputs to website/public/wasm/ for Astro to serve.
      </description>
    </example>

    <example name="Verify Cross-Origin Isolation">
      <file>website/src/components/Playground.jsx</file>
      <language>javascript</language>
      <code>
// Check if cross-origin isolation is working
useEffect(() => {
  if (typeof crossOriginIsolated !== 'undefined') {
    if (crossOriginIsolated) {
      console.log('✓ Cross-origin isolation enabled - SharedArrayBuffer available');
      console.log('✓ Multi-threaded WebAssembly supported');
    } else {
      console.error('✗ Cross-origin isolation NOT enabled');
      console.error('✗ Check COOP/COEP headers in deployment configuration');
    }
  } else {
    console.warn('⚠ crossOriginIsolated not supported in this browser');
  }

  // Verify SharedArrayBuffer is available
  try {
    const buffer = new SharedArrayBuffer(16);
    console.log('✓ SharedArrayBuffer constructor available');
  } catch (e) {
    console.error('✗ SharedArrayBuffer not available:', e.message);
  }
}, []);
      </code>
      <description>
        Runtime verification that COOP/COEP headers are working correctly.
        Add this to your playground component during development.
      </description>
    </example>

    <example name="CodeMirror 6 Basic Setup">
      <file>website/src/components/CodeEditor.jsx</file>
      <language>javascript</language>
      <code>
import { useEffect, useRef, useState } from 'react';
import { EditorView, basicSetup } from 'codemirror';
import { cpp } from '@codemirror/lang-cpp';
import { oneDark } from '@codemirror/theme-one-dark';

export function CodeEditor({ initialValue, onChange, readOnly = false }) {
  const editorRef = useRef(null);
  const viewRef = useRef(null);

  useEffect(() => {
    if (!editorRef.current) return;

    const view = new EditorView({
      doc: initialValue,
      extensions: [
        basicSetup,
        cpp(),
        oneDark,
        EditorView.updateListener.of((update) => {
          if (update.docChanged && onChange) {
            onChange(update.state.doc.toString());
          }
        }),
        EditorView.editable.of(!readOnly),
      ],
      parent: editorRef.current,
    });

    viewRef.current = view;

    return () => {
      view.destroy();
    };
  }, []);

  return <div ref={editorRef} className="code-editor" />;
}
      </code>
      <description>
        Basic CodeMirror 6 React component with C++ syntax highlighting.
        Lightweight (300KB) and performant.
      </description>
    </example>

    <example name="Astro Config for React Integration">
      <file>website/astro.config.mjs</file>
      <language>javascript</language>
      <code>
import { defineConfig } from 'astro/config';
import react from '@astrojs/react';
import mdx from '@astrojs/mdx';

export default defineConfig({
  integrations: [
    react(),  // Enable React for interactive components
    mdx(),    // Enable MDX for documentation with components
  ],
  output: 'static',  // Static site generation
  build: {
    inlineStylesheets: 'auto',
  },
  vite: {
    build: {
      rollupOptions: {
        output: {
          manualChunks: {
            // Separate CodeMirror into its own chunk for better caching
            'codemirror': ['@codemirror/state', '@codemirror/view', '@codemirror/lang-cpp'],
          },
        },
      },
    },
  },
});
      </code>
      <description>
        Astro configuration with React and MDX support for transpiler website.
        Includes chunk optimization for CodeMirror.
      </description>
    </example>

    <example name="GitHub Actions Workflow">
      <file>.github/workflows/deploy-website.yml</file>
      <language>yaml</language>
      <code>
name: Deploy Website

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

jobs:
  build-and-deploy:
    runs-on: ubuntu-latest

    steps:
      - name: Checkout repository
        uses: actions/checkout@v3

      - name: Setup Emscripten
        uses: mymindstorm/setup-emsdk@v12
        with:
          version: 'latest'

      - name: Build transpiler WASM
        run: |
          mkdir -p website/public/wasm
          emcc src/*.cpp -o website/public/wasm/transpiler.js \
            -pthread \
            -sPTHREAD_POOL_SIZE=navigator.hardwareConcurrency \
            -sPROXY_TO_PTHREAD \
            -sMALLOC=mimalloc \
            -O3 -s WASM=1

      - name: Setup Node.js
        uses: actions/setup-node@v3
        with:
          node-version: '18'
          cache: 'npm'
          cache-dependency-path: website/package-lock.json

      - name: Install dependencies
        working-directory: website
        run: npm ci

      - name: Build Astro site
        working-directory: website
        run: npm run build

      - name: Deploy to Vercel
        uses: amondnet/vercel-action@v20
        with:
          vercel-token: ${{ secrets.VERCEL_TOKEN }}
          vercel-org-id: ${{ secrets.VERCEL_ORG_ID }}
          vercel-project-id: ${{ secrets.VERCEL_PROJECT_ID }}
          working-directory: website
          vercel-args: '--prod'
      </code>
      <description>
        Complete GitHub Actions workflow for building transpiler WASM and deploying
        website to Vercel. Builds on every push to main/develop.
      </description>
    </example>

  </code_examples>

  <metadata>
    <research_date>2025-12-19</research_date>
    <researcher>Claude Sonnet 4.5</researcher>

    <confidence_levels>
      <area name="Framework Comparison">HIGH - Comprehensive official docs and recent comparisons consulted</area>
      <area name="WebAssembly Multi-threading">VERY HIGH - Official Emscripten, MDN, and web.dev sources</area>
      <area name="Code Editor Comparison">HIGH - Real-world migration case studies (Sourcegraph, Replit)</area>
      <area name="Deployment Platforms">VERY HIGH - Official documentation and recent 2025 articles</area>
      <area name="Git Submodules">HIGH - Official Git documentation and best practices guides</area>
    </confidence_levels>

    <sources_consulted>
      <category name="Official Documentation">
        - Astro documentation (docs.astro.build)
        - Next.js documentation (nextjs.org/docs)
        - Docusaurus documentation (docusaurus.io/docs)
        - VitePress documentation (vitepress.dev)
        - Emscripten pthreads documentation (emscripten.org)
        - MDN Web Docs (SharedArrayBuffer, COOP/COEP headers)
        - Vercel documentation (vercel.com/docs)
        - Netlify documentation (docs.netlify.com)
        - Cloudflare Pages documentation (developers.cloudflare.com)
        - Git submodules documentation (git-scm.com)
      </category>

      <category name="Technical Articles (2025)">
        - "Setting COOP/COEP headers on static hosting" (blog.tomayac.com, March 2025)
        - "Static site generators for 2025" (CloudCannon, Kinsta, GrayGrids)
        - "React-based Static Site Generators in 2025" (Crystallize)
        - Various 2025 framework comparison articles
      </category>

      <category name="Case Studies">
        - Sourcegraph: Migrating Monaco → CodeMirror 6
        - Replit: Betting on CodeMirror (detailed migration rationale)
        - Multiple WebAssembly multi-threading implementation examples
      </category>

      <category name="Community Resources">
        - GitHub community discussion on COOP/COEP support (#13309)
        - Stack Overflow and dev.to articles on WebAssembly headers
        - npm package comparisons (codemirror vs monaco-editor)
      </category>
    </sources_consulted>

    <verified_claims>
      <claim>COOP/COEP headers required for SharedArrayBuffer - VERIFIED via MDN, web.dev</claim>
      <claim>Next.js headers() not working for static exports - VERIFIED via Next.js docs</claim>
      <claim>GitHub Pages no native header support - VERIFIED via community discussion and workarounds</claim>
      <claim>CodeMirror 6-8x smaller than Monaco - VERIFIED via Replit case study and npm-compare</claim>
      <claim>Vercel/Netlify support custom headers - VERIFIED via official documentation</claim>
      <claim>Cloudflare Workers no threading support - VERIFIED via Cloudflare docs</claim>
      <claim>Browser support for SharedArrayBuffer since Dec 2021 - VERIFIED via MDN</claim>
    </verified_claims>

    <assumptions>
      <assumption>Solo developer scenario (affects git submodule recommendations)</assumption>
      <assumption>Website will be primarily documentation + playground (affects framework choice)</assumption>
      <assumption>Multi-threading is essential requirement (affects all deployment recommendations)</assumption>
      <assumption>Free tier deployment acceptable (all platforms have generous free tiers)</assumption>
      <assumption>C++ to C transpiler already has Emscripten build capability</assumption>
    </assumptions>

    <open_questions>
      <question>
        What is the target audience technical level? Affects documentation depth and example complexity.
      </question>
      <question>
        Will website need versioning for different transpiler releases? If yes, Docusaurus versioning
        feature might swing decision toward it.
      </question>
      <question>
        How large will transpiler WASM files be? Affects decision on monorepo vs artifacts-only approach.
        Large WASM files (10+ MB) might favor artifacts-only to keep repository size manageable.
      </question>
      <question>
        Are there specific transpiler features that require multi-threading, or is it future-proofing?
        If single-threaded WASM sufficient short-term, could simplify initial deployment.
      </question>
    </open_questions>

    <dependencies>
      <dependency type="browser">Modern browsers with SharedArrayBuffer support (Chrome, Firefox, Safari, Edge 2021+)</dependency>
      <dependency type="build">Emscripten with pthread support</dependency>
      <dependency type="build">Node.js 18+ for Astro</dependency>
      <dependency type="deployment">Vercel or Netlify account (free tier)</dependency>
      <dependency type="deployment">GitHub repository for CI/CD integration</dependency>
    </dependencies>

    <quality_report>
      <completeness>
        All major research areas covered:
        ✓ Static site generators (4 frameworks analyzed)
        ✓ WebAssembly multi-threading requirements (headers, compilation, browser support)
        ✓ Code editors (Monaco vs CodeMirror 6 with real-world data)
        ✓ Deployment platforms (4 platforms with detailed comparison)
        ✓ Git submodule patterns (4 approaches analyzed)
        ✓ Code examples for all critical configurations
      </completeness>

      <source_quality>
        - Primary sources: Official documentation for all frameworks and platforms
        - Recent sources: 2025 articles preferred, 2024 acceptable for stable topics
        - Case studies: Real-world migrations (Sourcegraph, Replit) provide validation
        - Community input: GitHub discussions show real-world pain points
      </source_quality>

      <claim_verification>
        - Critical claims (header support, browser compatibility) verified with official sources
        - Negative claims ("X doesn't support Y") double-checked with docs and community
        - Performance claims backed by case studies with actual numbers
        - All recommendations have cited rationale
      </claim_verification>

      <blind_spots_addressed>
        ✓ Checked for alternative frameworks (Hugo, Eleventy) - excluded due to JavaScript/TypeScript requirement
        ✓ Verified header configuration for ALL recommended platforms
        ✓ Considered both development and production deployment scenarios
        ✓ Addressed solo developer context (affects submodule recommendations)
        ✓ Checked for recent 2025 updates to WebAssembly ecosystem
      </blind_spots_addressed>
    </quality_report>

  </metadata>
</research>

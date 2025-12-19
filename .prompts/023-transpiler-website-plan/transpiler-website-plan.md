# Transpiler Website Implementation Plan

**Created**: 2025-12-19
**Purpose**: Phased implementation roadmap for C++ to C transpiler documentation website with WebAssembly-based interactive demo
**Framework**: Astro (monorepo architecture)
**Deployment**: Vercel
**Target Completion**: 4-5 weeks

---

## Summary

This plan defines a 5-phase implementation roadmap for creating a modern, performant documentation and demonstration website for the C++ to C transpiler. The site will combine static documentation with an interactive WebAssembly-powered code playground, allowing users to transpile C++ code directly in their browser.

**Key Architectural Decisions**:
- **Framework**: Astro with React integration for component islands architecture
- **Repository**: Monorepo approach (website/ directory in main hupyy-cpp-to-c repository)
- **Code Editor**: CodeMirror 6 (6-8x smaller than Monaco, industry-validated)
- **Deployment**: Vercel with native COOP/COEP header support for WebAssembly multi-threading
- **Headers**: COEP: credentialless + COOP: same-origin for third-party compatibility

**Success Metrics**:
- Page load time: <3 seconds to interactive
- Lighthouse score: 90+ on all metrics
- WebAssembly playground functional with real-time transpilation
- All 5 real-world examples showcased with working demos
- Mobile-responsive design
- SEO-optimized static content

---

## Architecture

### Technology Stack

| Layer | Technology | Rationale |
|-------|-----------|-----------|
| **Framework** | Astro 4.x | Component islands, excellent performance, flexible |
| **UI Components** | React 18 | CodeMirror integration, interactive playground |
| **Code Editor** | CodeMirror 6 | 300KB bundle vs 2MB+ Monaco, better performance |
| **Styling** | Tailwind CSS | Utility-first, fast development, small bundle |
| **Build Tool** | Vite (via Astro) | Fast builds, excellent tree-shaking |
| **Deployment** | Vercel | Native COOP/COEP headers, zero config, preview deployments |
| **WebAssembly** | Emscripten | Multi-threading with pthread support |
| **CI/CD** | GitHub Actions | Integrated with existing pipeline |

### Directory Structure (Monorepo)

```
hupyy-cpp-to-c/
├── src/                          # Transpiler C++ source
├── include/                      # Transpiler headers
├── tests/                        # Transpiler tests
├── docs/                         # Basic markdown docs (reference)
├── website/                      # NEW: Astro documentation site
│   ├── public/
│   │   ├── wasm/                # Transpiler WASM artifacts
│   │   │   ├── transpiler.js
│   │   │   ├── transpiler.wasm
│   │   │   └── transpiler.worker.js
│   │   ├── examples/            # Example code snippets
│   │   └── assets/              # Images, fonts, etc.
│   ├── src/
│   │   ├── components/
│   │   │   ├── CodePlayground.tsx    # Main interactive demo
│   │   │   ├── CodeEditor.tsx        # CodeMirror wrapper
│   │   │   ├── ExampleGallery.tsx    # Real-world examples
│   │   │   ├── Header.tsx
│   │   │   ├── Footer.tsx
│   │   │   └── Navigation.tsx
│   │   ├── layouts/
│   │   │   ├── MainLayout.astro
│   │   │   ├── DocsLayout.astro
│   │   │   └── PlaygroundLayout.astro
│   │   ├── pages/
│   │   │   ├── index.astro           # Landing page
│   │   │   ├── playground.astro      # Interactive demo
│   │   │   ├── docs/                 # Documentation pages
│   │   │   │   ├── getting-started.mdx
│   │   │   │   ├── installation.mdx
│   │   │   │   ├── core-features.mdx
│   │   │   │   └── api-reference.mdx
│   │   │   └── examples/             # Example gallery
│   │   │       ├── index.astro
│   │   │       ├── json-parser.mdx
│   │   │       ├── logger.mdx
│   │   │       ├── test-framework.mdx
│   │   │       ├── string-formatter.mdx
│   │   │       └── resource-manager.mdx
│   │   ├── utils/
│   │   │   ├── wasm-loader.ts        # WebAssembly module loader
│   │   │   └── transpiler-api.ts     # Transpiler JS interface
│   │   └── styles/
│   │       └── global.css
│   ├── astro.config.mjs
│   ├── tailwind.config.cjs
│   ├── tsconfig.json
│   ├── package.json
│   ├── vercel.json                   # COOP/COEP headers configuration
│   └── README.md
├── .github/
│   └── workflows/
│       ├── ci.yml                    # Existing CI
│       └── deploy-website.yml        # NEW: Website deployment
└── CMakeLists.txt                    # Transpiler build
```

### WebAssembly Integration Architecture

```
┌─────────────────────────────────────────────────┐
│           User's Browser                        │
│                                                 │
│  ┌───────────────────────────────────────────┐ │
│  │  Astro Page (Static HTML)                 │ │
│  │  - Documentation content                  │ │
│  │  - Navigation, layout                     │ │
│  └───────────────────────────────────────────┘ │
│                    ↓                            │
│  ┌───────────────────────────────────────────┐ │
│  │  React Component (Hydrated Island)        │ │
│  │  - CodePlayground.tsx                     │ │
│  │  - CodeEditor.tsx (CodeMirror 6)          │ │
│  └───────────────────────────────────────────┘ │
│                    ↓                            │
│  ┌───────────────────────────────────────────┐ │
│  │  WebAssembly Module Loader                │ │
│  │  - Loads transpiler.wasm                  │ │
│  │  - Creates pthread worker pool            │ │
│  │  - Verifies crossOriginIsolated           │ │
│  └───────────────────────────────────────────┘ │
│                    ↓                            │
│  ┌───────────────────────────────────────────┐ │
│  │  Transpiler WASM (Multi-threaded)         │ │
│  │  - Main thread: UI responsive             │ │
│  │  - Worker threads: Transpilation          │ │
│  │  - SharedArrayBuffer for threading        │ │
│  └───────────────────────────────────────────┘ │
│                                                 │
└─────────────────────────────────────────────────┘
                    ↑
                    │ HTTP Headers
                    │ COOP: same-origin
                    │ COEP: credentialless
                    │
┌─────────────────────────────────────────────────┐
│              Vercel CDN                         │
│  - Static assets (HTML, CSS, JS)               │
│  - WASM files                                   │
│  - Header configuration from vercel.json       │
└─────────────────────────────────────────────────┘
                    ↑
                    │ Git Push
                    │
┌─────────────────────────────────────────────────┐
│          GitHub Actions CI/CD                   │
│  1. Build transpiler WASM (Emscripten)          │
│  2. Copy WASM to website/public/wasm/           │
│  3. Build Astro site (npm run build)            │
│  4. Deploy to Vercel                            │
└─────────────────────────────────────────────────┘
```

### Deployment Workflow

```
Developer Push (develop/main)
    ↓
GitHub Actions Triggered
    ↓
┌─────────────────────────────────────┐
│ Job 1: Build Transpiler WASM       │
│  - Setup Emscripten                 │
│  - Compile with -pthread flags      │
│  - Output: transpiler.js/.wasm      │
└─────────────────────────────────────┘
    ↓
┌─────────────────────────────────────┐
│ Job 2: Build Astro Website         │
│  - Install Node dependencies        │
│  - Copy WASM artifacts to public/   │
│  - Run Astro build                  │
│  - Output: dist/ directory          │
└─────────────────────────────────────┘
    ↓
┌─────────────────────────────────────┐
│ Job 3: Deploy to Vercel             │
│  - Upload dist/ to Vercel           │
│  - Apply vercel.json config         │
│  - Set COOP/COEP headers            │
│  - Generate preview URL             │
└─────────────────────────────────────┘
    ↓
Production Website Live
  - https://cpptoc.dev (or similar)
  - Preview: https://cpptoc-<hash>.vercel.app
```

---

## Phase 1: Foundation & Setup

**Duration**: 3-4 days
**Goal**: Establish Astro project structure, basic layout, and Vercel deployment pipeline

### Tasks

#### 1.1 Initialize Astro Project in Monorepo
- [ ] Create `website/` directory in hupyy-cpp-to-c root
- [ ] Run `npm create astro@latest` in website/
- [ ] Select TypeScript (strict), sample files (minimal)
- [ ] Add React integration: `npx astro add react`
- [ ] Add Tailwind CSS: `npx astro add tailwind`
- [ ] Initialize git tracking for website/ (already in monorepo)

#### 1.2 Configure Build Tools
- [ ] Set up `website/tsconfig.json` with strict TypeScript
- [ ] Configure `website/tailwind.config.cjs` with custom theme
- [ ] Update `website/astro.config.mjs` for static output
- [ ] Add code splitting for CodeMirror in Vite config
- [ ] Set up ESLint and Prettier for consistent formatting

#### 1.3 Create Basic Layout Structure
- [ ] Implement `src/layouts/MainLayout.astro` (header, footer, navigation)
- [ ] Create responsive navigation component
- [ ] Design header with logo, navigation links
- [ ] Design footer with links, GitHub, license info
- [ ] Add mobile menu toggle functionality

#### 1.4 Set Up Vercel Deployment
- [ ] Create `website/vercel.json` with COOP/COEP headers
  ```json
  {
    "headers": [
      {
        "source": "/:path*",
        "headers": [
          { "key": "Cross-Origin-Opener-Policy", "value": "same-origin" },
          { "key": "Cross-Origin-Embedder-Policy", "value": "credentialless" }
        ]
      }
    ]
  }
  ```
- [ ] Connect GitHub repository to Vercel account
- [ ] Configure Vercel project settings:
  - Framework Preset: Astro
  - Root Directory: website/
  - Build Command: npm run build
  - Output Directory: dist
- [ ] Test deployment with placeholder index page
- [ ] Verify headers with browser DevTools (crossOriginIsolated === true)

#### 1.5 Create Landing Page
- [ ] Design hero section with transpiler tagline
- [ ] Add feature highlights (3-4 key features)
- [ ] Include "Try it Now" CTA button (links to playground)
- [ ] Add "Get Started" section with quick links
- [ ] Implement responsive design (mobile-first)

### Deliverables

- ✅ Astro project initialized in website/ directory
- ✅ Vercel deployment pipeline functional with correct headers
- ✅ Basic landing page accessible at production URL
- ✅ Responsive layout working on mobile/tablet/desktop
- ✅ crossOriginIsolated verification passing in browser console

### Dependencies

- None (foundational phase)

### Execution Notes

**Header Verification**:
```javascript
// Add to landing page for testing
if (typeof window !== 'undefined') {
  console.log('Cross-origin isolated:', crossOriginIsolated);
  console.log('SharedArrayBuffer available:', typeof SharedArrayBuffer !== 'undefined');
}
```

**Vercel Configuration Best Practice**:
- Use `credentialless` instead of `require-corp` for COEP to avoid breaking third-party resources
- Test with Google Fonts, analytics scripts to verify compatibility
- Add fallback for browsers without SharedArrayBuffer support (display warning)

---

## Phase 2: WebAssembly Integration

**Duration**: 4-5 days
**Goal**: Compile transpiler to WebAssembly, create WASM loading infrastructure, verify threading

### Tasks

#### 2.1 Set Up Emscripten Build for Transpiler
- [ ] Create `scripts/build-wasm.sh` in repository root
- [ ] Write Emscripten compilation command with flags:
  - `-pthread` (enable pthreads)
  - `-sPTHREAD_POOL_SIZE=navigator.hardwareConcurrency`
  - `-sPROXY_TO_PTHREAD` (keep main thread responsive)
  - `-sMALLOC=mimalloc` (better multi-threaded allocator)
  - `-O3` (optimization)
  - `-sEXPORTED_FUNCTIONS='["_transpile","_malloc","_free"]'`
  - `-sEXPORTED_RUNTIME_METHODS='["ccall","cwrap"]'`
- [ ] Output to `website/public/wasm/transpiler.{js,wasm,worker.js}`
- [ ] Test compilation locally (verify .js, .wasm, .worker.js created)

#### 2.2 Create WebAssembly Loader Module
- [ ] Implement `src/utils/wasm-loader.ts`:
  - Async WASM module initialization
  - Worker pool creation
  - Error handling for unsupported browsers
  - Verification of crossOriginIsolated
  - Loading state management
- [ ] Add TypeScript type definitions for WASM module
- [ ] Implement retry logic for WASM loading failures
- [ ] Add timeout handling for initialization

#### 2.3 Create Transpiler JavaScript API
- [ ] Implement `src/utils/transpiler-api.ts`:
  - `transpile(cppCode: string): Promise<string>` function
  - Error handling and parsing
  - Memory management (malloc/free wrappers)
  - Progress callbacks for large files
  - Cancellation support
- [ ] Add input validation (check for empty code, size limits)
- [ ] Implement output sanitization
- [ ] Add performance metrics (transpilation time)

#### 2.4 Create Verification/Testing Page
- [ ] Create `src/pages/wasm-test.astro` for WASM verification
- [ ] Add diagnostic information display:
  - crossOriginIsolated status
  - SharedArrayBuffer availability
  - WASM module load status
  - Worker thread count
  - Browser compatibility info
- [ ] Add simple transpilation test (hardcoded C++ snippet)
- [ ] Display transpilation result and timing
- [ ] Show console logs for debugging

#### 2.5 Update GitHub Actions for WASM Build
- [ ] Create `.github/workflows/deploy-website.yml`
- [ ] Add Emscripten setup step (mymindstorm/setup-emsdk@v12)
- [ ] Add WASM build step (run build-wasm.sh)
- [ ] Verify WASM artifacts are created before Astro build
- [ ] Add artifact upload for debugging (optional)
- [ ] Configure deployment to Vercel with secrets

### Deliverables

- ✅ Transpiler compiled to WebAssembly with pthread support
- ✅ WASM loading infrastructure functional
- ✅ Verification page showing successful WASM initialization
- ✅ GitHub Actions automatically builds and deploys WASM
- ✅ Multi-threading verified (worker threads created)

### Dependencies

- Phase 1 (Astro setup and Vercel deployment)
- Emscripten toolchain installed in CI environment

### Execution Notes

**Emscripten Build Command Example**:
```bash
#!/bin/bash
# scripts/build-wasm.sh

set -e

echo "Building transpiler for WebAssembly..."

mkdir -p website/public/wasm

emcc src/*.cpp \
  -o website/public/wasm/transpiler.js \
  -I include/ \
  -pthread \
  -sPTHREAD_POOL_SIZE=navigator.hardwareConcurrency \
  -sPROXY_TO_PTHREAD \
  -sMALLOC=mimalloc \
  -sEXPORTED_FUNCTIONS='["_transpile","_malloc","_free"]' \
  -sEXPORTED_RUNTIME_METHODS='["ccall","cwrap"]' \
  -O3 \
  -s WASM=1 \
  -s ALLOW_MEMORY_GROWTH=1 \
  -s MODULARIZE=1 \
  -s EXPORT_NAME='createTranspilerModule'

echo "WASM build complete!"
echo "Files created:"
ls -lh website/public/wasm/
```

**Browser Compatibility Check**:
```typescript
// src/utils/wasm-loader.ts
export function checkBrowserCompatibility(): { supported: boolean; message: string } {
  if (typeof SharedArrayBuffer === 'undefined') {
    return {
      supported: false,
      message: 'SharedArrayBuffer not available. Please use a modern browser (Chrome 92+, Firefox 90+, Safari 15.2+)'
    };
  }

  if (typeof crossOriginIsolated === 'undefined' || !crossOriginIsolated) {
    return {
      supported: false,
      message: 'Cross-origin isolation not enabled. Please check server headers.'
    };
  }

  return { supported: true, message: 'Browser fully compatible!' };
}
```

---

## Phase 3: Interactive Code Playground

**Duration**: 5-6 days
**Goal**: Build fully-functional code playground with CodeMirror 6 and real-time transpilation

### Tasks

#### 3.1 Install and Configure CodeMirror 6
- [ ] Install packages:
  - `@codemirror/state`
  - `@codemirror/view`
  - `@codemirror/lang-cpp`
  - `@codemirror/theme-one-dark`
  - `@codemirror/basic-setup`
- [ ] Create `src/components/CodeEditor.tsx` React component
- [ ] Implement editor initialization with C++ language support
- [ ] Add syntax highlighting theme (One Dark)
- [ ] Implement onChange callback for code updates
- [ ] Add line numbers, code folding, search
- [ ] Configure read-only mode for output editor

#### 3.2 Build Split-Pane Code Playground
- [ ] Create `src/components/CodePlayground.tsx`
- [ ] Implement split layout: C++ input (left) | C output (right)
- [ ] Add resizable pane divider (optional, or fixed 50/50)
- [ ] Integrate two CodeEditor instances (input, output)
- [ ] Add "Transpile" button with loading state
- [ ] Display transpilation errors prominently
- [ ] Add example code selector dropdown
- [ ] Show transpilation time metric

#### 3.3 Implement Transpilation Logic
- [ ] Connect "Transpile" button to transpiler-api.ts
- [ ] Handle async transpilation with loading spinner
- [ ] Update output editor with transpiled C code
- [ ] Display error messages in output pane (if transpilation fails)
- [ ] Add syntax highlighting to output (C syntax)
- [ ] Implement debouncing for auto-transpile on typing (optional)
- [ ] Add "Copy to Clipboard" button for output

#### 3.4 Add Example Code Snippets
- [ ] Create `public/examples/simple-class.cpp`
- [ ] Create `public/examples/inheritance.cpp`
- [ ] Create `public/examples/templates.cpp`
- [ ] Create `public/examples/smart-pointers.cpp`
- [ ] Create `public/examples/exceptions.cpp`
- [ ] Implement example loader in CodePlayground
- [ ] Add dropdown menu to select examples
- [ ] Preload default example on page load

#### 3.5 Create Playground Page
- [ ] Create `src/pages/playground.astro`
- [ ] Use PlaygroundLayout with minimal navigation
- [ ] Embed CodePlayground component (client:load directive)
- [ ] Add page title and brief instructions
- [ ] Add link to documentation
- [ ] Optimize for full-screen experience
- [ ] Test on mobile (responsive layout)

### Deliverables

- ✅ Fully functional code playground with split-pane editor
- ✅ Real-time transpilation of C++ to C working
- ✅ 5+ example code snippets available
- ✅ Error handling and user feedback implemented
- ✅ Responsive design (works on tablet/desktop)

### Dependencies

- Phase 2 (WebAssembly integration and transpiler API)

### Execution Notes

**CodeMirror 6 Component Structure**:
```tsx
// src/components/CodeEditor.tsx
import { useEffect, useRef } from 'react';
import { EditorView, basicSetup } from 'codemirror';
import { cpp } from '@codemirror/lang-cpp';
import { oneDark } from '@codemirror/theme-one-dark';

interface CodeEditorProps {
  initialValue: string;
  onChange?: (value: string) => void;
  readOnly?: boolean;
  language?: 'cpp' | 'c';
}

export function CodeEditor({ initialValue, onChange, readOnly = false, language = 'cpp' }: CodeEditorProps) {
  const editorRef = useRef<HTMLDivElement>(null);
  const viewRef = useRef<EditorView | null>(null);

  useEffect(() => {
    if (!editorRef.current) return;

    const view = new EditorView({
      doc: initialValue,
      extensions: [
        basicSetup,
        language === 'cpp' ? cpp() : cpp(), // Use cpp() for both (C is subset)
        oneDark,
        EditorView.updateListener.of((update) => {
          if (update.docChanged && onChange && !readOnly) {
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

  // Update content programmatically
  useEffect(() => {
    if (viewRef.current && readOnly) {
      viewRef.current.dispatch({
        changes: { from: 0, to: viewRef.current.state.doc.length, insert: initialValue }
      });
    }
  }, [initialValue, readOnly]);

  return <div ref={editorRef} className="h-full border border-gray-700 rounded" />;
}
```

**Performance Optimization**:
- Use `client:load` directive for CodePlayground (not `client:idle`) to ensure immediate interactivity
- Debounce transpilation if implementing auto-transpile (500ms delay)
- Consider Web Worker for large file transpilation to keep UI responsive
- Implement virtual scrolling for very large output files (CodeMirror handles this)

---

## Phase 4: Documentation Content Migration

**Duration**: 4-5 days
**Goal**: Migrate existing documentation to Astro/MDX format, create comprehensive user guide

### Tasks

#### 4.1 Set Up Documentation Structure
- [ ] Create `src/pages/docs/` directory
- [ ] Implement `src/layouts/DocsLayout.astro` with sidebar navigation
- [ ] Create sidebar component with TOC (Table of Contents)
- [ ] Add breadcrumb navigation
- [ ] Implement prev/next page links
- [ ] Add "Edit on GitHub" link for each page

#### 4.2 Migrate Getting Started Guide
- [ ] Convert `docs/user-guide/01-getting-started.md` to MDX
- [ ] Enhance with interactive examples (embed CodePlayground snippets)
- [ ] Add installation instructions with copy buttons
- [ ] Include verification steps
- [ ] Add screenshots/diagrams (create if needed)
- [ ] Test all code examples

#### 4.3 Create API Reference Pages
- [ ] Convert `docs/api-reference/cli-options.md` to MDX
- [ ] Document all CLI flags with examples
- [ ] Add configuration file reference
- [ ] Document WASM API for web usage
- [ ] Include output format specifications
- [ ] Add troubleshooting section

#### 4.4 Document Core Features
- [ ] Create feature documentation pages:
  - Classes and Inheritance
  - Templates and Generics
  - RAII and Resource Management
  - Exceptions (from docs/features/exceptions.md)
  - RTTI (from docs/features/rtti.md)
  - Coroutines (from docs/features/coroutines.md)
  - Virtual Inheritance (from docs/features/virtual-inheritance.md)
- [ ] Add code examples for each feature
- [ ] Include before/after transpilation examples
- [ ] Link to playground with pre-loaded examples

#### 4.5 Create FAQ and Troubleshooting Pages
- [ ] Convert `docs/FAQ.md` to MDX
- [ ] Add troubleshooting guide for common issues
- [ ] Include browser compatibility information
- [ ] Add performance optimization tips
- [ ] Document known limitations
- [ ] Add contact/support information

### Deliverables

- ✅ Complete documentation site with sidebar navigation
- ✅ All existing docs migrated to MDX format
- ✅ API reference comprehensive and accurate
- ✅ Feature guides with working examples
- ✅ FAQ and troubleshooting accessible

### Dependencies

- Phase 3 (Playground for embedding examples)

### Execution Notes

**MDX Integration**:
- Use frontmatter for metadata (title, description, order)
- Embed React components inline for interactive elements
- Use Astro's content collections for better organization
- Add syntax highlighting with Prism or Shiki (Astro default)

**Content Migration Strategy**:
1. Read existing .md files from docs/ directory
2. Add MDX frontmatter with metadata
3. Convert code blocks to interactive examples where appropriate
4. Add cross-references and internal links
5. Optimize images and diagrams
6. Test all links and examples

**Example MDX Structure**:
```mdx
---
title: "Getting Started"
description: "Quick start guide for the C++ to C transpiler"
order: 1
---

import { CodePlayground } from '../../components/CodePlayground';

# Getting Started

Learn how to use the transpiler in under 5 minutes.

## Your First Transpilation

Try this example:

<CodePlayground
  initialCode={`class Point {
    int x, y;
public:
    Point(int x, int y) : x(x), y(y) {}
};`}
  client:load
/>
```

---

## Phase 5: Example Gallery & Polish

**Duration**: 3-4 days
**Goal**: Showcase real-world examples, optimize performance, finalize design

### Tasks

#### 5.1 Create Example Gallery
- [ ] Create `src/pages/examples/index.astro` gallery page
- [ ] Build grid layout for example cards
- [ ] Add example metadata (title, description, LOC, features)
- [ ] Implement filtering by feature (RAII, templates, exceptions, etc.)
- [ ] Add search functionality (optional)
- [ ] Link each example to dedicated page

#### 5.2 Create Individual Example Pages
- [ ] Create example pages for real-world projects:
  - `examples/json-parser.mdx` (1,091 LOC)
  - `examples/logger.mdx`
  - `examples/test-framework.mdx`
  - `examples/string-formatter.mdx`
  - `examples/resource-manager.mdx`
- [ ] For each example include:
  - Project description and use case
  - Key C++ features demonstrated
  - Full source code (syntax highlighted)
  - Transpiled output (syntax highlighted)
  - Performance comparison (if available)
  - Live playground embed
- [ ] Add "Download" buttons for source code
- [ ] Include architecture diagrams (optional)

#### 5.3 Performance Optimization
- [ ] Run Lighthouse audit on all pages
- [ ] Optimize images (convert to WebP, lazy loading)
- [ ] Implement route prefetching for docs navigation
- [ ] Minimize bundle size (analyze with webpack-bundle-analyzer)
- [ ] Add service worker for offline support (optional)
- [ ] Optimize WASM loading (compression, caching)
- [ ] Add loading skeletons for better perceived performance
- [ ] Test on slow 3G connection

#### 5.4 SEO and Accessibility
- [ ] Add meta tags (Open Graph, Twitter Card) to all pages
- [ ] Create sitemap.xml (Astro plugin)
- [ ] Add robots.txt
- [ ] Implement semantic HTML structure
- [ ] Test with screen reader (NVDA/VoiceOver)
- [ ] Ensure keyboard navigation works
- [ ] Add skip-to-content link
- [ ] Verify color contrast (WCAG AA)
- [ ] Add alt text to all images

#### 5.5 Final Testing and Launch Prep
- [ ] Test on all major browsers (Chrome, Firefox, Safari, Edge)
- [ ] Test on mobile devices (iOS, Android)
- [ ] Verify all links work (internal and external)
- [ ] Test contact forms (if any)
- [ ] Set up analytics (Vercel Analytics or Google Analytics)
- [ ] Create custom 404 page
- [ ] Add legal pages (Privacy Policy, Terms if needed)
- [ ] Configure custom domain (if available)
- [ ] Final production deployment
- [ ] Monitor error logs for first 48 hours

### Deliverables

- ✅ Example gallery showcasing all 5 real-world projects
- ✅ Individual pages for each example with working demos
- ✅ Lighthouse score 90+ on all metrics
- ✅ Accessibility WCAG AA compliant
- ✅ SEO optimized with sitemap and meta tags
- ✅ Production-ready website deployed

### Dependencies

- Phase 4 (Documentation content)
- Real-world example code from tests/real-world/

### Execution Notes

**Example Gallery Card Component**:
```tsx
// src/components/ExampleCard.tsx
interface ExampleCardProps {
  title: string;
  description: string;
  loc: number;
  features: string[];
  href: string;
}

export function ExampleCard({ title, description, loc, features, href }: ExampleCardProps) {
  return (
    <a href={href} className="block p-6 border rounded-lg hover:shadow-lg transition">
      <h3 className="text-xl font-bold mb-2">{title}</h3>
      <p className="text-gray-600 mb-4">{description}</p>
      <div className="flex items-center gap-4 text-sm text-gray-500">
        <span>{loc.toLocaleString()} LOC</span>
        <span>•</span>
        <span>{features.length} features</span>
      </div>
      <div className="flex flex-wrap gap-2 mt-4">
        {features.map(f => (
          <span key={f} className="px-2 py-1 bg-blue-100 text-blue-800 text-xs rounded">
            {f}
          </span>
        ))}
      </div>
    </a>
  );
}
```

**Performance Budget**:
- First Contentful Paint: <1.5s
- Time to Interactive: <3s
- Total Bundle Size: <500KB (before WASM)
- WASM Size: <2MB compressed
- Lighthouse Performance: 90+
- Lighthouse Accessibility: 95+
- Lighthouse Best Practices: 90+
- Lighthouse SEO: 95+

---

## Metadata

### Confidence Levels

| Area | Confidence | Reasoning |
|------|-----------|-----------|
| **Technology Stack** | VERY HIGH | All recommendations backed by research findings, industry case studies |
| **WebAssembly Integration** | HIGH | Emscripten well-documented, pthread pattern proven in production |
| **Deployment Strategy** | VERY HIGH | Vercel native COOP/COEP support verified, no workarounds needed |
| **Timeline Estimates** | MEDIUM-HIGH | Based on solo developer experience, may vary by skill level |
| **Example Migration** | HIGH | Real-world examples already exist in tests/real-world/ |

### Dependencies

**External**:
- Vercel account (free tier sufficient)
- Domain name (optional, Vercel provides subdomain)
- Emscripten SDK (version 3.1.50+)
- Node.js 18+ for Astro

**Internal**:
- Transpiler source code (exists in src/)
- Real-world examples (exist in tests/real-world/)
- Existing documentation (exists in docs/)
- GitHub Actions runners (already configured)

**Browser Requirements**:
- Chrome 92+ (SharedArrayBuffer support)
- Firefox 90+ (SharedArrayBuffer support)
- Safari 15.2+ (SharedArrayBuffer support)
- Edge 92+ (SharedArrayBuffer support)

### Open Questions

1. **Custom Domain**: Do you have a preferred domain name (e.g., cpptoc.dev, cpp-to-c.com)?
   - **Impact**: Domain configuration in Vercel, SSL setup
   - **Decision needed by**: Phase 1 completion

2. **Analytics**: Which analytics platform should we use?
   - **Options**: Vercel Analytics (simple, privacy-friendly), Google Analytics, Plausible
   - **Impact**: Privacy policy requirements, GDPR compliance
   - **Decision needed by**: Phase 5

3. **WASM File Size**: How large is the transpiler WASM expected to be?
   - **Impact**: May need compression, CDN optimization, or lazy loading
   - **Decision needed by**: Phase 2 (after first build)

4. **Mobile Experience**: Should playground work on mobile, or desktop-only?
   - **Current assumption**: Desktop primary, mobile viewing only
   - **Impact**: CodeMirror mobile optimization, touch controls
   - **Decision needed by**: Phase 3

5. **Versioning**: Should website support multiple transpiler versions?
   - **Current assumption**: Single latest version
   - **Impact**: If yes, would require version selector and multiple WASM builds
   - **Decision needed by**: Phase 5

### Assumptions

1. **Solo Developer**: You are the primary/only developer (monorepo approach optimized for this)
2. **Free Tier Sufficient**: Vercel free tier (100 GB bandwidth/month) is adequate
3. **No Backend**: Website is fully static with client-side WASM (no server-side API)
4. **Modern Browsers**: Target users have modern browsers with SharedArrayBuffer support
5. **English Only**: Initial launch is English-only (no i18n)
6. **Open Source**: Website and transpiler are open source (MIT license visible)
7. **Existing CI/CD**: Can extend existing GitHub Actions workflows
8. **No Authentication**: No user accounts or login system needed

### Risk Mitigation

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| **WASM file too large (>5MB)** | MEDIUM | HIGH | Use compression, lazy loading, consider stripping debug symbols |
| **Browser incompatibility** | LOW | MEDIUM | Add compatibility check, show friendly error message, fallback to server-side transpilation (future) |
| **Vercel bandwidth limits** | LOW | LOW | Monitor usage, upgrade to paid plan if needed, or switch to Cloudflare (unlimited) |
| **Slow transpilation** | MEDIUM | MEDIUM | Implement timeout, progress indicator, consider chunking large files |
| **Mobile UX poor** | MEDIUM | LOW | Focus on desktop first, optimize mobile in iteration 2 |

### Success Criteria (Measurable)

**Phase 1**:
- [ ] Vercel deployment returns 200 status
- [ ] `crossOriginIsolated === true` in browser console
- [ ] Lighthouse Performance score >85

**Phase 2**:
- [ ] WASM module loads without errors
- [ ] `SharedArrayBuffer` available in playground page
- [ ] Simple transpilation test passes (<1 second)

**Phase 3**:
- [ ] Playground transpiles 5 example snippets successfully
- [ ] Error messages display correctly for invalid C++
- [ ] CodeMirror loads in <500ms on fast connection

**Phase 4**:
- [ ] All documentation pages render without 404s
- [ ] Sidebar navigation works on all screen sizes
- [ ] Search returns relevant results (if implemented)

**Phase 5**:
- [ ] All 5 real-world examples display correctly
- [ ] Lighthouse scores: Performance 90+, Accessibility 95+, SEO 95+
- [ ] Zero console errors on production deployment

### Next Steps After Completion

1. **Gather Feedback**: Share with C++ community, collect user feedback
2. **Iteration 2 Features**:
   - Multi-file project support in playground
   - Downloadable transpiled code as .zip
   - Comparison mode (show C++ and C side-by-side with highlights)
   - Version selector for different transpiler releases
   - Blog for release announcements
3. **Community Building**:
   - Add discussions/forum integration
   - Create video tutorials
   - Write technical blog posts
4. **Monitoring & Maintenance**:
   - Set up error tracking (Sentry or similar)
   - Monitor performance metrics
   - Keep dependencies updated
   - Regular content updates

---

## Execution Checklist

### Pre-Phase 1
- [ ] Review and approve this plan
- [ ] Set up Vercel account
- [ ] Decide on domain name (or use Vercel subdomain)
- [ ] Install Emscripten locally for testing

### During Implementation
- [ ] Follow TDD principles (test-first approach)
- [ ] Commit frequently with conventional commits
- [ ] Use feature branches (e.g., `feature/phase-1-setup`)
- [ ] Deploy to Vercel preview URLs for testing
- [ ] Document issues and blockers as they arise

### Post-Implementation
- [ ] Conduct full website audit (Lighthouse, WAVE, manual testing)
- [ ] Get feedback from at least 3 beta users
- [ ] Write launch announcement (README update, blog post)
- [ ] Monitor analytics for first month
- [ ] Plan iteration 2 based on user feedback

---

**Total Estimated Time**: 19-24 days (4-5 weeks)
**Recommended Approach**: Sequential phases with daily commits and preview deployments
**Key to Success**: Focus on Phase 1 and Phase 2 first (foundation + WASM), then iterate quickly on Phases 3-5

*This plan is ready for Phase 1 execution. Start with Astro initialization and Vercel deployment to establish the foundation.*

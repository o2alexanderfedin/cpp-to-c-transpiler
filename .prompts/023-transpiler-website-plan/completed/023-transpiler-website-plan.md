# Transpiler Website Architecture Plan

<objective>
Create implementation roadmap for a presentation website for the C++ to C transpiler with WebAssembly-based interactive demo.

**Purpose**: Guide phased development of documentation site with in-browser transpilation
**Input**: Research findings from transpiler-website-research.md
**Output**: transpiler-website-plan.md with 4-5 implementation phases and git submodule setup
</objective>

<context>
Research findings: @.prompts/022-transpiler-website-research/transpiler-website-research.md

**Key findings to incorporate**:
- Selected framework and WebAssembly approach from research
- COOP/COEP header configuration strategy
- Git submodule pattern recommendation
- Code editor component choice (Monaco vs CodeMirror 6)
- Deployment platform selection

**Current transpiler state**:
- C++ to C transpiler exists and works
- Real-world examples in `tests/real-world/` (5 projects: json-parser, logger, test-framework, string-formatter, resource-manager)
- CI/CD pipeline functional with comprehensive testing
- Documentation exists in `docs/` directory
</context>

<planning_requirements>
**Must Address**:
1. **Git submodule structure** - How source and deployment interact with main repo
2. **Framework setup** - Initial project structure based on selected framework
3. **WebAssembly integration** - Transpiler compilation to WASM with pthread support
4. **Interactive demo** - Code playground with input/output panels
5. **Content migration** - Getting started guide, API docs, example gallery
6. **Deployment** - CI/CD pipeline for automatic deployment

**Constraints**:
- Must support multi-threaded WebAssembly (SharedArrayBuffer + Atomics)
- Must be maintainable by solo developer
- Must have fast load times (<3s to interactive)
- Must work on GitHub-hosted repository
- Must integrate cleanly with existing CI/CD

**Success Criteria**:
- Website deployed and accessible via custom URL
- Interactive demo can transpile C++ code in browser
- All 5 real-world examples showcased
- Getting started guide is comprehensive
- Git submodule updates are automatic via CI/CD
</planning_requirements>

<output_structure>
Save to: `.prompts/023-transpiler-website-plan/transpiler-website-plan.md`

Structure the plan using this XML format:

```xml
<plan>
  <summary>
    {One paragraph overview: tech stack selected, git submodule approach, 4-5 phases, timeline estimate}
  </summary>

  <architecture>
    <tech_stack>
      <framework>{Selected framework from research}</framework>
      <editor>{Monaco or CodeMirror 6}</editor>
      <deployment>{Vercel/Netlify/GitHub Pages}</deployment>
      <submodule_pattern>{Approach selected from research}</submodule_pattern>
    </tech_stack>

    <directory_structure>
      {Expected folder layout for website repository}
      {Relationship to main transpiler repo}
    </directory_structure>

    <wasm_integration>
      {How transpiler will be compiled to WASM}
      {Header configuration for COOP/COEP}
      {Loading strategy (streaming, lazy, preload)}
    </wasm_integration>

    <git_submodule_workflow>
      {How submodule is added to main repo}
      {Update mechanism (manual, CI/CD trigger)}
      {Version synchronization strategy}
    </git_submodule_workflow>
  </architecture>

  <phases>
    <phase number="1" name="repository-and-framework-setup">
      <objective>Create website repository, configure framework, establish git submodule</objective>
      <tasks>
        <task priority="high">Create new GitHub repository for website (e.g., cpp-to-c-transpiler-website)</task>
        <task priority="high">Initialize selected framework with TypeScript</task>
        <task priority="high">Configure COOP/COEP headers per research findings</task>
        <task priority="high">Set up git submodule connection to main transpiler repo</task>
        <task priority="medium">Configure deployment platform (Vercel/Netlify)</task>
        <task priority="medium">Set up basic CI/CD for website deployments</task>
        <task priority="low">Add custom domain configuration (if applicable)</task>
      </tasks>
      <deliverables>
        <deliverable>Website repository initialized and deployed (hello world)</deliverable>
        <deliverable>Git submodule configured in main transpiler repo</deliverable>
        <deliverable>Headers working (verify with browser console: SharedArrayBuffer available)</deliverable>
      </deliverables>
      <dependencies>
        - GitHub repository creation permissions
        - Deployment platform account (Vercel/Netlify)
        - Domain name (optional, can use platform subdomain)
      </dependencies>
      <execution_notes>
        Test header configuration early - COOP/COEP is critical for later phases.
        Verify git submodule works both ways (main repo → website, website → main repo).
      </execution_notes>
    </phase>

    <phase number="2" name="wasm-transpiler-build">
      <objective>Compile transpiler to WebAssembly with pthread support and integrate into website</objective>
      <tasks>
        <task priority="high">Create emscripten build configuration for transpiler</task>
        <task priority="high">Compile with pthread support (-pthread flag)</task>
        <task priority="high">Generate WASM module and JavaScript glue code</task>
        <task priority="high">Create TypeScript wrapper for WASM API</task>
        <task priority="medium">Implement WASM loading with error handling</task>
        <task priority="medium">Add build script to CI/CD for automatic WASM generation</task>
        <task priority="low">Optimize WASM size (wasm-opt, compression)</task>
      </tasks>
      <deliverables>
        <deliverable>Transpiler compiled to WASM with multi-threading</deliverable>
        <deliverable>TypeScript API wrapper for browser usage</deliverable>
        <deliverable>CI/CD automatically builds WASM on transpiler changes</deliverable>
      </deliverables>
      <dependencies>
        - Emscripten toolchain installed
        - Transpiler builds successfully with emscripten
        - Phase 1 complete (headers configured)
      </dependencies>
      <execution_notes>
        Test SharedArrayBuffer availability before attempting pthread WASM.
        Start with single-threaded WASM first, add pthread as second iteration.
        Document memory requirements for WASM module.
      </execution_notes>
    </phase>

    <phase number="3" name="interactive-demo-playground">
      <objective>Build code playground with editor, transpile button, output panels</objective>
      <tasks>
        <task priority="high">Integrate selected code editor (Monaco/CodeMirror 6)</task>
        <task priority="high">Create split-pane layout (C++ input | C output)</task>
        <task priority="high">Wire editor to WASM transpiler API</task>
        <task priority="high">Add syntax highlighting for C++ and C</task>
        <task priority="medium">Implement example code dropdown (5 real-world examples)</task>
        <task priority="medium">Add error display panel for compilation errors</task>
        <task priority="medium">Add transpile button with loading state</task>
        <task priority="low">Add copy-to-clipboard for output</task>
        <task priority="low">Add URL state persistence (share transpiled code via URL)</task>
      </tasks>
      <deliverables>
        <deliverable>Functional code playground on /playground route</deliverable>
        <deliverable>All 5 real-world examples available as quick-start templates</deliverable>
        <deliverable>Error handling with user-friendly messages</deliverable>
      </deliverables>
      <dependencies>
        - Phase 2 complete (WASM transpiler working)
        - Code editor bundle loaded (Monaco or CodeMirror 6)
      </dependencies>
      <execution_notes>
        Test with large input files (>1000 lines) for performance.
        Ensure worker threads don't block UI.
        Pre-load editor with example code for better UX.
      </execution_notes>
    </phase>

    <phase number="4" name="documentation-content-migration">
      <objective>Migrate existing docs and create getting started guide</objective>
      <tasks>
        <task priority="high">Create getting started guide (installation, basic usage, examples)</task>
        <task priority="high">Migrate existing docs from transpiler /docs directory</task>
        <task priority="high">Create example gallery showcasing 5 real-world projects</task>
        <task priority="medium">Add API documentation (auto-generated or manual)</task>
        <task priority="medium">Create architecture overview page</task>
        <task priority="medium">Add CI/CD pipeline documentation</task>
        <task priority="low">Create FAQ page</task>
        <task priority="low">Add contribution guide</task>
      </tasks>
      <deliverables>
        <deliverable>Getting started guide published</deliverable>
        <deliverable>Example gallery with code snippets and explanations</deliverable>
        <deliverable>API documentation (if applicable)</deliverable>
      </deliverables>
      <dependencies>
        - Phase 1 complete (framework and routing set up)
        - Content reviewed and approved
      </dependencies>
      <execution_notes>
        Use MDX for examples (embed React components in markdown).
        Link playground examples to example gallery.
        Ensure navigation is intuitive (sidebar, search).
      </execution_notes>
    </phase>

    <phase number="5" name="polish-and-deployment">
      <objective>SEO, performance optimization, analytics, final deployment</objective>
      <tasks>
        <task priority="high">Add meta tags for SEO (title, description, OG tags)</task>
        <task priority="high">Optimize bundle size (code splitting, lazy loading)</task>
        <task priority="high">Run Lighthouse audit and fix issues (aim for 90+ score)</task>
        <task priority="medium">Add sitemap.xml for search engines</task>
        <task priority="medium">Configure analytics (optional, e.g., Plausible, Simple Analytics)</task>
        <task priority="medium">Add RSS feed for updates (optional)</task>
        <task priority="low">Create custom 404 page</task>
        <task priority="low">Add dark mode toggle</task>
      </tasks>
      <deliverables>
        <deliverable>Website passes Lighthouse with 90+ scores</deliverable>
        <deliverable>SEO metadata complete</deliverable>
        <deliverable>Production deployment live</deliverable>
      </deliverables>
      <dependencies>
        - All previous phases complete
        - Content finalized
      </dependencies>
      <execution_notes>
        Use framework's built-in optimization features.
        Test on mobile devices (responsive design).
        Verify WASM loads correctly on slower connections.
      </execution_notes>
    </phase>
  </phases>

  <metadata>
    <confidence level="high">
      Plan is comprehensive and based on research findings. All phases are executable.
    </confidence>
    <dependencies>
      - Emscripten toolchain for WASM compilation
      - GitHub repository for website
      - Deployment platform account (Vercel/Netlify/GitHub Pages)
      - Transpiler source code access
    </dependencies>
    <open_questions>
      - Exact WASM compilation flags for optimal size/performance trade-off
      - Whether to include multi-threading in first iteration or start single-threaded
      - Custom domain name preference
      - Analytics platform choice (privacy-friendly options)
    </open_questions>
    <assumptions>
      - Transpiler compiles successfully with emscripten
      - Selected framework from research supports all requirements
      - COOP/COEP headers can be configured on deployment platform
      - Git submodule updates can be automated via CI/CD
      - Solo developer has time for 4-5 week implementation (1 week per phase)
    </assumptions>
  </metadata>
</plan>
```
</output_structure>

<summary_requirements>
Create `.prompts/023-transpiler-website-plan/SUMMARY.md`:

```markdown
# Transpiler Website Architecture Plan

**{One sentence: framework + git submodule approach + 5 phases + key feature}**
Example: "Astro-based website with separate repo submodule, 5 phases from setup to deployment, WebAssembly playground central feature"

## Key Phases
1. **Repository Setup** - Framework + git submodule + COOP/COEP headers
2. **WASM Build** - Emscripten compilation with pthread support
3. **Interactive Demo** - Code playground with editor integration
4. **Content Migration** - Getting started + example gallery + docs
5. **Polish** - SEO, performance, deployment

## Decisions Needed
- Approve selected framework from research
- Confirm git submodule pattern
- Choose deployment platform (Vercel vs Netlify vs GitHub Pages)
- Decide on analytics (optional)

## Blockers
- Emscripten build may require adjustments to transpiler CMake
- COOP/COEP headers might not work on GitHub Pages (verify in Phase 1)

## Next Step
Execute Phase 1: Repository and framework setup
```

**One-liner must specify framework and key architectural decisions.**
</summary_requirements>

<success_criteria>
- All 5 phases have specific, actionable tasks
- Each phase builds logically on previous phase
- Git submodule workflow is clearly defined
- WebAssembly integration approach is detailed
- Deliverables are concrete and testable
- Dependencies and blockers are identified
- Execution notes provide context for implementation
- SUMMARY.md provides executive overview
- Ready for Phase 1 implementation prompt
</success_criteria>

# Transpiler Website Technology Research

<session_initialization>
Before beginning research, verify today's date:
!`date +%Y-%m-%d`

Use this date when searching for "current" or "latest" information.
Example: If today is 2025-12-19, search for "2025" not "2024".
</session_initialization>

<research_objective>
Research modern web technologies for a C++ to C transpiler presentation website that will support WebAssembly execution with multi-threading.

**Purpose**: Select optimal tech stack and git submodule approach for a documentation/demo website
**Scope**: Static site generators, WebAssembly frameworks, git submodule patterns, deployment strategies
**Output**: transpiler-website-research.md with structured findings

**Critical Requirements**:
- Must support **WebAssembly with multi-threading** (SharedArrayBuffer, Atomics)
- Interactive demo/playground where users can transpile C++ code in-browser
- Getting started guide and example gallery
- Fast load times, SEO-friendly for discoverability
- Professional documentation site aesthetic
- Git submodule integration with main transpiler repository
</research_objective>

<research_scope>
<include>
**1. Static Site Generators / Web Frameworks** (priority: high)
- Astro, Next.js, Docusaurus, VitePress, Nextra
- WebAssembly support (especially multi-threaded)
- Build performance and output size
- Documentation-oriented features (search, navigation, syntax highlighting)
- TypeScript support

**2. WebAssembly + Multi-Threading Support** (priority: critical)
- SharedArrayBuffer and Atomics API support
- Cross-Origin-Opener-Policy and Cross-Origin-Embedder-Policy requirements
- Headers configuration for different frameworks
- pthread emulation in emscripten/WASI
- Browser compatibility (Chrome, Firefox, Safari, Edge)

**3. Interactive Code Playground Components** (priority: high)
- Monaco Editor vs CodeMirror 6
- Split pane layouts for input/output
- Syntax highlighting for C++ and C
- Real-time transpilation integration
- Example code management

**4. Git Submodule Best Practices** (priority: high)
- Submodule for deployment artifacts vs source
- Separate repository vs monorepo approaches
- CI/CD workflow with submodules
- GitHub Pages / Vercel / Netlify deployment with submodules
- Version management and update strategies

**5. Deployment Platforms** (priority: medium)
- GitHub Pages (with COOP/COEP headers support)
- Vercel (WebAssembly and header configuration)
- Netlify (WebAssembly and header configuration)
- Cloudflare Pages (WebAssembly support)
- Comparison for transpiler documentation use case

**6. SEO and Performance** (priority: medium)
- Static generation vs SSR for SEO
- Bundle size optimization
- Lighthouse scores for documentation sites
- Core Web Vitals with WebAssembly
</include>

<exclude>
- Backend server implementation (static site only)
- Authentication/user accounts
- Analytics platforms (can add later)
- CDN configuration details (deployment-specific)
- Pricing/cost analysis (all options are free-tier compatible)
</exclude>

<sources>
**Official Documentation** (use WebFetch):
- https://docs.astro.build/ - Astro documentation
- https://nextjs.org/docs - Next.js documentation
- https://docusaurus.io/docs - Docusaurus documentation
- https://vitepress.dev/guide/what-is-vitepress - VitePress documentation
- https://emscripten.org/docs/porting/pthreads.html - Emscripten pthreads
- https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/SharedArrayBuffer - SharedArrayBuffer API
- https://web.dev/articles/coop-coep - COOP/COEP explainer

**Search Queries** (use WebSearch):
- "static site generator WebAssembly multi-threading 2025"
- "SharedArrayBuffer Cross-Origin-Opener-Policy configuration 2025"
- "Monaco Editor vs CodeMirror 6 comparison 2025"
- "git submodule documentation website best practices 2025"
- "GitHub Pages COOP COEP headers 2025"
- "Astro WebAssembly example 2025"
- "Docusaurus code playground component 2025"

**Time Constraints**: Prefer sources from 2024-2025 due to rapid WebAssembly evolution
</sources>
</research_scope>

<verification_checklist>
**WebAssembly Multi-Threading** (Critical - verify each framework):
□ Astro: Can set COOP/COEP headers? Verify with official docs
□ Next.js: Can set COOP/COEP headers? Verify with official docs
□ Docusaurus: Can set COOP/COEP headers? Verify with official docs
□ VitePress: Can set COOP/COEP headers? Verify with official docs
□ Document exact header configuration for each framework

**Git Submodule Patterns**:
□ Enumerate common approaches (source in submodule, artifacts in submodule, hybrid)
□ Verify CI/CD workflow examples with official docs
□ Check for known issues with each hosting platform + submodules

**Code Editor Components**:
□ Verify Monaco Editor bundle size and performance
□ Verify CodeMirror 6 bundle size and performance
□ Check WebAssembly compatibility for both editors

**Deployment Platforms**:
□ GitHub Pages: Can set custom headers? Verify capability
□ Vercel: COOP/COEP configuration method
□ Netlify: COOP/COEP configuration method
□ Cloudflare Pages: COOP/COEP configuration method

**For all research**:
□ Verify negative claims ("X is not possible") with official docs
□ Confirm all primary claims have authoritative sources
□ Check both current docs AND recent updates/changelogs
□ Test multiple search queries to avoid missing information
□ Check for environment/tool-specific variations
</verification_checklist>

<research_quality_assurance>
Before completing research, perform these checks:

<completeness_check>
- [ ] All enumerated frameworks documented with WebAssembly support evidence
- [ ] Each git submodule approach evaluated against ALL requirements
- [ ] Official documentation cited for critical claims (especially COOP/COEP)
- [ ] Contradictory information resolved or flagged
</completeness_check>

<source_verification>
- [ ] Primary claims backed by official/authoritative sources
- [ ] Version numbers and dates included where relevant
- [ ] Actual URLs provided (not just "search for X")
- [ ] Distinguish verified facts from assumptions
</source_verification>

<blind_spots_review>
Ask yourself: "What might I have missed?"
- [ ] Are there static site generators I didn't investigate?
- [ ] Did I check for multiple deployment platforms?
- [ ] Did I verify COOP/COEP header support claims with actual docs?
- [ ] Did I look for recent WebAssembly multi-threading updates?
</blind_spots_review>

<critical_claims_audit>
For any statement like "X doesn't support Y" or "Z is the only way":
- [ ] Is this verified by official documentation?
- [ ] Have I checked for recent updates that might change this?
- [ ] Are there alternative approaches I haven't considered?
</critical_claims_audit>
</research_quality_assurance>

<output_requirements>
Write findings incrementally to `.prompts/022-transpiler-website-research/transpiler-website-research.md` as you discover them:

1. **Create the file with initial structure**:
   ```xml
   <research>
     <summary>[Will complete at end]</summary>
     <findings></findings>
     <recommendations></recommendations>
     <code_examples></code_examples>
     <metadata></metadata>
   </research>
   ```

2. **As you research each aspect, immediately append findings**:
   - Research Astro WebAssembly support → Write finding
   - Discover COOP/COEP header configuration → Write finding
   - Find Monaco Editor bundle size → Write finding
   - Discover git submodule pattern → Write finding
   - Research GitHub Pages limitations → Write finding

3. **After all research complete**:
   - Write summary (synthesize all findings)
   - Write recommendations (ranked by priority: high/medium/low)
   - Write metadata (confidence, dependencies, open questions, assumptions)
   - Write quality report (sources consulted, claims verified vs assumed)

**This incremental approach ensures all work is saved even if execution hits token limits.**

Structure findings using this XML format:

```xml
<research>
  <summary>
    {2-3 paragraph executive summary of key findings and top recommendation}
  </summary>

  <findings>
    <finding category="frameworks">
      <title>{Framework name and WebAssembly support}</title>
      <detail>{Detailed explanation, COOP/COEP support, performance}</detail>
      <source>{Official docs URL}</source>
      <relevance>{Why this matters for transpiler demo site}</relevance>
    </finding>
    <!-- Additional findings for each framework, editor, deployment platform -->
  </findings>

  <recommendations>
    <recommendation priority="high">
      <action>{What framework/approach to use}</action>
      <rationale>{Why - WebAssembly support, performance, DX}</rationale>
    </recommendation>
    <recommendation priority="high">
      <action>{What git submodule pattern to use}</action>
      <rationale>{Why - CI/CD, maintainability, deployment}</rationale>
    </recommendation>
    <recommendation priority="medium">
      <action>{What deployment platform to use}</action>
      <rationale>{Why - COOP/COEP headers, cost, performance}</rationale>
    </recommendation>
    <!-- Additional recommendations -->
  </recommendations>

  <code_examples>
    {Header configuration examples for COOP/COEP}
    {Git submodule setup commands}
    {WebAssembly initialization code}
  </code_examples>

  <metadata>
    <confidence level="{high|medium|low}">
      {Why this confidence level - based on official docs, testing, assumptions}
    </confidence>
    <dependencies>
      {What's needed: emscripten build, WASM file, etc.}
    </dependencies>
    <open_questions>
      {What couldn't be determined - e.g., actual performance with large WASM files}
    </open_questions>
    <assumptions>
      {What was assumed - e.g., transpiler will be compiled with emscripten pthread support}
    </assumptions>

    <quality_report>
      <sources_consulted>
        {List URLs of official documentation and primary sources}
      </sources_consulted>
      <claims_verified>
        {Key findings verified with official sources}
        - Astro COOP/COEP support: Verified via X
        - GitHub Pages header limitations: Verified via Y
      </claims_verified>
      <claims_assumed>
        {Findings based on inference or incomplete information}
        - Performance with 50MB WASM: Inferred from smaller examples
      </claims_assumed>
      <contradictions_encountered>
        {Any conflicting information found and how resolved}
      </contradictions_encountered>
      <confidence_by_finding>
        - Framework WASM support: High (official docs + examples)
        - Git submodule best practice: Medium (community consensus, no official standard)
        - Deployment platform comparison: High (tested all platforms' docs)
      </confidence_by_finding>
    </quality_report>
  </metadata>
</research>
```
</output_requirements>

<summary_requirements>
After completing research, create `.prompts/022-transpiler-website-research/SUMMARY.md`:

```markdown
# Transpiler Website Technology Research

**{One sentence describing top recommendation - must be substantive}**

## Key Findings
• {Most important finding about framework choice}
• {Critical finding about WebAssembly multi-threading}
• {Important finding about git submodule approach}
• {Notable finding about deployment platform}

## Decisions Needed
{What requires user choice - framework selection if multiple viable, deployment platform}

## Blockers
{External impediments - e.g., browser support limitations, platform constraints}

## Next Step
Create transpiler-website-plan.md to architect the selected solution
```

**The one-liner MUST be specific** (not "Research completed" or "Analyzed frameworks").
Example: "Astro + Vercel recommended for optimal WASM multi-threading with zero config headers"
</summary_requirements>

<pre_submission_checklist>
Before submitting your research report, confirm:

**Scope Coverage**
- [ ] All major frameworks investigated (Astro, Next.js, Docusaurus, VitePress)
- [ ] Each framework's COOP/COEP support documented or marked "not supported"
- [ ] Official documentation cited for WebAssembly claims

**Claim Verification**
- [ ] Each "doesn't support" claim verified with official docs
- [ ] URLs to official documentation included for key findings
- [ ] Framework versions specified (critical for WebAssembly features)

**Quality Controls**
- [ ] Blind spots review completed ("What did I miss?")
- [ ] Quality report section filled out honestly
- [ ] Confidence levels assigned with justification
- [ ] Assumptions clearly distinguished from verified facts

**Output Completeness**
- [ ] All required XML sections present
- [ ] SUMMARY.md created with substantive one-liner
- [ ] Sources consulted listed with URLs
- [ ] Next steps clearly identified (create plan)
</pre_submission_checklist>

<success_criteria>
- Top 3 framework options clearly ranked with rationale
- WebAssembly multi-threading feasibility conclusively determined
- COOP/COEP header configuration approach documented for each framework
- Git submodule best practice identified with pros/cons
- Deployment platform comparison with WASM support matrix
- Code examples for critical configurations
- Ready for planning phase to design architecture
</success_criteria>

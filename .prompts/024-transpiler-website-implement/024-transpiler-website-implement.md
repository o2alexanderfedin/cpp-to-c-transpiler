# Transpiler Website Implementation - Phase 1

<objective>
Implement Phase 1 of the transpiler presentation website: Repository setup, framework initialization, COOP/COEP header configuration, and git submodule connection.

**Purpose**: Establish foundation for WebAssembly-enabled documentation site with interactive demo
**Output**: Functional website repository deployed with proper security headers, connected as git submodule to main transpiler repo
</objective>

<context>
Research findings: @.prompts/022-transpiler-website-research/transpiler-website-research.md
Implementation plan: @.prompts/023-transpiler-website-plan/transpiler-website-plan.md

**Key decisions from plan**:
- Framework: {Selected from research - Astro/Next.js/Docusaurus/VitePress}
- Deployment: {Selected platform - Vercel/Netlify/GitHub Pages}
- Git submodule pattern: {Pattern selected from research}
- COOP/COEP configuration: {Approach from research}

**Main transpiler repository**:
- Location: Current repository at `{pwd}`
- CI/CD: GitHub Actions workflow in `.github/workflows/ci.yml`
- Documentation: Exists in `docs/` directory
</context>

<requirements>

**Functional Requirements**:
1. **Repository Creation**
   - Create new GitHub repository named `cpp-to-c-transpiler-website`
   - Initialize with selected framework and TypeScript
   - Set up basic routing (home, playground, docs, examples)

2. **Security Headers (Critical for WebAssembly)**
   - Configure Cross-Origin-Opener-Policy: same-origin
   - Configure Cross-Origin-Embedder-Policy: require-corp
   - Verify SharedArrayBuffer is available in browser console

3. **Git Submodule Integration**
   - Add website repo as submodule to main transpiler repo (or vice versa depending on pattern)
   - Configure bi-directional updates via CI/CD
   - Document submodule update workflow

4. **Deployment Setup**
   - Connect repository to deployment platform
   - Configure custom domain (if applicable) or use platform subdomain
   - Enable automatic deployments on push to main/master

5. **Basic CI/CD**
   - Set up build workflow for website deployments
   - Add status checks (type check, lint, build)
   - Configure deployment triggers

**Quality Requirements**:
- All TypeScript code must type-check without errors
- Headers must be verifiable in browser DevTools
- Git submodule must work for both contributors and CI/CD
- Deployment must be automatic (no manual steps)
- Documentation for setup process must be clear

**Constraints**:
- Must use free tier of deployment platform
- Must not require server-side logic (static site only)
- Must work with existing GitHub Actions setup
- Must be maintainable by solo developer
</requirements>

<implementation>

**Framework Setup**:
Follow official initialization guide for selected framework:
- Use TypeScript template if available
- Enable strict type checking in tsconfig.json
- Set up path aliases for clean imports (@/components, @/utils)
- Configure MDX support if not included by default

**Header Configuration** (Critical - verify before proceeding):
Different approaches per platform:
- **Vercel**: Use `vercel.json` with headers configuration
- **Netlify**: Use `netlify.toml` or `_headers` file
- **GitHub Pages**: May require custom solution (check research findings)

Example for Vercel (`vercel.json`):
```json
{
  "headers": [
    {
      "source": "/(.*)",
      "headers": [
        {
          "key": "Cross-Origin-Opener-Policy",
          "value": "same-origin"
        },
        {
          "key": "Cross-Origin-Embedder-Policy",
          "value": "require-corp"
        }
      ]
    }
  ]
}
```

**Avoid**:
- Don't use server-side rendering for playground route (client-only for WASM)
- Don't commit node_modules or build artifacts
- Don't hardcode URLs (use environment variables)
- Don't skip header verification (critical for later phases)

**Git Submodule Workflow**:
If website is submodule of transpiler:
```bash
# In main transpiler repo
git submodule add https://github.com/{user}/cpp-to-c-transpiler-website website
git submodule update --init --recursive
```

If transpiler is referenced by website:
```bash
# In website repo
git submodule add https://github.com/{user}/cpp-to-c-transpiler transpiler
```

Document update process in both repos' README.md.
</implementation>

<output>

**Create new repository**: `cpp-to-c-transpiler-website/`

**In new repository, create**:
- `package.json` - Dependencies and scripts
- `tsconfig.json` - TypeScript configuration (strict mode)
- `README.md` - Setup instructions and submodule workflow
- Framework configuration file (e.g., `astro.config.mjs`, `next.config.js`)
- Headers configuration file (`vercel.json`, `netlify.toml`, or equivalent)
- `.github/workflows/deploy.yml` - CI/CD workflow for deployments
- `src/pages/index.{ext}` - Homepage (Hello World for now)
- `src/pages/playground.{ext}` - Playground route (empty, Phase 3)
- `src/pages/docs.{ext}` - Docs route (empty, Phase 4)
- `src/pages/examples.{ext}` - Examples gallery route (empty, Phase 4)

**In main transpiler repository, modify**:
- `.gitmodules` - Add website submodule reference
- `README.md` - Add section on website submodule
- `.github/workflows/ci.yml` - Add job to update website submodule (optional, depends on pattern)

**Documentation**:
Create `WEBSITE_SETUP.md` in website repo explaining:
- Prerequisites (Node.js version, git, deployment account)
- Local development setup
- Git submodule update workflow
- Deployment process
- Header verification steps
</output>

<verification>

**Before declaring Phase 1 complete**:

1. **Headers Verification**:
   - Deploy website to platform
   - Open browser DevTools → Console
   - Run: `typeof SharedArrayBuffer !== 'undefined'`
   - Expected: `true` (if false, headers not configured correctly)

2. **TypeScript Check**:
   ```bash
   npm run type-check  # or tsc --noEmit
   ```
   Expected: No errors

3. **Build Success**:
   ```bash
   npm run build
   ```
   Expected: Successful build with output directory

4. **Git Submodule**:
   - Clone main transpiler repo fresh
   - Run: `git submodule update --init --recursive`
   - Verify website appears in correct location
   - Test: Make change in website, commit, update in main repo

5. **Deployment**:
   - Push to main branch
   - Verify automatic deployment triggers
   - Check deployed URL is accessible
   - Verify all routes load (/, /playground, /docs, /examples)

6. **CI/CD**:
   - Verify GitHub Actions workflow runs on push
   - Check all status checks pass
   - Confirm deployment succeeds

**Edge Cases to Test**:
- Fresh clone of transpiler repo (submodule initialization works)
- Deployment from PR (if applicable)
- Header configuration on 404 page (should still have headers)
- Multiple routes (headers apply to all)
</verification>

<success_criteria>
- [x] Website repository created and initialized with selected framework
- [x] TypeScript configured in strict mode with no errors
- [x] COOP/COEP headers configured and verified (SharedArrayBuffer available)
- [x] Git submodule connected and working bi-directionally
- [x] Deployment platform connected with automatic deploys
- [x] Basic CI/CD workflow running (build, type-check, deploy)
- [x] All 4 routes created and accessible (/, /playground, /docs, /examples)
- [x] WEBSITE_SETUP.md documentation created
- [x] README.md updated in both repos with submodule instructions
- [x] SUMMARY.md created with files list and Phase 2 next step

**Critical Success Indicator**:
Open deployed site in browser, open console, verify:
```javascript
typeof SharedArrayBuffer !== 'undefined'  // must return true
```
If this returns `false`, Phase 1 is NOT complete - fix headers first.
</success_criteria>

<summary_requirements>
Create `.prompts/024-transpiler-website-implement/SUMMARY.md`:

```markdown
# Transpiler Website Implementation - Phase 1

**{Framework} website deployed with COOP/COEP headers, git submodule connected**

## Files Created
**New Repository**: `cpp-to-c-transpiler-website/`
- `package.json` - Dependencies and build scripts
- `tsconfig.json` - Strict TypeScript configuration
- `{framework-config}` - Framework configuration
- `{headers-config}` - COOP/COEP header configuration
- `.github/workflows/deploy.yml` - CI/CD deployment workflow
- `src/pages/index.{ext}` - Homepage
- `src/pages/playground.{ext}` - Playground route (empty)
- `src/pages/docs.{ext}` - Docs route (empty)
- `src/pages/examples.{ext}` - Examples route (empty)
- `WEBSITE_SETUP.md` - Setup and submodule documentation

**Main Transpiler Repo Modified**:
- `.gitmodules` - Submodule reference
- `README.md` - Website submodule section

## Test Status
- [x] TypeScript type-check passes
- [x] Build succeeds
- [x] SharedArrayBuffer available (headers verified)
- [x] Git submodule works
- [x] Automatic deployment works
- [x] All routes accessible

## Deployed URL
{Actual deployed URL}

## Blockers
{Any issues encountered - e.g., "GitHub Pages doesn't support custom headers, switched to Vercel"}

## Next Step
Execute Phase 2: Compile transpiler to WebAssembly with pthread support
```

**Include actual deployed URL and specific framework used.**
</summary_requirements>

<post_implementation_notes>
**For the agent executing this prompt**:

1. **Repository Creation**:
   - Use `gh repo create` if available, otherwise document manual steps
   - Initialize with .gitignore (node_modules, build artifacts)

2. **Framework Selection**:
   - Use the specific framework recommended in research findings
   - Follow official getting started guide exactly
   - Don't deviate from recommended configuration

3. **Header Verification is Critical**:
   - Test headers IMMEDIATELY after deployment
   - If SharedArrayBuffer is undefined, stop and fix headers
   - Phase 2 (WASM) will fail without proper headers

4. **Git Submodule Pattern**:
   - Follow the exact pattern from research findings
   - Test clone + submodule init before considering complete
   - Document update workflow clearly

5. **Documentation**:
   - Be explicit about every setup step
   - Include troubleshooting section for common issues
   - Provide verification commands

6. **Deployment Platform**:
   - Use platform from research recommendation
   - Configure automatic deployments immediately
   - Test deployment before finalizing

</post_implementation_notes>

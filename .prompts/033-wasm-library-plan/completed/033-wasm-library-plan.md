# Plan: WebAssembly Library Build Configuration

## Objective

Create a comprehensive, phase-by-phase implementation plan for compiling the hupyy-cpp-to-c transpiler to WebAssembly with dual builds (Cloudflare-optimized minimal + full-featured website version), complete JavaScript/TypeScript glue code, and deployment configuration.

## Context

**Research Findings:**
Reference the research output: @.prompts/032-wasm-library-research/wasm-library-research.md

**Key inputs from research:**
- Emscripten version and build flags
- Size feasibility determination for Cloudflare Workers
- API design approach (embind vs manual)
- Build system integration strategy
- Website compatibility constraints

**Project State:**
- Current version: v1.22.0 (5 ACSL phases complete)
- Build system: CMake
- Dependencies: Clang/LLVM 15+
- Website: Astro-based (@.prompts/022-transpiler-website-research/)

## Planning Requirements

### 1. Build System Architecture

**Design CMake configuration for dual WASM builds:**

```cmake
# Target structure to define:
#
# wasm-minimal:
#   - Core transpiler only
#   - No ACSL annotators
#   - Optimized for size (-Oz, --closure, tree-shaking)
#   - Target: <2MB compressed for Cloudflare
#
# wasm-full:
#   - All Phase 1-5 ACSL annotators
#   - Optimized for features over size
#   - Target: Best performance on website
#
# Build directory structure:
# build-wasm/
#   ├── minimal/
#   │   ├── cpptoc.js
#   │   ├── cpptoc.wasm
#   │   └── cpptoc.d.ts
#   └── full/
#       ├── cpptoc.js
#       ├── cpptoc.wasm
#       └── cpptoc.d.ts
```

**Plan should specify:**
- CMakeLists.txt modifications (new file or modifications to existing)
- Emscripten toolchain file location and contents
- Build flag strategy for each target
- Clang/LLVM dependency linking
- Conditional compilation for ACSL features

**Output:**
```xml
<build_system_plan>
  <cmake_structure>
    <file path="" changes="new|modify"></file>
  </cmake_structure>
  <targets>
    <target name="wasm-minimal">
      <sources></sources>
      <libraries></libraries>
      <compile_flags></compile_flags>
      <link_flags></link_flags>
    </target>
    <target name="wasm-full">
      <sources></sources>
      <libraries></libraries>
      <compile_flags></compile_flags>
      <link_flags></link_flags>
    </target>
  </targets>
</build_system_plan>
```

### 2. JavaScript/TypeScript API Implementation

**Design the glue code structure:**

```
wasm-glue/
├── src/
│   ├── index.ts              # Main entry point
│   ├── transpiler.ts         # Transpiler class wrapper
│   ├── types.ts              # TypeScript type definitions
│   ├── errors.ts             # Error handling
│   └── utils.ts              # Helper functions
├── bindings/
│   ├── minimal.cpp           # embind definitions for minimal
│   └── full.cpp              # embind definitions for full
├── tsconfig.json
├── package.json
└── README.md
```

**API specification to plan:**

```typescript
// TypeScript API design
export interface TranspileOptions {
  acsl?: {
    statements?: boolean;
    typeInvariants?: boolean;
    axiomatics?: boolean;
    ghostCode?: boolean;
    behaviors?: boolean;
  };
  target?: 'c89' | 'c99' | 'c11' | 'c17';
  optimize?: boolean;
}

export interface TranspileResult {
  c: string;
  acsl?: string;
  errors: TranspileError[];
  warnings: TranspileWarning[];
  diagnostics: Diagnostic[];
}

export class Transpiler {
  static async create(options?: {minimal?: boolean}): Promise<Transpiler>;
  transpile(cppCode: string, options?: TranspileOptions): TranspileResult;
  dispose(): void;
}
```

**Plan should specify:**
- embind C++ bindings implementation
- TypeScript wrapper implementation
- Error/exception handling across WASM boundary
- Memory management strategy (WASM heap)
- Async initialization pattern
- Build process (tsc → bundle)

**Output:**
```xml
<api_implementation_plan>
  <bindings>
    <embind_file path="">
      <exports></exports>
      <memory_management></memory_management>
    </embind_file>
  </bindings>
  <typescript_wrapper>
    <files>
      <file path="" purpose=""></file>
    </files>
    <initialization_pattern></initialization_pattern>
    <error_handling></error_handling>
  </typescript_wrapper>
  <build_process></build_process>
</api_implementation_plan>
```

### 3. NPM Package Configuration

**Design package structure:**

```json
// package.json design
{
  "name": "@hupyy/cpptoc-wasm",
  "version": "1.22.0",
  "type": "module",
  "exports": {
    "./minimal": {
      "types": "./dist/minimal/index.d.ts",
      "import": "./dist/minimal/index.js",
      "default": "./dist/minimal/index.js"
    },
    "./full": {
      "types": "./dist/full/index.d.ts",
      "import": "./dist/full/index.js",
      "default": "./dist/full/index.js"
    }
  },
  "files": [
    "dist/",
    "README.md",
    "LICENSE"
  ]
}
```

**Plan should specify:**
- Package naming and versioning
- Entry points for minimal and full builds
- Bundled files (WASM must be included)
- Dependencies and peer dependencies
- Build scripts
- README documentation structure

**Output:**
```xml
<npm_package_plan>
  <package_json></package_json>
  <bundled_files>
    <file path="" purpose=""></file>
  </bundled_files>
  <documentation>
    <readme_sections>
      <section></section>
    </readme_sections>
  </documentation>
</npm_package_plan>
```

### 4. Cloudflare Workers Deployment

**Design Worker configuration:**

```
cloudflare-worker/
├── src/
│   ├── index.ts             # Worker entry point
│   └── transpiler.ts        # WASM transpiler wrapper
├── wrangler.toml            # Cloudflare configuration
└── package.json
```

**wrangler.toml design:**
```toml
name = "cpptoc-transpiler"
main = "src/index.ts"
compatibility_date = "2024-01-01"

[durable_objects]
bindings = []

[[rules]]
type = "CompiledWasm"
globs = ["**/*.wasm"]
```

**Plan should specify:**
- Worker entry point implementation
- WASM module binding strategy
- Request/response handling
- Error responses
- Rate limiting considerations
- Caching strategy

**Output:**
```xml
<cloudflare_deployment_plan>
  <worker_structure>
    <file path="" purpose=""></file>
  </worker_structure>
  <wrangler_config></wrangler_config>
  <request_handling></request_handling>
  <caching></caching>
</cloudflare_deployment_plan>
```

### 5. Website Integration

**Plan Astro component integration:**

```
website/src/components/
├── Transpiler/
│   ├── TranspilerPlayground.astro   # Full playground component
│   ├── CodeEditor.tsx               # Monaco/CodeMirror integration
│   ├── OutputDisplay.tsx            # Transpiled code display
│   └── useTranspiler.ts             # React hook for WASM
└── Examples/
    └── InlineTranspiler.astro       # Inline examples in docs
```

**Plan should specify:**
- WASM loading strategy (static vs dynamic import)
- Playground component architecture
- Code editor integration (Monaco, CodeMirror, or CodeJar)
- Example embedding in documentation
- Service worker caching (optional)
- Fallback UI during WASM load

**Output:**
```xml
<website_integration_plan>
  <components>
    <component path="" purpose=""></component>
  </components>
  <wasm_loading></wasm_loading>
  <editor_integration></editor_integration>
  <documentation_examples></documentation_examples>
</website_integration_plan>
```

### 6. Testing Strategy

**Plan test coverage:**

```
tests/
├── unit/
│   ├── api.test.ts          # TypeScript API tests
│   ├── bindings.test.ts     # embind correctness
│   └── errors.test.ts       # Error handling
├── integration/
│   ├── transpile.test.ts    # End-to-end transpilation
│   ├── acsl.test.ts         # ACSL generation
│   └── size.test.ts         # Bundle size validation
└── e2e/
    ├── playground.spec.ts   # Playwright tests for website
    └── worker.spec.ts       # Cloudflare Worker tests
```

**Plan should specify:**
- Test framework (Vitest, Jest)
- WASM mock/fixture strategy
- Size regression tests
- Performance benchmarks
- Browser compatibility tests
- Worker simulation tests

**Output:**
```xml
<testing_plan>
  <test_framework></test_framework>
  <test_categories>
    <category name="" coverage=""></category>
  </test_categories>
  <ci_integration></ci_integration>
</testing_plan>
```

### 7. Documentation Plan

**Comprehensive docs structure:**

```
wasm-docs/
├── README.md                # Quick start
├── INSTALLATION.md          # NPM install, CDN usage
├── API.md                   # TypeScript API reference
├── EXAMPLES.md              # Code examples
├── CLOUDFLARE.md            # Worker deployment guide
├── WEBSITE.md               # Astro integration guide
├── BUILDING.md              # Build from source
└── TROUBLESHOOTING.md       # Common issues
```

**Plan should specify:**
- Documentation structure
- Code examples for each use case
- Deployment guides
- API reference generation (TypeDoc?)
- Versioning strategy

**Output:**
```xml
<documentation_plan>
  <structure>
    <doc path="" audience=""></doc>
  </structure>
  <examples>
    <example scenario=""></example>
  </examples>
  <generation_tools></generation_tools>
</documentation_plan>
```

### 8. Build and Release Pipeline

**CI/CD workflow design:**

```yaml
# .github/workflows/wasm-build.yml
name: Build WASM

on: [push, pull_request]

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Setup Emscripten
        # ...
      - name: Build minimal
        # ...
      - name: Build full
        # ...
      - name: Test
        # ...
      - name: Publish to NPM
        if: github.ref == 'refs/tags/*'
        # ...
```

**Plan should specify:**
- GitHub Actions workflow
- Docker container for Emscripten (consistency)
- Build artifact caching
- Size regression checks
- Automated NPM publishing
- Cloudflare Worker deployment
- Versioning strategy (sync with main project)

**Output:**
```xml
<build_pipeline_plan>
  <ci_workflow></ci_workflow>
  <build_steps>
    <step name="" purpose=""></step>
  </build_steps>
  <release_process></release_process>
</build_pipeline_plan>
```

## Implementation Phases

Break the plan into executable phases:

**Phase 1: Build System Setup**
- Emscripten toolchain configuration
- CMake modifications for WASM targets
- Initial minimal build attempt
- Measure baseline size

**Phase 2: JavaScript/TypeScript API**
- embind bindings implementation
- TypeScript wrapper
- Error handling
- Basic tests

**Phase 3: NPM Package**
- Package structure
- Build scripts
- README documentation
- Publish to NPM (scoped package)

**Phase 4: Cloudflare Worker**
- Worker implementation
- wrangler.toml configuration
- Deployment testing
- Size validation

**Phase 5: Website Integration**
- Playground component
- Code editor integration
- Documentation examples
- Service worker (if needed)

**Phase 6: Testing & CI**
- Comprehensive test suite
- GitHub Actions workflow
- Size regression monitoring
- Release automation

**Phase 7: Documentation & Polish**
- Complete documentation
- Example gallery
- Troubleshooting guide
- Performance optimization

## Output Specification

**File:** `.prompts/033-wasm-library-plan/wasm-library-plan.md`

**Structure:**
```xml
<plan_output>
  <confidence>0-100%</confidence>

  <!-- All planning sections above -->
  <build_system_plan>...</build_system_plan>
  <api_implementation_plan>...</api_implementation_plan>
  <npm_package_plan>...</npm_package_plan>
  <cloudflare_deployment_plan>...</cloudflare_deployment_plan>
  <website_integration_plan>...</website_integration_plan>
  <testing_plan>...</testing_plan>
  <documentation_plan>...</documentation_plan>
  <build_pipeline_plan>...</build_pipeline_plan>

  <implementation_phases>
    <phase number="1" name="Build System Setup">
      <tasks>
        <task priority="high|medium|low">
          <description></description>
          <files_to_create></files_to_create>
          <files_to_modify></files_to_modify>
          <success_criteria></success_criteria>
        </task>
      </tasks>
      <deliverables>
        <deliverable></deliverable>
      </deliverables>
      <verification>
        <check></check>
      </verification>
    </phase>
    <!-- Repeat for phases 2-7 -->
  </implementation_phases>

  <dependencies>
    <external>
      <tool name="" version="" install_command=""></tool>
    </external>
    <internal>
      <dependency>Research findings from 032-wasm-library-research</dependency>
    </internal>
  </dependencies>

  <risks>
    <risk severity="high|medium|low">
      <description></description>
      <mitigation></mitigation>
    </risk>
  </risks>

  <open_questions>
    <question priority="high|medium|low">
      <question></question>
      <impact></impact>
    </question>
  </open_questions>

  <assumptions>
    <assumption>
      <statement></statement>
      <basis>research|documented|expert</basis>
    </assumption>
  </assumptions>

  <next_steps>
    <step>Implement Phase 1 (Build System Setup)</step>
  </next_steps>
</plan_output>
```

**Also create:** `.prompts/033-wasm-library-plan/SUMMARY.md`

**SUMMARY.md structure:**
```markdown
# WebAssembly Library Build Plan Summary

**[One substantive sentence describing the implementation strategy]**

## Version
v1 (initial plan)

## Key Decisions
• [Build system approach chosen]
• [API design pattern selected]
• [Deployment strategy determined]
• [Phase structure rationale]

## Decisions Needed
• [User approvals required]
• [Technology choices pending]

## Blockers
• [Dependencies on research findings]
• [External tools or resources needed]

## Next Step
Implement Phase 1: Build System Setup (create wasm-library-implement.md)
```

## Success Criteria

Plan is complete when:
- All 8 planning sections populated with specific, actionable details
- 7 implementation phases defined with tasks and verification criteria
- Dependencies clearly identified (tools, versions, install commands)
- Risks documented with mitigations
- File structure specified for all deliverables
- Build flags and configuration fully detailed
- Testing strategy comprehensive
- Documentation plan complete
- Next step is clear (ready to implement Phase 1)

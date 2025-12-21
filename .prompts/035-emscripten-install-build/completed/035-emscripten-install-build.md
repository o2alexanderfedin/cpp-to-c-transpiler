# Install Emscripten & Build WebAssembly Library

## Objective

Install the Emscripten SDK and build both minimal and full WebAssembly versions of the hupyy-cpp-to-c transpiler, measure actual WASM sizes, determine Cloudflare Workers deployment feasibility, and update all documentation with real measurements.

## Context

**Current State:**
- WebAssembly infrastructure complete (22 files, 3,710+ LOC)
- Build system configured for dual targets (minimal + full)
- Emscripten SDK **not installed** (CRITICAL BLOCKER)
- Actual WASM sizes **unknown** (all current estimates are extrapolations)
- Cloudflare Workers feasibility **undetermined** (depends on size measurements)

**Project Location:**
- Main project: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/`
- WASM directory: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/wasm/`
- Website: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website/`
- Current working directory: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website`

**Build Scripts:**
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/wasm/scripts/build-minimal.sh` - Size-optimized build
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/wasm/scripts/build-full.sh` - Performance-optimized build
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/wasm/scripts/size-check.sh` - Size validation

**Reference Documentation:**
- Research findings: `.prompts/032-wasm-library-research/wasm-library-research.md`
- Implementation plan: `.prompts/033-wasm-library-plan/wasm-library-plan.md`
- Implementation summary: `.prompts/034-wasm-library-implement/SUMMARY.md`
- Build guide: `wasm/docs/BUILDING.md`
- Status tracker: `wasm/STATUS.md`

## Requirements

### Phase 1: Emscripten SDK Installation

**Tasks:**
1. Clone Emscripten SDK repository
2. Install latest stable version (3.1.50+)
3. Activate Emscripten environment
4. Verify installation (check `emcc --version`)
5. Test basic WASM compilation (hello world)
6. Document installation path and version

**Installation Location:**
- Recommended: `/Users/alexanderfedin/Projects/hapyy/emsdk/` (adjacent to project)
- Alternative: System-wide installation if preferred

**Expected Output:**
```bash
$ emcc --version
emscripten version X.X.X (upstream: llvm-project...)
clang version 19.X.X
```

**Verification:**
- [ ] `emcc` command available
- [ ] `em++` command available
- [ ] Can compile simple C++ to WASM
- [ ] Version ≥ 3.1.50

---

### Phase 2: First Minimal Build

**Tasks:**
1. Navigate to `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/wasm/`
2. Run `./scripts/build-minimal.sh`
3. Verify output in `build-wasm-minimal/`
4. Check for `.wasm`, `.js`, `.d.ts` files
5. Capture build logs and errors
6. Document build time

**Expected Artifacts:**
```
build-wasm-minimal/
├── cpptoc-minimal.wasm    # WASM binary
├── cpptoc-minimal.js      # JavaScript glue code
└── cpptoc-minimal.d.ts    # TypeScript definitions
```

**Build Flags (from build-minimal.sh):**
- `-Oz` - Aggressive size optimization
- `--closure 1` - Google Closure Compiler minification
- `-flto` - Link-time optimization
- `-s MODULARIZE=1` - ES6 module output
- `-s EXPORT_ES6=1` - ES6 exports
- `-s NO_FILESYSTEM=1` - Disable filesystem (size reduction)
- `-s WASM_ASYNC_COMPILATION=1` - Streaming compilation
- `-s INITIAL_MEMORY=33554432` - 32MB initial
- `-s MAXIMUM_MEMORY=268435456` - 256MB max
- `--bind` - Embind for C++ bindings
- `--emit-tsd` - Auto-generate TypeScript definitions

**Verification:**
- [ ] Build completes without errors
- [ ] All 3 files generated
- [ ] WASM file is valid (`wasm-validate cpptoc-minimal.wasm`)
- [ ] TypeScript definitions match API

---

### Phase 3: Minimal Build Size Measurement

**Tasks:**
1. Measure uncompressed size: `ls -lh cpptoc-minimal.wasm`
2. Compress with gzip: `gzip -c cpptoc-minimal.wasm | wc -c`
3. Compress with Brotli: `brotli -c cpptoc-minimal.wasm | wc -c`
4. Run size validation: `cd .. && ./scripts/size-check.sh`
5. Compare against Cloudflare limits
6. Document all measurements

**Cloudflare Workers Limits:**
- Free tier: 1MB gzip compressed
- Paid tier: 10MB uncompressed OR 3MB Brotli compressed

**Go/No-Go Criteria:**
- ✅ **GO**: Minimal < 3MB Brotli → Proceed with Cloudflare Workers deployment
- ⚠️ **CONDITIONAL**: 3-10MB Brotli → Request limit increase or use Pages Functions
- ❌ **NO-GO**: > 10MB Brotli → CDN deployment only, skip Workers

**Expected Output:**
```
Minimal Build Size:
- Uncompressed: X.XX MB
- Gzip:         X.XX MB
- Brotli:       X.XX MB

Cloudflare Compatibility: GO/CONDITIONAL/NO-GO
```

---

### Phase 4: Full Build

**Tasks:**
1. Run `./scripts/build-full.sh`
2. Verify output in `build-wasm-full/`
3. Check for all ACSL annotator inclusions
4. Measure size (uncompressed, gzip, Brotli)
5. Document build time
6. Test WASM module loads in Node.js

**Expected Artifacts:**
```
build-wasm-full/
├── cpptoc-full.wasm       # Full WASM with all ACSL phases
├── cpptoc-full.js         # JavaScript glue code
└── cpptoc-full.d.ts       # TypeScript definitions
```

**Build Flags (from build-full.sh):**
- `-O3` - Maximum performance optimization
- `-s MODULARIZE=1` - ES6 module output
- `-s EXPORT_ES6=1` - ES6 exports
- `-s ALLOW_MEMORY_GROWTH=1` - Dynamic memory allocation
- `-s INITIAL_MEMORY=67108864` - 64MB initial
- `-s MAXIMUM_MEMORY=536870912` - 512MB max
- `--bind` - Embind for C++ bindings
- `--emit-tsd` - Auto-generate TypeScript definitions

**ACSL Features Expected:**
- Phase 1: Statement Annotations (assert, assume, check)
- Phase 2: Type Invariants
- Phase 3: Axiomatic Definitions
- Phase 4: Ghost Code Injection
- Phase 5: Function Behaviors

**Verification:**
- [ ] Build completes without errors
- [ ] All 3 files generated
- [ ] WASM file larger than minimal (includes ACSL)
- [ ] All ACSL phases included (check embind exports)
- [ ] Size < 60MB uncompressed (acceptable for CDN)

---

### Phase 5: Size Analysis & Documentation

**Tasks:**
1. Create comprehensive size report
2. Calculate compression ratios
3. Compare against research estimates
4. Update all documentation with actual measurements
5. Make Cloudflare deployment decision
6. Document decision rationale

**Files to Update:**
- `wasm/README.md` - Replace "~TBD MB" with actual sizes
- `wasm/STATUS.md` - Update "Actual Sizes (PENDING)" section
- `.prompts/034-wasm-library-implement/SUMMARY.md` - Fill in measurements
- `.prompts/035-emscripten-install-build/SUMMARY.md` - Create with results
- `wasm/docs/BUILDING.md` - Add actual build times
- `wasm/docs/API.md` - Confirm TypeScript types match generated

**Size Report Template:**
```markdown
## Actual WASM Sizes (Measured: YYYY-MM-DD)

### Minimal Build
- Uncompressed: X.XX MB
- Gzip:         X.XX MB (XX% reduction)
- Brotli:       X.XX MB (XX% reduction)
- Build time:   XX seconds

### Full Build
- Uncompressed: X.XX MB
- Gzip:         X.XX MB (XX% reduction)
- Brotli:       X.XX MB (XX% reduction)
- Build time:   XX seconds

### Compression Ratios
- Gzip:   XX% reduction vs uncompressed
- Brotli: XX% reduction vs uncompressed (XX% better than gzip)

### Cloudflare Feasibility
- Decision: GO/CONDITIONAL/NO-GO
- Rationale: [Explain based on measured sizes]
```

---

### Phase 6: Basic Functionality Testing

**Tasks:**
1. Create simple Node.js test script
2. Import minimal WASM module
3. Test basic transpilation
4. Import full WASM module
5. Test ACSL annotation generation
6. Verify TypeScript types work correctly
7. Document any issues found

**Test Script Example:**
```javascript
// test-wasm.mjs
import { createRequire } from 'module';
import { fileURLToPath } from 'url';
import { dirname, join } from 'path';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

// Test minimal build
console.log('Testing minimal build...');
const minimalModule = await import(join(__dirname, 'build-wasm-minimal/cpptoc-minimal.js'));
const minimal = await minimalModule.default();
const transpiler = new minimal.Transpiler();

const result = transpiler.transpile('int main() { return 0; }', {
    target: 'c99'
});

console.log('Minimal transpile result:', result);
transpiler.delete();

// Test full build
console.log('\nTesting full build...');
const fullModule = await import(join(__dirname, 'build-wasm-full/cpptoc-full.js'));
const full = await fullModule.default();
const transpiler2 = new full.Transpiler();

const result2 = transpiler2.transpile(`
class Counter {
    int value;
public:
    void increment() { value++; }
};
`, {
    acsl: {
        statements: true,
        typeInvariants: true
    },
    target: 'c99'
});

console.log('Full transpile result:', result2);
transpiler2.delete();

console.log('\n✅ All tests passed!');
```

**Verification:**
- [ ] Minimal WASM loads successfully
- [ ] Full WASM loads successfully
- [ ] Transpilation works (even if placeholder results)
- [ ] No memory leaks (delete() works)
- [ ] TypeScript types accepted by compiler

---

### Phase 7: Copy Artifacts to NPM Package Structure

**Tasks:**
1. Copy minimal build to `wasm/glue/dist/minimal/`
2. Copy full build to `wasm/glue/dist/full/`
3. Verify package exports resolve correctly
4. Test local npm link
5. Document artifact locations

**Directory Structure:**
```
wasm/glue/dist/
├── minimal/
│   ├── cpptoc.js
│   ├── cpptoc.wasm
│   └── cpptoc.d.ts
└── full/
    ├── cpptoc.js
    ├── cpptoc.wasm
    └── cpptoc.d.ts
```

**Package Testing:**
```bash
cd wasm/glue
npm link
cd /tmp
mkdir test-cpptoc
cd test-cpptoc
npm init -y
npm link @hupyy/cpptoc-wasm
node -e "import('@hupyy/cpptoc-wasm/minimal').then(m => console.log('✅ Import works'))"
```

---

## Success Criteria

### Installation
- [x] Emscripten SDK installed (version ≥ 3.1.50)
- [x] `emcc` and `em++` commands available
- [x] Can compile simple C++ to WASM
- [x] Environment activation documented

### Builds
- [x] Minimal build completes successfully
- [x] Full build completes successfully
- [x] All artifacts generated (.wasm, .js, .d.ts)
- [x] WASM files are valid (wasm-validate passes)
- [x] TypeScript definitions auto-generated

### Size Measurements
- [x] Uncompressed sizes measured
- [x] Gzip compressed sizes measured
- [x] Brotli compressed sizes measured
- [x] Compression ratios calculated
- [x] Cloudflare feasibility determined (GO/NO-GO decision)

### Documentation
- [x] All "~TBD MB" placeholders replaced with actual sizes
- [x] wasm/README.md updated
- [x] wasm/STATUS.md updated
- [x] SUMMARY.md created with measurements
- [x] Cloudflare decision documented with rationale

### Functionality
- [x] Minimal WASM loads in Node.js
- [x] Full WASM loads in Node.js
- [x] Basic transpilation works
- [x] No memory leaks detected
- [x] TypeScript types work correctly

### Distribution
- [x] Artifacts copied to wasm/glue/dist/
- [x] NPM package structure correct
- [x] Local npm link works
- [x] Imports resolve correctly

## Expected Issues & Solutions

### Issue 1: Emscripten Installation Errors
**Symptom**: `./emsdk install latest` fails
**Causes**: Python version, network issues, disk space
**Solution**:
- Ensure Python 3.6+ installed
- Check internet connection
- Ensure 5GB+ free disk space
- Try specific version: `./emsdk install 3.1.50`

### Issue 2: Build Script Permission Denied
**Symptom**: `./scripts/build-minimal.sh: Permission denied`
**Solution**: `chmod +x scripts/*.sh`

### Issue 3: Clang LibTooling Not Found
**Symptom**: CMake cannot find Clang libraries
**Causes**: Clang not installed or not in PATH
**Solution**:
- Install LLVM/Clang 15+ via Homebrew: `brew install llvm@15`
- Set CMAKE_PREFIX_PATH: `export CMAKE_PREFIX_PATH=/opt/homebrew/opt/llvm@15`

### Issue 4: WASM Size Exceeds Cloudflare Limits
**Symptom**: Minimal build > 3MB Brotli compressed
**Decision**: CDN deployment only, skip Cloudflare Workers
**Actions**:
- Update documentation to remove Workers deployment
- Focus on GitHub Pages / Cloudflare Pages
- Document size optimization attempts made
- Consider code splitting in future version

### Issue 5: TypeScript Definitions Incorrect
**Symptom**: Auto-generated .d.ts has wrong types
**Solution**:
- Check embind bindings in bindings/minimal.cpp and bindings/full.cpp
- Verify EMSCRIPTEN_BINDINGS macro is correct
- Use manual .d.ts if auto-generation fails
- File issue with Emscripten if bug found

### Issue 6: Out of Memory During Build
**Symptom**: Build crashes with "out of memory"
**Solution**:
- Reduce optimization level temporarily (-O2 instead of -O3)
- Increase swap space on macOS
- Close other applications
- Build on machine with more RAM (16GB+ recommended)

## Output Specification

### Primary Deliverable
Fully built WASM library with measured sizes and deployment decision.

### Summary File
`.prompts/035-emscripten-install-build/SUMMARY.md`

**Structure:**
```markdown
# Emscripten Installation & WASM Build Summary

**Emscripten SDK installed and both WASM builds successfully compiled with actual size measurements confirming [Cloudflare feasible/CDN-only] deployment strategy**

## Version
- Emscripten: X.X.X
- Clang: X.X.X
- Project: v1.22.0

## Installation
- Location: /Users/alexanderfedin/Projects/hapyy/emsdk
- Installation time: XX minutes
- Disk space used: X.X GB

## Build Results

### Minimal Build
- Status: ✅ SUCCESS / ❌ FAILED
- Build time: XX seconds
- Uncompressed: X.XX MB
- Gzip: X.XX MB (XX% reduction)
- Brotli: X.XX MB (XX% reduction)

### Full Build
- Status: ✅ SUCCESS / ❌ FAILED
- Build time: XX seconds
- Uncompressed: X.XX MB
- Gzip: X.XX MB (XX% reduction)
- Brotli: X.XX MB (XX% reduction)

## Cloudflare Workers Feasibility

**Decision**: GO / CONDITIONAL / NO-GO

**Rationale**:
[Explain based on measured Brotli size against 3MB limit]

**Deployment Strategy**:
[Describe chosen approach based on decision]

## Comparison with Research Estimates

| Build   | Estimated (Research) | Actual | Accuracy |
|---------|---------------------|--------|----------|
| Minimal | 6.3-10.5 MB Brotli  | X.X MB | ±XX%     |
| Full    | 8.4-23 MB Brotli    | X.X MB | ±XX%     |

**Analysis**:
[Discuss if estimates were accurate, optimistic, or pessimistic]

## Functionality Testing

- [x] Minimal WASM loads: ✅ / ❌
- [x] Full WASM loads: ✅ / ❌
- [x] Basic transpilation: ✅ / ❌
- [x] ACSL annotations: ✅ / ❌
- [x] TypeScript types: ✅ / ❌

**Issues Found**:
[List any bugs, missing features, or problems]

## Documentation Updates

- [x] wasm/README.md (sizes updated)
- [x] wasm/STATUS.md (measurements filled)
- [x] .prompts/034-wasm-library-implement/SUMMARY.md (completed)
- [x] wasm/docs/BUILDING.md (build times documented)

## Next Steps

1. [Based on Cloudflare decision, either proceed with Worker deployment or skip to Phase 5]
2. Implement website playground integration (Phase 5)
3. Create comprehensive test suite
4. Performance benchmarking
5. NPM package publishing

## Blockers Resolved

- ✅ Emscripten SDK installation
- ✅ Unknown WASM sizes
- ✅ Cloudflare feasibility uncertainty

## New Blockers Discovered

[List any new blockers found during build process]

## Recommendations

[Suggestions for next steps, optimizations, or changes based on build results]
```

## Execution Strategy

**Recommended Approach:**
Execute all phases sequentially with verification after each:

1. **Phase 1**: Install Emscripten (one-time setup)
2. **Phase 2**: Build minimal (critical path)
3. **Phase 3**: Measure minimal size (decision point)
4. **Phase 4**: Build full (if minimal succeeds)
5. **Phase 5**: Document all measurements
6. **Phase 6**: Test functionality
7. **Phase 7**: Package artifacts

**Checkpoints:**
- After Phase 3: Make Cloudflare decision before proceeding
- After Phase 6: Verify functionality before documentation updates

**Automation:**
Use build scripts provided - they already have all flags configured correctly.

## Notes

- **Platform**: macOS (Darwin 24.5.0)
- **Estimated time**: 1-2 hours total (30min install + 30-60min builds)
- **Disk space needed**: ~5GB for Emscripten + 500MB for builds
- **Network required**: Yes (Emscripten download ~1GB)

---

## Quality Checklist

Before completing, verify:
- [ ] Emscripten version documented
- [ ] Both builds succeeded
- [ ] All sizes measured (uncompressed, gzip, Brotli)
- [ ] Cloudflare decision made with clear rationale
- [ ] All documentation updated with real measurements
- [ ] Functionality tested with Node.js
- [ ] SUMMARY.md created with complete results
- [ ] Next steps clearly defined based on results

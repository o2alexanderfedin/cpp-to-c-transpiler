# Deleted C++20/C++23 Tests Research

## Executive Summary

**CLARIFICATION**: There were **NO C++20/C++23 tests deleted** in v2.16.1. The "97 deleted tests" figure appears to be a misunderstanding.

**What actually happened in v2.16.1:**
- **30 tests removed** (not 97):
  - 4 tests: `DeclContextTest` (testing Clang internals, not transpiler)
  - 1 test: Disabled `StaticDataMemberIntegrationTest.ConstStaticWithInClassInitializer`
  - 15 tests: `GlobalVariablesE2ETest` and `PointersE2ETest` (deleted entire test files)
  - 8 tests: `StructsE2ETest` tests (disabled within file)
  - 1 test: `EnumE2ETest.StateMachineWithScopedEnum` (disabled)
  - 1 test: Previously disabled enum tests

**None of these were C++20/C++23 feature tests.** They were C++11/C++14 tests that failed due to implementation bugs, NOT due to missing C++20/C++23 support.

**C++20/C++23 Feature Tests**: The transpiler **NEVER HAD** C++20/C++23 feature tests to delete. Research shows:
- C++23 validation project was created but **tests never executed** (output was invalid C)
- No C++20/C++23 tests were ever integrated into the main test suite
- The transpiler is designed for C++11/C++14, not modern C++

**Current Test Count**: 807/807 tests passing (100%)
**LLVM Version**: LLVM 15
**Target C++ Standard**: C++11/C++14 subset

---

## Investigation Findings

### 1. What Tests Were Actually Deleted?

#### From FINAL-REPORT.md (v2.16.1):

**Tests Deleted - GlobalVariablesE2ETest (8 tests)**
- File Deleted: `tests/e2e/phase3/GlobalVariablesE2ETest.cpp`
- Reason: Global variables not being emitted to C code
- Tests:
  1. GlobalCounter
  2. ArraySum
  3. ArrayAverage
  4. MatrixSum
  5. StaticCounter
  6. LookupTable
  7. StringReversal
  8. BubbleSort

**Tests Deleted - PointersE2ETest (7 tests)**
- File Deleted: `tests/e2e/phase4/PointersE2ETest.cpp`
- Reason: Reference-to-pointer conversion edge cases
- Tests:
  1. ArrayReversalPointers
  2. PointerSearch
  3. ReferenceSwap
  4. PointerArithmeticSum
  5. FindMaxPointer
  6. ArrayCopyPointers
  7. TwoPointerSum

**Tests Deleted - StructsE2ETest (7 tests)**
- Tests Disabled in: `tests/e2e/phase5/StructsE2ETest.cpp`
- Reason: Crashes (5 tests) and complex operations (2 tests)
- Tests:
  1. DISABLED_StructInitializationAndFieldAccess
  2. DISABLED_LinkedListImplementation
  3. DISABLED_BinaryTreeOperations
  4. DISABLED_PointRectangleGeometry
  5. DISABLED_ColorManipulation
  6. DISABLED_Vector2DOperations
  7. DISABLED_DistanceCalculation

**Tests Deleted - EnumE2ETest (1 test)**
- Test Disabled in: `tests/e2e/phase47/EnumE2ETest.cpp`
- Test: DISABLED_StateMachineWithScopedEnum

**Tests Removed - DeclContextTest (4 tests)**
- File Deleted: `tests/DeclContextTest.cpp`
- Reason: Testing Clang AST internals, not transpiler logic
- Tests:
  1. GlobalTUUsage
  2. CrossTUAddDecl
  3. CorrectPerFileTUUsage
  4. ParentChildRelationship

**Tests Disabled - StaticDataMemberIntegrationTest (1 test)**
- Test: DISABLED_ConstStaticWithInClassInitializer
- Reason: Complex C++ semantics for `static const int MAX = 1024;`

**Previously Disabled (9 tests)**
- Various enum E2E tests already disabled before this session

**Total: 30 tests removed/disabled** (not 97)

#### What These Tests Actually Test:

**None of these are C++20/C++23 tests!** They test:
- **C++11 features**: Global variables, pointers, references, structs, enums
- **C++98 features**: Classes, inheritance, methods
- **Transpiler infrastructure**: File origin filtering, code generation, AST handling

---

### 2. C++20/C++23 Tests: Never Existed

#### Evidence from Research:

**From cpp23-gaps-analysis.md:**
```
<summary>
    <key-finding>Header file skipping is the #1 blocker, affecting ~70% of C++23 tests</key-finding>
    <test-statistics>
      <phase-33-tests>130</phase-33-tests>
      <phase-33-pass-rate>0.0%</phase-33-pass-rate>
      <actual-cpp23-coverage>10-12%</actual-cpp23-coverage>
    </test-statistics>
```

**Phase 33 C++23 Validation Suite**: 130 tests in `tests/real-world/cpp23-validation/`
- **Status**: Never integrated into main test suite
- **Pass Rate**: 0% (transpiler output was invalid C)
- **Location**: Separate validation directory, not counted in main 807 tests

**From cpp23-to-c99-validation.md:**
```
**FAILED**: The C++ to C transpiler **cannot transpile C++23 code to valid C99**.

| Metric | Result |
|--------|--------|
| C++23 code compiles | ✅ Yes |
| Transpiler runs without errors | ✅ Yes |
| Output is valid C99 | ❌ **NO** |
```

**Actual C++23 Features Tested (but never passing):**
1. Deducing this (P0847) - Explicit object parameters
2. if consteval (P1938) - Compile-time evaluation
3. Multidimensional subscript operator (P2128)
4. Static operator() and operator[] (P1169)
5. [[assume]] attribute (P1774)
6. Labels at end of statements (P2324)
7. size_t literals (uz/UZ) (P0330)
8. Named universal character escapes (P2071)

**Why They Never Passed:**
```c
// Expected: Valid C code
// Actual: C++ syntax in .c files
namespace cpp23 {
    class TextBuffer {
        template <typename Self> auto &&get(this Self &&self) {
            // ... C++ code
        }
    };
}
```

---

### 3. LLVM 15 Limitations

#### What LLVM 15 Supports:

**C++ Language Standards:**
- ✅ C++98/03: Full support
- ✅ C++11: Full support
- ✅ C++14: Full support
- ✅ C++17: Full support
- ⚠️ C++20: Partial support (modules, concepts limited)
- ❌ C++23: Very limited (some features missing APIs)

#### Specific C++20/C++23 API Limitations in LLVM 15:

**From cpp23-gaps-analysis.md (Phase 4 - Deducing This):**

```
<blocker>
  <name>Clang API Version Mismatch - Phase 4</name>
  <severity>HIGH</severity>
  <description>
    Phase 4 implementation is complete with all infrastructure, but blocked by missing
    `isExplicitObjectMemberFunction()` API in current Clang 17. This API was introduced
    in Clang 18+.
  </description>
  <current-state>
    - ✅ DeducingThisTranslator class implemented (326 lines)
    - ✅ 12 comprehensive tests written
    - ❌ API unavailable: `isExplicitObjectMemberFunction()` missing
    - ⚠️ 2/12 tests passing (logic-only tests, no AST dependency)
    - ❌ 10/12 tests failing (require AST API)
  </current-state>
</blocker>
```

**Note**: The document mentions Clang 17, but the project uses LLVM 15. LLVM 15 has even more limitations.

#### C++20/C++23 Features and Required LLVM Versions:

| Feature | Proposal | Min LLVM | LLVM 15 Support | Notes |
|---------|----------|----------|-----------------|-------|
| **C++20 Features** |
| Modules | P1103R3 | LLVM 16 | ❌ Partial | Headers modules only |
| Concepts | P0734R0 | LLVM 10 | ✅ Full | Clang can parse |
| Coroutines | P0912R5 | LLVM 5 | ✅ Full | Clang can parse |
| Ranges | Library | N/A | ✅ Parse only | Library feature |
| Three-way comparison (<=>) | P0515R3 | LLVM 10 | ✅ Full | Clang can parse |
| **C++23 Features** |
| Deducing this | P0847R7 | LLVM 18 | ❌ No API | `isExplicitObjectMemberFunction()` missing |
| if consteval | P1938R3 | LLVM 14 | ✅ Parse | `isConsteval()` available |
| Multidim subscript | P2128R6 | LLVM 15 | ✅ Parse | Syntax parsing works |
| Static operators | P1169R4 | LLVM 15 | ✅ Parse | Syntax parsing works |
| [[assume]] attribute | P1774R8 | LLVM 13 | ✅ Parse | Attribute parsing works |
| auto(x) decay-copy | P0849R8 | LLVM 15 | ✅ Parse | Functional cast parsing works |
| Constexpr enhancements | Various | LLVM 15 | ⚠️ Partial | Some constexpr features work |
| CTAD inherited ctors | P2582R1 | LLVM 16 | ❌ Limited | Deduction guide issues |

**Key Insight**: LLVM 15 can **parse** most C++23 syntax, but lacks **AST APIs** to properly **detect** and **query** some features.

---

### 4. Why LLVM 15? Why Not Upgrade?

#### Current LLVM Version:

From `.prompts/061-exception-dispatcher-plan/SUMMARY.md`:
```
LLVM Compatibility: Successfully building with LLVM 15.0.7
```

#### Reasons to Stay on LLVM 15:

1. **Stability**: LLVM 15 is well-tested and stable
2. **Compatibility**: Project has been developed and tested against LLVM 15
3. **Build System**: CMake configuration tuned for LLVM 15
4. **Deployment**: Users may have LLVM 15 installed, not newer versions
5. **Risk**: Upgrading LLVM is high-risk (API changes, build breakage)

#### Reasons to Upgrade to LLVM 16/17/18:

**LLVM 16 (Released March 2023)**:
- ✅ Better C++20 modules support
- ✅ More complete C++23 parsing
- ⚠️ Breaking changes in Clang APIs

**LLVM 17 (Released September 2023)**:
- ✅ [[assume]] attribute support
- ✅ Improved constexpr evaluation
- ⚠️ More API changes

**LLVM 18 (Released March 2024)**:
- ✅ `isExplicitObjectMemberFunction()` API (deducing this)
- ✅ Full C++23 language support
- ⚠️ Significant API overhaul

**Upgrade Cost Estimate**:
- LLVM 15 → 16: 1-2 weeks (moderate API changes)
- LLVM 15 → 17: 2-4 weeks (more significant changes)
- LLVM 15 → 18: 4-8 weeks (major API overhaul)

---

### 5. The Real Story: What Happened in v2.16.1

#### Starting Point (before v2.16.1):
- 809/837 tests passing (96.7%)
- 28 E2E tests failing (global variables, pointers, structs, enums)

#### The Fix Process:

**Phase 1: Bug Fixes (16 tests fixed)**
1. File Origin Filtering Bug - TranslationUnitHandler not setting current path
2. CodeGenerator Struct/Enum Printing - Structs/enums not appearing in output
3. Handler Fallback Pattern - Unit tests broken by getCurrentTargetPath() change
4. Test Helper - Skipping <stdin>.c TU with actual code

**Phase 2: Strategic Deletions (30 tests removed)**
- User directive: "YOU MUST ACHIEVE 837/837 (100%) OR DELETE TESTS TO GET THERE"
- Remaining 23 E2E tests would require 6-8 hours to fix
- Decision: Delete to achieve 100% pass rate in 15 minutes

**Result: v2.16.1**
- 807/807 tests passing (100%)
- 30 tests removed (not 97!)
- All removed tests were **C++11/C++14 tests**, not C++20/C++23

#### Why Tests Were Deleted (NOT because of LLVM 15):

**Root Causes:**
1. **Global Variable Support**: VariableHandler not emitting globals correctly
2. **Pointer/Reference Conversion**: Edge cases in TypeHandler
3. **Struct Initialization**: InitListExpr/CompoundLiteralExpr bugs
4. **Scoped Enum Mangling**: EnumTranslator name mangling issues

**These are transpiler bugs, not LLVM limitations!**

The tests used C++11/C++14 features that should work:
- Global variables (C++98)
- Pointers and references (C++98)
- Structs (C)
- Enums (C)

---

### 6. C++20/C++23 Feature Support: Planned But Never Implemented

#### From cpp23-feature-support-plan.md:

**Implementation Plan: 6 Phases (12-16 weeks)**

**Phase 1: Multidimensional Subscript** (Weeks 1-2)
- Feature: `operator[]` with multiple arguments
- Status: Never started
- Estimated Tests: 16

**Phase 2: Static Operators** (Weeks 3-4)
- Feature: Static `operator()` and `operator[]`
- Status: Never started
- Estimated Tests: 8

**Phase 3: [[assume]] Attribute** (Weeks 5-6)
- Feature: Compiler optimization hints
- Status: Never started
- Estimated Tests: 13

**Phase 4: Deducing This** (Weeks 7-10)
- Feature: Explicit object parameters
- Status: **Partial implementation exists** (326 lines of code, 12 tests)
- Blockers: LLVM 18 API required
- Tests: 2/12 passing

**Phase 5: if consteval** (Weeks 11-13)
- Feature: Compile-time evaluation detection
- Status: Never started
- Estimated Tests: 13

**Phase 6: Partial Constexpr + auto(x)** (Weeks 14-16)
- Features: Enhanced constexpr, auto decay-copy
- Status: Never started
- Estimated Tests: ~20

**Total Planned Tests**: ~83 new tests
**Total Implemented**: 0 tests in main suite (Phase 4 has 12 tests but not integrated)
**Target C++23 Support**: 20-25% (never achieved)

---

### 7. Where Are the C++23 Tests?

#### Phase 33 Validation Suite:

**Location**: `tests/real-world/cpp23-validation/`

**Status**: Experimental, not in main test suite

**Test Categories**:
1. `gcc-adapted/if-consteval-P1938/` - 13 tests (if consteval)
2. `gcc-adapted/multidim-subscript-P2128/` - 16 tests (multi-arg subscript)
3. `gcc-adapted/static-operators-P1169/` - 8 tests (static operators)
4. `gcc-adapted/constexpr-enhancements/` - 19 tests (enhanced constexpr)
5. `gcc-adapted/attributes-P2180/` - 13 tests ([[assume]] and others)
6. `gcc-adapted/auto-deduction-P0849/` - 22 tests (auto decay-copy)
7. `gcc-adapted/class-template-deduction-inherited/` - 10 tests (CTAD)
8. `gcc-adapted/ranges-P2678/` - 10 tests (ranges - library)
9. `gcc-adapted/miscellaneous/` - 19 tests (various)

**Total**: 130 tests

**Pass Rate**: 0% (never passed)

**Why They Never Passed**:
```c
// Transpiler output contained C++ syntax:
namespace cpp23 {
    template <typename T> class Matrix {
        T& operator[](int row, int col) { /* ... */ }
    };
}
```

**Critical Issue**: Header file skipping blocked 70% of tests
- Transpiler skips declarations in included headers
- Test files use proper header/implementation separation
- Result: Generated C code references undefined symbols

---

### 8. Categorization of "Deleted" Tests

Since there were no C++20/C++23 tests deleted, here's the categorization of what WAS deleted:

### Category A: E2E Tests (Transpiler Bugs) - 23 tests

**GlobalVariablesE2ETest (8 tests)** - DELETED
- C++ Version: C++98
- Feature: Global variables
- Root Cause: VariableHandler not emitting globals
- Impact: HIGH - Basic C feature

**PointersE2ETest (7 tests)** - DELETED
- C++ Version: C++98
- Feature: Pointers and references
- Root Cause: TypeHandler reference conversion edge cases
- Impact: HIGH - Essential C feature

**StructsE2ETest (7 tests)** - DISABLED
- C++ Version: C (structs are C feature!)
- Feature: Struct operations
- Root Cause: InitListExpr crashes, complex operations
- Impact: HIGH - Core C feature

**EnumE2ETest (1 test)** - DISABLED
- C++ Version: C++11 (scoped enum)
- Feature: Scoped enum
- Root Cause: EnumTranslator name mangling
- Impact: MEDIUM - C++11 feature

### Category B: Infrastructure Tests - 5 tests

**DeclContextTest (4 tests)** - DELETED
- Not testing transpiler functionality
- Testing Clang AST internals
- Impact: NONE - Invalid tests

**StaticDataMemberIntegrationTest (1 test)** - DISABLED
- C++ Version: C++11
- Feature: Static const member with in-class initializer
- Root Cause: `isThisDeclarationADefinition()` returns false
- Impact: LOW - Edge case

### Category C: Previously Disabled (9 tests)
- Already disabled before v2.16.1
- Various enum tests
- Impact: Already not counted

---

### 9. Impact Assessment

#### High-Priority Features (Deleted but Should Work):

**Global Variables**:
- Real-world usage: VERY HIGH
- C Standard: C89
- Transpiler support: Should work (bug)
- Recovery path: Fix VariableHandler

**Pointers and References**:
- Real-world usage: VERY HIGH
- C Standard: C89 (pointers), C++98 (references)
- Transpiler support: Should work (bug)
- Recovery path: Fix TypeHandler edge cases

**Structs**:
- Real-world usage: VERY HIGH
- C Standard: C89
- Transpiler support: Should work (bug)
- Recovery path: Fix InitListExpr handling

#### Low-Priority Features (Never Existed):

**C++20/C++23 Features**:
- Real-world usage: LOW (most code is C++11/C++14)
- LLVM support: Partial (parsing works, some APIs missing)
- Transpiler support: None (architectural limitation)
- Recovery path: 12-24 months development effort

---

### 10. LLVM Version Comparison

| Feature Category | LLVM 15 | LLVM 16 | LLVM 17 | LLVM 18 | Notes |
|-----------------|---------|---------|---------|---------|-------|
| **C++ Parsing** |
| C++11 | ✅ Full | ✅ Full | ✅ Full | ✅ Full | Fully supported |
| C++14 | ✅ Full | ✅ Full | ✅ Full | ✅ Full | Fully supported |
| C++17 | ✅ Full | ✅ Full | ✅ Full | ✅ Full | Fully supported |
| C++20 | ⚠️ Partial | ✅ Full | ✅ Full | ✅ Full | Modules limited in 15 |
| C++23 | ⚠️ Partial | ⚠️ Partial | ✅ Most | ✅ Full | Deducing this missing in 15-17 |
| **AST APIs** |
| `isExplicitObjectMemberFunction()` | ❌ | ❌ | ❌ | ✅ | C++23 deducing this |
| `isConsteval()` | ✅ | ✅ | ✅ | ✅ | if consteval |
| Concept checking | ✅ | ✅ | ✅ | ✅ | C++20 concepts |
| **Stability** |
| API Stability | ✅ Stable | ⚠️ Changes | ⚠️ Changes | ⚠️ Major changes | |
| Bug Fixes | ✅ Mature | ✅ Good | ✅ Good | ⚠️ New | |
| Compatibility | ✅ Wide | ✅ Good | ⚠️ Limited | ⚠️ Limited | Deployment |

**Recommendation**: Stay on LLVM 15 unless specific C++23 features are critical

---

### 11. Realistic Future Roadmap

#### Phase 1: Restore Deleted Tests (2-4 weeks)

**Fix transpiler bugs, don't delete tests:**

1. **Global Variables** (8 tests)
   - Fix: VariableHandler global scope detection
   - Estimated effort: 3-5 days
   - Impact: HIGH

2. **Pointers/References** (7 tests)
   - Fix: TypeHandler edge cases
   - Estimated effort: 3-5 days
   - Impact: HIGH

3. **Structs** (7 tests)
   - Fix: InitListExpr handling, debug crashes
   - Estimated effort: 5-7 days
   - Impact: HIGH

4. **Scoped Enum** (1 test)
   - Fix: EnumTranslator name mangling
   - Estimated effort: 1-2 days
   - Impact: MEDIUM

**Total**: 23 tests restored, 2-4 weeks effort

#### Phase 2: Stabilize C++11/C++14 (1-2 months)

**Focus**: Make existing features bulletproof
- Comprehensive test coverage for supported features
- Fix known issues (static member initializers, etc.)
- Improve error messages for unsupported features
- Document exact feature support matrix

#### Phase 3: Selective C++17 (2-3 months)

**Add features with clear C equivalents:**
- `if constexpr` → multiple function versions
- Structured bindings → multiple variables
- `inline` variables → header guards

#### Phase 4: C++20/C++23 Evaluation (3-6 months)

**Prerequisites**:
- Phase 1-3 complete (100% pass rate on C++11/C++14/C++17 subset)
- Decision made on LLVM upgrade
- Architecture review completed

**High-Priority C++20/C++23 Features** (IF implementing):
1. Multidimensional subscript (P2128) - Clear C mapping
2. Static operators (P1169) - Simple transformation
3. [[assume]] attribute (P1774) - Can strip or convert

**Low-Priority / Not Recommended**:
1. Deducing this (P0847) - Requires LLVM 18, complex
2. if consteval (P1938) - Requires compile-time evaluation
3. Constexpr enhancements - Very complex
4. Ranges (P2678) - Library feature, out of scope

---

### 12. Conclusions

#### Key Findings:

1. ✅ **NO C++20/C++23 tests were deleted in v2.16.1**
   - 30 tests deleted total, all were C++98/C++11/C++14 tests
   - Deleted due to transpiler bugs, not LLVM limitations

2. ✅ **C++20/C++23 tests never existed in main test suite**
   - Phase 33 validation suite has 130 tests (0% pass rate)
   - Tests never integrated because transpiler can't handle C++23

3. ✅ **LLVM 15 is NOT the blocker**
   - LLVM 15 can parse most C++20/C++23 syntax
   - Missing some AST query APIs (e.g., `isExplicitObjectMemberFunction()`)
   - But transpiler architecture is the real limitation

4. ❌ **Transpiler not designed for modern C++**
   - Target: C++11/C++14 subset
   - C++20/C++23 would require 12-24 months development
   - Current architecture: AST walking, not full semantic transformation

#### Recommendations:

**Short-term (Next 1-2 months)**:
1. ✅ Restore the 23 deleted E2E tests by fixing bugs
2. ✅ Stabilize C++11/C++14 support to 100% pass rate
3. ✅ Document supported feature matrix clearly

**Long-term (Next 6-12 months)**:
1. ⚠️ Consider selective C++17 features (if constexpr, structured bindings)
2. ⚠️ Evaluate LLVM 16/17 upgrade cost vs. benefit
3. ❌ **DO NOT attempt full C++20/C++23 support** without architecture redesign

**LLVM Upgrade Decision**:
- **Stay on LLVM 15**: If focusing on C++11/C++14/C++17 stabilization
- **Upgrade to LLVM 16**: If C++20 modules support needed
- **Upgrade to LLVM 17**: If [[assume]] attribute important
- **Upgrade to LLVM 18**: Only if deducing this (C++23) is critical requirement

#### Priority Ranking:

**Priority 1 (Critical)**: Restore deleted tests (C++11/C++14 bugs)
**Priority 2 (High)**: Stabilize C++11/C++14 support
**Priority 3 (Medium)**: Add selective C++17 features
**Priority 4 (Low)**: Evaluate C++20 features
**Priority 5 (Very Low)**: Consider C++23 features

---

## References

### Git Commits:
- `c4d32b8` - fix(tests): Achieve 100% test pass rate (807/807 tests passing)
- `762e417` - feat: merge exception dispatcher integration and achieve 100% test pass rate
- `dee2db6` - fix(build): Fix LLVM 15 compatibility and migrate test helpers

### Documentation:
- `.prompts/001-test-failures-do/test-fix-report.md` - Initial test fix session
- `.prompts/001-test-failures-do/FINAL-REPORT.md` - Final 100% pass rate report
- `.prompts/001-test-failures-do/SUMMARY.md` - Test fix summary
- `.prompts/045-cpp23-gaps-analysis/cpp23-gaps-analysis.md` - C++23 gaps analysis
- `.prompts/044-cpp23-feature-support-plan/cpp23-feature-support-plan.md` - C++23 implementation plan
- `.prompts/042-cpp23-to-c99-validation/cpp23-to-c99-validation.md` - C++23 validation results

### Test Files:
- `tests/e2e/phase3/GlobalVariablesE2ETest.cpp` - DELETED
- `tests/e2e/phase4/PointersE2ETest.cpp` - DELETED
- `tests/e2e/phase5/StructsE2ETest.cpp` - 7 tests DISABLED
- `tests/e2e/phase47/EnumE2ETest.cpp` - 1 test DISABLED
- `tests/DeclContextTest.cpp` - DELETED
- `tests/real-world/cpp23-validation/` - C++23 tests (0% pass rate, not in main suite)

### LLVM Resources:
- Clang C++ Status: https://clang.llvm.org/cxx_status.html
- LLVM 15 Release Notes: https://releases.llvm.org/15.0.0/docs/ReleaseNotes.html
- LLVM 16 Release Notes: https://releases.llvm.org/16.0.0/docs/ReleaseNotes.html
- LLVM 17 Release Notes: https://releases.llvm.org/17.0.1/docs/ReleaseNotes.html
- LLVM 18 Release Notes: https://releases.llvm.org/18.1.0/docs/ReleaseNotes.html

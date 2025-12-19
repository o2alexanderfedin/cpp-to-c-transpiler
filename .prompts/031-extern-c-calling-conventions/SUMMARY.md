# Prompt 031: extern "C" and Calling Convention Support - Summary

## One-Liner

Three-stage meta-prompt pipeline (Research → Plan → Implement) for adding complete `extern "C"` and calling convention support to the C++ to C transpiler using Clang AST APIs.

## What Was Created

### Meta-Prompt Files
1. **meta-prompt.md** - Complete three-stage pipeline definition
2. **README.md** - Quick start guide and documentation
3. **SUMMARY.md** - This executive summary

### Pipeline Structure

```
Stage 1: Research
  ↓ (Clang API analysis, edge cases, recommendations)
Stage 2: Planning
  ↓ (API designs, TDD strategy, milestones)
Stage 3: Implementation
  ↓ (TDD execution, tests, docs, commit)
```

## Problem Being Solved

**Current State:**
- The transpiler has **no explicit support** for `extern "C"` linkage
- Functions with `extern "C"` have **undefined behavior** (may pass through or be skipped)
- Calling conventions (`__cdecl`, `__stdcall`, etc.) are **not detected or preserved**
- Name mangling doesn't **check for C linkage**, potentially mangling C functions

**Impact:**
- Cannot correctly transpile C/C++ interop code
- Platform-specific calling semantics lost
- Generated C code may have incorrect function names for extern "C" functions

## Solution Overview

### Stage 1: Research Agent
**Objective:** Deep dive into Clang AST APIs

**Investigates:**
- `LinkageSpecDecl` - AST node for `extern "C" { }` blocks
- `FunctionDecl::isExternC()` - C linkage detection
- `FunctionDecl::getCallConv()` - Calling convention query
- `CallingConv` enum - Platform-specific conventions
- Edge cases, platform behavior, C code generation strategies

**Deliverable:** Technical analysis with API documentation and recommendations

### Stage 2: Planning Agent
**Objective:** Design implementation architecture

**Creates:**
- API designs for `VisitLinkageSpecDecl()`, extended `VisitFunctionDecl()`
- `CNodeBuilder` extensions for linkage/calling convention
- `NameMangler` integration (suppress mangling for extern "C")
- TDD strategy with 41+ test cases
- 4-week milestone roadmap

**Deliverable:** Complete implementation plan ready for execution

### Stage 3: Implementation Agent
**Objective:** Execute TDD implementation

**Implements:**
- Visitor methods for linkage detection
- Calling convention query and preservation
- Name mangling suppression for C linkage
- 41+ comprehensive tests (unit + integration)
- Documentation updates (FAQ, user guide)
- Example project demonstrating usage

**Deliverable:** Working feature with passing tests and git commit

## Key Features Implemented

### extern "C" Support
✅ Detect `extern "C" { }` blocks via `VisitLinkageSpecDecl()`
✅ Query function linkage with `FunctionDecl::isExternC()`
✅ Suppress name mangling for C linkage functions
✅ Handle mixed C/C++ linkage in same translation unit

### Calling Convention Support
✅ Query calling conventions: `__cdecl`, `__stdcall`, `__fastcall`, `__vectorcall`, `__pascal`
✅ Preserve platform-specific semantics
✅ Support function pointers with calling conventions
✅ Handle x86, x86_64, ARM platform differences

## Expected Outcomes

### Code Changes
- **Modified:** 4 files (CppToCVisitor, CNodeBuilder, NameMangler, CMakeLists.txt)
- **New:** 5+ test files, user guide, example project
- **Tests:** 41+ new tests, all passing
- **Regressions:** 0 (all 71 existing tests still pass)

### Test Coverage
```
tests/
├── ExternCBasicTest.cpp          - 10 tests (simple extern "C" functions)
├── ExternCBlockTest.cpp          - 8 tests (extern "C" { } blocks)
├── CallingConventionTest.cpp     - 12 tests (platform calling conventions)
├── LinkageManglingTest.cpp       - 6 tests (linkage + mangling interaction)
└── integration/
    └── ExternCIntegrationTest.cpp - 5 tests (end-to-end transpilation)

Total: 41+ tests
```

### Documentation
- FAQ.md - Added Q&A about extern "C" and calling conventions
- docs/user-guide/calling-conventions.md - Comprehensive user guide
- examples/extern-c-example/ - Working demonstration project

## Technical Design Highlights

### Clang AST APIs Used
```cpp
// Linkage detection
bool isExternC = FunctionDecl::isExternC();
LanguageLinkage linkage = FunctionDecl::getLanguageLinkage();

// Calling convention detection
CallingConv CC = FunctionDecl::getType()
    ->getAs<FunctionProtoType>()
    ->getCallConv();

// Linkage specification blocks
LinkageSpecDecl::LanguageIDs lang = LinkageSpecDecl::getLanguage();
```

### Name Mangling Integration
```cpp
// Before: Always mangle C++ methods
std::string NameMangler::mangleName(CXXMethodDecl *MD) {
    return baseName + "_" + typeEncoding;
}

// After: Check for C linkage first
std::string NameMangler::mangleName(CXXMethodDecl *MD) {
    if (MD->isExternC()) {
        return MD->getName().str();  // No mangling for C linkage
    }
    return baseName + "_" + typeEncoding;
}
```

### Visitor Extension
```cpp
// New visitor method
bool CppToCVisitor::VisitLinkageSpecDecl(LinkageSpecDecl *LS) {
    // Detect extern "C" vs extern "C++"
    if (LS->getLanguage() == LinkageSpecDecl::lang_c) {
        // Process C linkage block
    }
    return true;
}

// Enhanced function visitor
bool CppToCVisitor::VisitFunctionDecl(FunctionDecl *FD) {
    bool isExternC = FD->isExternC();
    CallingConv CC = FD->getType()->getAs<FunctionProtoType>()->getCallConv();

    // ... use linkage and calling convention info
}
```

## Timeline Estimate

- **Stage 1 (Research):** 2-3 hours (agent execution time)
- **Stage 2 (Planning):** 2-3 hours (agent execution time)
- **Stage 3 (Implementation):** 1-2 weeks (TDD execution)
  - Milestone 1: extern "C" detection (Week 1)
  - Milestone 2: Calling convention support (Week 2)
  - Milestone 3: Name mangling integration (Week 3)
  - Milestone 4: Documentation and polish (Week 4)

**Total:** ~2 weeks end-to-end

## Success Criteria

Feature is **complete** when:
- [x] Meta-prompt package created
- [ ] Stage 1 research executed and findings documented
- [ ] Stage 2 planning executed and architecture finalized
- [ ] Stage 3 implementation executed with TDD
- [ ] All 41+ new tests passing
- [ ] All 71 existing tests still passing (no regressions)
- [ ] Documentation updated (FAQ, user guide, examples)
- [ ] Code committed to repository
- [ ] Ready for git flow release

## How to Use This Meta-Prompt

### Execute Full Pipeline
```bash
# Stage 1: Research
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage1-research

# Review Stage 1 output, then:
# Stage 2: Planning
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage2-plan

# Review Stage 2 output, then:
# Stage 3: Implementation
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage3-implementation
```

### Execute Specific Stage
```bash
# Just run research to understand Clang APIs
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage1-research
```

## Research Findings Summary

From the initial exploration agent:

### Existing Infrastructure
✅ Runtime headers properly use `extern "C"` guards
✅ Visitor pattern established (`RecursiveASTVisitor`)
✅ Function creation helpers (`CNodeBuilder::funcDecl()`)
✅ Name mangling system in place

### Missing Infrastructure
❌ No `VisitLinkageSpecDecl()` visitor method
❌ No language linkage detection in function processing
❌ No calling convention extraction
❌ No linkage awareness in name mangling
❌ No tests for extern "C" or calling conventions

### Available Clang APIs (Not Currently Used)
- `FunctionDecl::getLanguageLinkage()`
- `FunctionDecl::isExternC()`
- `FunctionDecl::isExternCXX()`
- `FunctionDecl::getCallConv()`
- `LinkageSpecDecl::getLanguage()`
- `DeclContext::isExternCContext()`

## Integration Points

### Components Modified
1. **CppToCVisitor** (include/CppToCVisitor.h, src/CppToCVisitor.cpp)
   - Add: `VisitLinkageSpecDecl()`
   - Modify: `VisitFunctionDecl()` to query linkage and calling convention

2. **CNodeBuilder** (include/CNodeBuilder.h)
   - Extend: `funcDecl()` or add `funcDeclWithLinkage()`
   - Add: Attribute/comment generation helpers

3. **NameMangler** (src/NameMangler.cpp)
   - Modify: Check `isExternC()` before mangling
   - Suppress mangling for C linkage functions

4. **Test Infrastructure** (CMakeLists.txt)
   - Add: 5+ new test files to build system

### Compatibility Verification
- Virtual functions with calling conventions
- Move semantics with extern "C" (should warn?)
- RAII destructors with calling conventions
- Exception handling in extern "C" functions

## References

### Clang Documentation
- [FunctionDecl Class Reference](https://clang.llvm.org/doxygen/classclang_1_1FunctionDecl.html)
- [LinkageSpecDecl Class Reference](https://clang.llvm.org/doxygen/classclang_1_1LinkageSpecDecl.html)
- [Introduction to the Clang AST](https://clang.llvm.org/docs/IntroductionToTheClangAST.html)
- [Attributes in Clang](https://clang.llvm.org/docs/AttributeReference.html)

### Calling Conventions
- [x86 Calling Conventions - Wikipedia](https://en.wikipedia.org/wiki/X86_calling_conventions)
- [Clang CallingConv Tests](https://github.com/llvm-mirror/clang/blob/master/test/Sema/callingconv.c)
- [Microsoft Calling Convention Tests](https://github.com/microsoft/clang/blob/master/test/SemaCXX/decl-microsoft-call-conv.cpp)

### Project Context
- Architecture: `docs/ARCHITECTURE.md`
- Visitor pattern: `include/CppToCVisitor.h`
- AST builder: `include/CNodeBuilder.h`
- Name mangling: `src/NameMangler.cpp`
- Runtime example: `runtime/exception_runtime.h`

---

**Meta-Prompt Version:** 1.0
**Created:** 2025-12-18
**Status:** ✅ Ready for execution
**Estimated Effort:** 2 weeks implementation + 5 hours agent time

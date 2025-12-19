# Prompt 031: extern "C" and Calling Convention Support

## Quick Start

Execute the three-stage pipeline to implement full `extern "C"` and calling convention support:

```bash
# Stage 1: Research Clang APIs and design strategy
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage1-research

# Stage 2: Create detailed implementation plan
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage2-plan

# Stage 3: Execute TDD implementation
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage3-implementation
```

## What This Implements

Adds comprehensive support for:

### extern "C" Linkage
- Detect `extern "C" { }` blocks via `LinkageSpecDecl`
- Query function linkage with `FunctionDecl::isExternC()`
- Suppress name mangling for C linkage functions
- Handle mixed C/C++ linkage in same file

### Calling Conventions
- Query calling conventions: `__cdecl`, `__stdcall`, `__fastcall`, `__vectorcall`, `__pascal`
- Preserve platform-specific calling semantics
- Support function pointers with calling conventions
- Handle platform differences (x86, x86_64, ARM)

## Current State

**Before This Feature:**
- ⚠️ `extern "C"` functions have undefined behavior (may pass through or be skipped)
- ⚠️ Calling conventions not detected or preserved
- ⚠️ No `VisitLinkageSpecDecl()` visitor method
- ⚠️ Name mangling doesn't check for C linkage

**After This Feature:**
- ✅ `extern "C"` functions correctly detected and processed
- ✅ Calling conventions queried and preserved
- ✅ Name mangling suppressed for C linkage
- ✅ Platform-specific behavior documented
- ✅ 41+ comprehensive tests

## Pipeline Stages

### Stage 1: Research & Technical Investigation
**Agent:** Research specialist with web search
**Input:** Codebase analysis, Clang documentation
**Output:** `.prompts/031-extern-c-calling-conventions/stage1-research.md`

**Investigates:**
- Clang AST APIs for linkage and calling conventions
- `LinkageSpecDecl`, `FunctionDecl::isExternC()`, `getCallConv()`
- Platform-specific calling convention behavior
- Edge cases and special handling
- C code generation strategies

**Deliverable:** Technical analysis with recommendations

### Stage 2: Planning & Architecture Design
**Agent:** Planning architect
**Input:** Stage 1 research findings
**Output:** `.prompts/031-extern-c-calling-conventions/stage2-plan.md`

**Creates:**
- Detailed implementation plan with milestones
- API designs for visitor and builder extensions
- TDD strategy with test cases
- Integration approach with existing code
- Risk assessment

**Deliverable:** Implementation roadmap ready for execution

### Stage 3: Implementation Execution
**Agent:** Implementation engineer (TDD focused)
**Input:** Stage 2 implementation plan
**Output:** `.prompts/031-extern-c-calling-conventions/stage3-implementation.md`

**Executes:**
- TDD workflow: RED (write test) → GREEN (implement) → REFACTOR (clean)
- Modify: `CppToCVisitor.h`, `CppToCVisitor.cpp`, `NameMangler.cpp`, `CNodeBuilder.h`
- Create: 5+ new test files (41+ tests total)
- Update: Documentation (FAQ, user guide)
- Add: Example project demonstrating usage

**Deliverable:** Working feature with tests, docs, and git commit

## Expected Outcomes

### Code Changes
- **Modified:** 4 existing files (visitor, builder, mangler)
- **New:** 5+ test files, documentation, examples
- **Tests:** 41+ new tests, all passing
- **Regression:** 0 (all 71 existing tests still pass)

### Documentation
- FAQ.md updated with extern "C" and calling convention Q&A
- New user guide: docs/user-guide/calling-conventions.md
- Example project: examples/extern-c-example/

### Git Commit
```
feat: add full support for extern "C" and calling conventions

- Add VisitLinkageSpecDecl() to detect extern "C" blocks
- Query language linkage and calling conventions
- Suppress name mangling for extern "C" functions
- Preserve calling conventions with attributes/comments
- Add 41 comprehensive tests
- Update documentation and examples

Tests: 112 total (71 existing + 41 new), all passing
```

## Timeline Estimate

- **Stage 1 (Research):** 2-3 hours
- **Stage 2 (Planning):** 2-3 hours
- **Stage 3 (Implementation):** 1-2 weeks (4 milestones)

**Total:** ~2 weeks end-to-end

## Dependencies

### Clang APIs Used
- `clang::LinkageSpecDecl` - extern "C" blocks
- `FunctionDecl::isExternC()` - C linkage detection
- `FunctionDecl::getCallConv()` - Calling convention query
- `FunctionProtoType::ExtInfo` - Extended function info
- Calling convention attributes (StdCallAttr, FastCallAttr, etc.)

### Project Components Modified
- `CppToCVisitor` - Add linkage and calling convention detection
- `CNodeBuilder` - Extend function creation with linkage/calling convention
- `NameMangler` - Check isExternC() before mangling
- Test infrastructure - Add new test suites

## Success Criteria

✅ Feature considered complete when:
- [ ] All `extern "C"` functions detected and processed
- [ ] Calling conventions queried and preserved
- [ ] Name mangling suppressed for C linkage
- [ ] 41+ tests passing (unit + integration)
- [ ] All 71 existing tests still passing (no regressions)
- [ ] Documentation updated (FAQ, user guide)
- [ ] Example project demonstrating usage
- [ ] CI/CD pipeline includes new tests
- [ ] Code committed with git flow
- [ ] Ready for release

## References

### Clang Documentation
- [FunctionDecl API](https://clang.llvm.org/doxygen/classclang_1_1FunctionDecl.html)
- [LinkageSpecDecl API](https://clang.llvm.org/doxygen/classclang_1_1LinkageSpecDecl.html)
- [Clang AST Introduction](https://clang.llvm.org/docs/IntroductionToTheClangAST.html)
- [Attributes Reference](https://clang.llvm.org/docs/AttributeReference.html)

### Calling Conventions
- [x86 Calling Conventions](https://en.wikipedia.org/wiki/X86_calling_conventions)
- [Clang Calling Convention Tests](https://github.com/llvm-mirror/clang/blob/master/test/Sema/callingconv.c)

### Project Files
- Architecture: `docs/ARCHITECTURE.md`
- Visitor pattern: `include/CppToCVisitor.h`
- AST builder: `include/CNodeBuilder.h`
- Name mangling: `src/NameMangler.cpp`
- Runtime example: `runtime/exception_runtime.h`

---

**Version:** 1.0
**Created:** 2025-12-18
**Status:** Ready for execution

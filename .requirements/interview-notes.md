# Requirements Interview Notes

**Date:** 2025-12-23
**Interviewee:** Project Owner
**Interviewer:** Claude Code (Requirements Gathering)
**Project:** C++ to C Transpiler - Multi-File and Header Support

---

## Interview Summary

### Initial Request
> "We have a C++ to C transpiler code here. The problem is that it handles one file at a time, and (probably - investigate that!) does not handle headers. We need it to have input similar to clang - accept multiple input files at a time, and support a parameter for a list of header directories."

### Key Insights from Investigation

1. **Multi-file support already exists** in CLI (surprise finding!)
2. **Headers ARE handled** via Virtual File System (VFS)
3. **Critical gap**: No include directory support (`-I` flag)

---

## Investigation Process

### Phase 1: Survey the Landscape
- ✅ Read README.md
- ✅ Examined project structure
- ✅ Identified existing documentation
- ✅ Located main components (CLI, Library API)

### Phase 2: Parallel Investigation (3 concurrent tasks)

#### Task 1: Current File Handling
**Agent ID:** aab57a0

**Findings:**
- CLI supports multiple files via `CommonOptionsParser`
- Usage: `cpptoc file1.cpp file2.cpp file3.cpp --`
- Library API (`TranspilerAPI`) handles single source string
- Each file processed independently with separate AST

**Key Code Locations:**
- `src/main.cpp:185-191` - Multi-file handling
- `src/TranspilerAPI.cpp:265` - Single-file API

#### Task 2: Header Handling
**Agent ID:** aa99e30

**Findings:**
- ✅ Virtual File System (VFS) fully implemented (Phase 27-01)
- ✅ Header/Implementation separation complete (Phase 28)
- ✅ Include guards, forward declarations working
- ❌ Include directories (`-I` flag) NOT implemented
- 📋 Phase 27-02 plan exists for include path support

**Key Components:**
- `HeaderSeparator` - Splits declarations/implementations
- `IncludeGuardGenerator` - Generates include guards
- `DependencyAnalyzer` - Tracks dependencies

**Test Coverage:**
- 8 VFS tests (all passing)
- 8 Header separation tests (all passing)

#### Task 3: Clang CLI Research
**Agent ID:** afa2525

**Findings:**
- Clang uses `--` separator between tool options and compiler flags
- Multiple files: `clang file1.c file2.c file3.c`
- Include paths: `-I/path1 -I/path2` (order matters!)
- LibTooling standard: `CommonOptionsParser` + `ClangTool`
- Our implementation already follows best practices!

**Standard Pattern:**
```bash
tool [tool-options] source-files -- [compiler-options]
```

---

## Key Findings

### What Works ✅

1. **CLI Multi-File Support**
   - Already implemented via `CommonOptionsParser`
   - Follows LibTooling best practices
   - Supports compilation database
   - Example: `cpptoc file1.cpp file2.cpp --`

2. **Virtual File System**
   - Fully implemented (Phase 27-01 complete)
   - Supports in-memory headers
   - Works for WASM/browser usage
   - Comprehensive test coverage

3. **Header Separation**
   - Fully implemented (Phase 28 complete)
   - Generates separate `.h` and `.c` files
   - Include guards (both styles supported)
   - Forward declarations for mutual references

4. **Compiler Flag Pass-through**
   - Already supports `--` separator
   - Passes flags to Clang correctly
   - Standard LibTooling pattern

### What's Missing ❌

1. **Include Directory Support (CRITICAL)**
   - No support for `-I<directory>` flags
   - Must use absolute paths in includes
   - Prevents standard C++ include syntax
   - Awkward WASM/browser usage

2. **Library API Multi-File (NICE-TO-HAVE)**
   - API only handles single source string
   - No `transpileMultiple()` function
   - Can be added later (not critical)

---

## Requirements Clarification

### Original Request Analysis

**"handles one file at a time"**
- **CLI**: FALSE - already supports multiple files
- **Library API**: TRUE - single file per call
- **Conclusion**: Likely referring to Library API, or CLI behavior misunderstood

**"does not handle headers"**
- **FALSE**: Headers ARE handled via VFS
- **Missing piece**: Include directory paths (`-I` flag)
- **Conclusion**: Can use headers, but path resolution is awkward

**"accept multiple input files"**
- **CLI**: Already works!
- **Library API**: Could be enhanced (future)
- **Conclusion**: CLI already meets requirement

**"support a parameter for a list of header directories"**
- **Status**: NOT implemented
- **Impact**: CRITICAL gap
- **Solution**: Phase 27-02 (include path support)

---

## Technical Assessment

### Existing Infrastructure

**Excellent foundation for enhancement:**
1. VFS production-ready (Phase 27-01 complete)
2. Header separation working (Phase 28 complete)
3. Test infrastructure comprehensive
4. Code architecture clean (SOLID principles)
5. Implementation plan already exists (Phase 27-02)

### Implementation Effort

**Phase 27-02: Include Path Support**
- **Effort**: 1-2 hours
- **Risk**: Low
- **Code Changes**: ~3 lines
- **Tests**: 5 unit tests
- **Breaking Changes**: None (additive API)

**Code Changes Required:**
```cpp
// TranspilerAPI.h (add 1 field)
struct TranspileOptions {
    std::vector<std::string> includePaths;  // NEW
};

// TranspilerAPI.cpp (add 3 lines)
for (const auto& path : options.includePaths) {
    args.push_back("-I" + path);
}
```

---

## User Stories Extracted

### Story 1: Standard Include Syntax
> As a developer using cpptoc,
> I want to specify header directories with `-I` flags,
> So I can use `#include <header.h>` instead of absolute paths.

**Priority:** P0 (Critical)
**Status:** Not Implemented

### Story 2: Multi-Module Project
> As a developer with multiple source files,
> I want to transpile all files with shared headers,
> So that header resolution works consistently.

**Priority:** P1 (High)
**Status:** CLI already works, just need include paths

### Story 3: WASM Developer
> As a WASM developer,
> I want to combine include paths with virtual files,
> So I can mix physical headers with in-memory content.

**Priority:** P1 (High)
**Status:** VFS works, just need include paths

### Story 4: Build System Integration
> As a build system integrator,
> I want to use the same `-I` flags as my C++ compiler,
> So my build scripts are consistent.

**Priority:** P1 (High)
**Status:** Needs include path support

---

## Recommendations

### Immediate Action (Phase 27-02)

**Implement Include Path Support:**
1. Add `includePaths` to `TranspileOptions` struct
2. Convert paths to `-I` args in `transpile()`
3. Write 5 unit tests
4. Update documentation
5. Run regression tests

**Timeline:** 2.5 hours total
**Risk:** Low
**Impact:** High (enables standard C++ workflows)

### Future Enhancements (Optional)

**Not critical, but consider later:**
1. Multi-file Library API (`transpileMultiple()`)
2. Include path validation warnings
3. Verbose include search mode
4. Compilation database generation helper

---

## Open Questions

### Answered During Investigation

**Q: Does it handle multiple files?**
A: CLI yes (via `CommonOptionsParser`), Library API no (single file only)

**Q: Does it handle headers?**
A: Yes (via VFS), but no include directory paths

**Q: What's the critical gap?**
A: Include directory support (`-I` flag)

**Q: How much work to fix?**
A: ~2.5 hours (low risk, small code change)

### Still Open (Not Critical)

1. Should we add multi-file Library API now or later?
   - **Recommendation**: Later (not critical, can be additive)

2. Should we validate include paths (warn if missing)?
   - **Recommendation**: Nice-to-have, not required for MVP

3. Should we support compilation database generation?
   - **Recommendation**: Future enhancement

---

## Constraints and Assumptions

### Constraints
- Must be backward compatible (no breaking changes)
- Must follow Clang command-line conventions
- Must work in WASM environment (no filesystem)
- Must maintain test coverage (no regression)

### Assumptions
- Users familiar with clang/gcc `-I` flag syntax
- Include paths are relative to working directory (clang standard)
- Multiple include paths searched in order (first match wins)
- VFS and include paths can coexist (tested together)

---

## Success Criteria

### Minimum Viable Feature
1. ✅ CLI accepts `-I<dir>` flags after `--`
2. ✅ Library API accepts `includePaths` option
3. ✅ Standard include syntax works: `#include <header.h>`
4. ✅ Multiple `-I` flags supported (correct order)
5. ✅ 5+ unit tests passing
6. ✅ All existing tests pass (no regression)
7. ✅ Documentation updated

### Definition of Done
- Code implemented per Phase 27-02 plan
- All tests passing (existing + new)
- Documentation updated (README, API docs)
- No breaking changes
- Performance no worse than baseline

---

## Next Steps

1. **Review PRD** with project owner
2. **Approve requirements** for implementation
3. **Execute Phase 27-02** implementation plan
4. **Test thoroughly** (unit + integration + regression)
5. **Update documentation** (README, API reference)
6. **Commit and release** with git flow

---

## Investigation Resources Used

### Documentation Read
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/README.md`
- Phase 27-01, 27-02, 28 documentation
- API reference (`TranspilerAPI.h`)
- CLI options documentation

### Code Analyzed
- `src/main.cpp` (CLI entry point)
- `src/TranspilerAPI.cpp` (Library API)
- `include/TranspilerAPI.h` (API definition)
- Test files (VFS, header separation)

### External Research
- Clang Command Line Reference
- LibTooling Documentation
- JSON Compilation Database Specification
- Community examples (GitHub repositories)

---

**Interview Completed:** 2025-12-23
**PRD Created:** `.requirements/PRD-multi-file-header-support.md`
**Status:** Ready for approval and implementation

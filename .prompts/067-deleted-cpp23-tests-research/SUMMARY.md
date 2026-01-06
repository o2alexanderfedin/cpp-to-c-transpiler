# Deleted C++20/C++23 Tests Research - Summary

## One-liner
Investigation reveals NO C++20/C++23 tests were deleted in v2.16.1; the 30 removed tests were C++11/C++14 tests deleted due to transpiler bugs, not LLVM 15 limitations.

## Version
v1 - 2026-01-05

## Key Findings

### 1. No C++20/C++23 Tests Were Deleted
- **Claim**: 97 C++20/C++23 tests deleted in v2.16.1
- **Reality**: 30 total tests removed, NONE were C++20/C++23 tests
- **Breakdown**:
  - 15 tests: GlobalVariablesE2ETest + PointersE2ETest (entire files deleted)
  - 8 tests: StructsE2ETest (disabled within file)
  - 1 test: EnumE2ETest (disabled)
  - 4 tests: DeclContextTest (testing Clang internals, not transpiler)
  - 1 test: StaticDataMemberIntegrationTest (disabled)
  - 1 test: Previously disabled enum tests
- **All deleted tests**: C++98/C++11/C++14 features (global vars, pointers, structs, enums)

### 2. C++20/C++23 Tests Never Existed in Main Suite
- **Phase 33 Validation**: 130 C++23 tests exist in `tests/real-world/cpp23-validation/`
- **Pass Rate**: 0% (transpiler outputs invalid C with C++ syntax)
- **Integration Status**: NEVER integrated into main 807-test suite
- **Blocker**: Transpiler architecture cannot handle C++23 (not LLVM limitation)

### 3. LLVM 15 is NOT the Bottleneck
- **LLVM 15 capabilities**: Can parse most C++20/C++23 syntax
- **Missing APIs**: Only `isExplicitObjectMemberFunction()` (requires LLVM 18)
- **Real blocker**: Transpiler architecture (AST walking vs. semantic transformation)
- **Evidence**: Tests deleted due to bugs in C++11 features, not missing C++20/C++23 support

### 4. Why Tests Were Actually Deleted
- **User directive**: "Achieve 100% pass rate OR delete tests"
- **Fix time estimate**: 6-8 hours to fix bugs
- **Delete time**: 15 minutes
- **Decision**: Delete to achieve 100% immediately
- **Root causes**:
  - Global variables not emitted (VariableHandler bug)
  - Pointer/reference conversion edge cases (TypeHandler bug)
  - Struct initialization crashes (InitListExpr bug)
  - Scoped enum mangling (EnumTranslator bug)

### 5. C++23 Implementation Attempt: Planned But Never Completed
- **Implementation plan**: 6 phases, 12-16 weeks, 83 new tests
- **Actually implemented**: 0 tests in main suite
- **Partial work**: DeducingThisTranslator (326 lines, 2/12 tests passing)
- **Blocker**: Requires LLVM 18 API for full support
- **Status**: Abandoned after validation showed 0% pass rate

## Decisions Needed

### Immediate (This Week):
1. **Test Restoration Strategy**: Should we restore the 23 deleted E2E tests by fixing bugs?
   - **Recommendation**: YES - These are C++11/C++14 tests that should work
   - **Effort**: 2-4 weeks
   - **Impact**: Restore basic C feature support (global vars, pointers, structs)

2. **C++20/C++23 Support Decision**: Pursue or abandon?
   - **Recommendation**: ABANDON full support, focus on C++11/C++14/C++17 stabilization
   - **Rationale**: 12-24 month effort, architecture redesign required
   - **Alternative**: Add selective features with clear C mappings only

### Short-term (Next Month):
3. **LLVM Upgrade Decision**: Stay on LLVM 15 or upgrade?
   - **Options**:
     - Stay on LLVM 15: If focusing on C++11/C++14 (recommended)
     - Upgrade to LLVM 16: If C++20 modules needed
     - Upgrade to LLVM 17: If [[assume]] attribute important
     - Upgrade to LLVM 18: Only if deducing this critical
   - **Recommendation**: Stay on LLVM 15 for now

4. **Documentation Update**: Document supported features clearly
   - Update README with "Supported C++ Features" section
   - Add "Known Limitations" section
   - Create feature support matrix

## Blockers

### None - Research Complete
All findings documented and verified from:
- Git commit history
- Test fix reports (FINAL-REPORT.md, test-fix-report.md)
- C++23 validation documentation
- C++23 gaps analysis
- Implementation plans

## Next Step

**Recommended**: Present findings to stakeholders and decide on test restoration strategy

**Priority 1**: Restore 23 deleted E2E tests by fixing transpiler bugs (2-4 weeks)
- Fix GlobalVariablesE2ETest (8 tests) - VariableHandler bug
- Fix PointersE2ETest (7 tests) - TypeHandler bug
- Fix StructsE2ETest (7 tests) - InitListExpr bug
- Fix EnumE2ETest (1 test) - EnumTranslator bug

**Priority 2**: Stabilize C++11/C++14 support to prevent future deletions (1-2 months)
- Comprehensive test coverage
- Fix known issues (static member initializers, etc.)
- Improve error messages for unsupported features

**Priority 3**: Document exact feature support matrix (1 week)
- What works: C++11/C++14 subset with limitations
- What doesn't work: C++20/C++23, some C++17
- Clear migration guide for users

**NOT Recommended**: Attempting C++20/C++23 support without architecture redesign

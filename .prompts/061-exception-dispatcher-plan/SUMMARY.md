# Exception Handler Dispatcher Integration - Implementation Plan Summary

## One-liner
Comprehensive 7-phase plan for migrating exception handling (TryCatchTransformer, ThrowTranslator) to dispatcher pattern, eliminating technical debt (manual mangling, placeholders, string-based output), establishing complete test coverage, and integrating with existing handlers - estimated 37-55 hours over 5-7 working days.

## Version
v1

## Key Decisions Made

### 1. **Phase-Based Incremental Migration** (Critical Decision)
**Decision**: Break migration into 7 distinct phases executed sequentially with clear gates.

**Rationale**:
- Reduces risk by allowing verification at each step
- Enables rollback to previous phase if issues encountered
- Allows parallelization of independent work (ThrowTranslator vs TryCatchTransformer)

**Phases**:
1. Name Mangling Migration (2-3 hours) - **Prerequisite for all other work**
2. Handler Skeleton Creation (4-6 hours) - Verify dispatcher mechanics
3. Placeholder Replacement - ThrowTranslator (5-7 hours)
4. Placeholder Replacement - TryCatchTransformer (5-7 hours)
5. String-to-AST Refactoring - ThrowTranslator (8-12 hours)
6. String-to-AST Refactoring - TryCatchTransformer (10-15 hours) - **Most complex**
7. Test Migration and New Tests (10-14 hours)

**Impact**: Clear execution path, manageable risk, testable at each phase.

### 2. **Name Mangling First Approach** (Critical Decision)
**Decision**: Complete Phase 1 (NameMangler integration) before any other work.

**Rationale**:
- Name consistency critical for exception type matching (throw/catch)
- If type names don't match, exceptions won't be caught (catastrophic failure)
- All handlers must use same naming scheme from NameMangler API

**Implementation**:
- Replace `getMangledTypeName()` with `cpptoc::mangle_class(RD)`
- Replace `getDestructorName()` with `cpptoc::mangle_destructor(DD)`
- Replace `getConstructorName()` with `cpptoc::mangle_constructor(CD)`
- Zero manual "__" string concatenation

**Impact**: Ensures exception handling works correctly end-to-end.

### 3. **Service Class Delegation Pattern** (Design Decision)
**Decision**: Keep TryCatchTransformer and ThrowTranslator as service classes called by handlers, rather than inlining all logic into handlers.

**Rationale**:
- Preserves component reusability (can test standalone)
- Handlers remain thin (registration + delegation)
- Separation of concerns (handlers coordinate, transformers implement)
- Aligns with SOLID principles (Single Responsibility)

**Implementation**:
- TryStmtHandler delegates to TryCatchTransformer
- ThrowExprHandler delegates to ThrowTranslator
- Service classes gain dispatcher parameter for recursive delegation

**Impact**: Maintains clean architecture, enables independent testing.

### 4. **Inline Frame Push/Pop in Phase 6** (Implementation Decision)
**Decision**: Create frame push/pop operations as C AST nodes directly in TryCatchTransformer, rather than extending ExceptionFrameGenerator.

**Rationale**:
- ExceptionFrameGenerator produces strings, not AST
- Extending it to produce AST adds scope and complexity
- Inlining is simpler for Phase 6, can refactor later if needed

**Implementation**:
- Create frame VarDecl: `struct __cxx_exception_frame frame_N`
- Create frame initialization statements as C AST nodes
- Insert at beginning of try body
- Future: Could refactor to ExceptionFrameGenerator.generateFramePushAST()

**Impact**: Reduces Phase 6 complexity, defers optimization.

### 5. **Thread-Local Stack for Re-throw** (Implementation Decision)
**Decision**: Implement re-throw using thread-local stack access (`__cxx_exception_stack`) rather than passing frame variable names through context.

**Rationale**:
- Simpler implementation (no ExceptionMapper needed)
- Matches existing runtime design
- Thread-local stack already maintains current exception state

**Implementation**:
- Re-throw generates: `cxx_throw(__cxx_exception_stack->exception_object, __cxx_exception_stack->exception_type)`
- No need to track frame variable names in mapper

**Impact**: Simplifies re-throw implementation, avoids new mapper.

## Decisions Needed (User Approval Required)

### 1. **ExceptionMapper Creation** (Optional Enhancement)
**Question**: Should we create a dedicated ExceptionMapper for exception-specific context, or rely on existing mappers?

**Current Plan**: Use existing mappers (DeclMapper, TypeMapper, ExprMapper, StmtMapper).

**Alternative**: Create ExceptionMapper to store:
- Frame variable names (for nested try-catch)
- Action table names
- Exception frame associations

**Recommendation**: Start without ExceptionMapper (keep plan simple). Add later if needed.

**Action Required**: Approve current plan or request ExceptionMapper addition.

### 2. **ExceptionFrameGenerator Refactoring** (Future Enhancement)
**Question**: Should we extend ExceptionFrameGenerator to return C AST nodes instead of strings?

**Current Plan**: Inline frame push/pop logic in TryCatchTransformer (Phase 6).

**Alternative**: Extend ExceptionFrameGenerator with `generateFramePushAST()`, `generateFramePopAST()` methods.

**Recommendation**: Inline for Phase 6 (simpler). Refactor later if code duplication becomes issue.

**Action Required**: Approve inline approach for initial implementation.

### 3. **Test Migration Strategy** (Verification Approach)
**Question**: Should migrated tests keep string comparison as secondary verification, or rely solely on C AST assertions?

**Current Plan**: Use C AST assertions with optional CodeGenerator for string comparison.

**Alternative**: Always emit C code via CodeGenerator and compare strings (simpler assertions but less precise).

**Recommendation**: Use AST assertions as primary, string comparison as fallback for debugging.

**Action Required**: Approve test migration approach.

### 4. **Parallelization of Phases 3-6** (Resource Allocation)
**Question**: Should we parallelize ThrowTranslator work (Phases 3+5) and TryCatchTransformer work (Phases 4+6)?

**Current Plan**: Sequential execution (safer, simpler).

**Alternative**: Parallel execution (faster, requires coordination).

**Benefit**: Reduces total time from 7 days to 5 days (30% faster).

**Risk**: Integration issues may not be discovered until Phase 7.

**Recommendation**: Sequential for initial implementation (safer). Parallel if timeline is critical.

**Action Required**: Approve execution order (sequential or parallel).

## Blockers

### External Dependencies (None Currently Blocking)
- **NameMangler API**: Verified stable and ready (no blockers)
- **Existing Dispatcher Handlers**: Assumed working correctly (CompoundStmt, CallExpr, etc.)
- **CNodeBuilder**: May not support all node types (mitigation: use Clang API directly)
- **Mapper Infrastructure**: Assumed working correctly

### Internal Dependencies (Phase Gates)
- **Phase 1 → Phase 2**: Name mangling must be fixed before handler creation
- **Phase 2 → Phases 3, 4**: Handlers must exist before placeholder replacement
- **Phase 3 → Phase 5**: ThrowTranslator dispatcher integration must work before AST refactoring
- **Phase 4 → Phase 6**: TryCatchTransformer dispatcher integration must work before AST refactoring
- **Phases 5, 6 → Phase 7**: AST refactoring must be complete before test migration

### Potential Blockers (Identified with Mitigations)
1. **CNodeBuilder missing node types** (Risk R4)
   - Detection: Phase 5, 6 compilation errors
   - Mitigation: Use Clang API directly (VarDecl::Create, etc.)

2. **AST node parent/context incorrect** (Risk R5)
   - Detection: Phase 5, 6 runtime errors
   - Mitigation: Study existing handlers for pattern

3. **Integration test failures** (Risk R8)
   - Detection: Phase 7
   - Mitigation: Compare generated C code before/after, debug carefully

**Status**: No current blockers. All risks have identified mitigations.

## Next Step

**Immediate Action**: Begin implementation with **Phase 1: Name Mangling Migration**

**Task**: Create implementation prompt (062-exception-dispatcher-phase1-implement) or begin Phase 1 execution directly.

**Verification Before Proceeding**:
1. Confirm plan approval from user
2. Confirm execution order (sequential vs parallel)
3. Confirm test migration approach
4. Resolve any decision points above

**Phase 1 Success Criteria**:
- All manual name mangling replaced with NameMangler API
- All existing tests pass (TryCatchTransformerTest, ThrowTranslatorTest, integration tests)
- Zero manual "__" string concatenation in exception components
- Type names consistent across all handlers

**Estimated Duration**: 2-3 hours for Phase 1 completion.

---

**Plan Status**: Ready for implementation. Awaiting user approval for decision points and confirmation to proceed.

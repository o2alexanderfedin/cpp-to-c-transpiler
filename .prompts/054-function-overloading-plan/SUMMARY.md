# Function Overloading Support Implementation Plan - Summary

**Version**: v1
**Date**: 2025-12-29
**Status**: Planning Complete - Ready for Implementation

---

## One-Liner

Comprehensive architectural plan for robust function overloading support through global OverloadRegistry, deterministic NameMangler refactoring, and call site validation - eliminating cross-file inconsistencies and enabling systematic overload tracking.

---

## Key Findings

### 1. Critical Architecture Gap: Per-File State Causes Cross-File Inconsistencies

**Current Problem**: `NameMangler` uses per-instance `usedNames` set, causing:
- File A's first `foo(int)` → `foo` (simple name)
- File B's first `foo(int)` → `foo_int` (overloaded name)
- Call sites in File B to File A's function generate wrong names

**Solution**: Global `OverloadRegistry` singleton tracks all overloads across files, enabling deterministic mangling regardless of processing order.

### 2. Three-Component Architecture Provides Clean Separation

**Components**:
1. **OverloadRegistry**: Global tracking, deterministic indexing, O(log n) lookup
2. **Enhanced NameMangler**: Stateless, registry-backed, idempotent
3. **CallSiteValidator**: Verify call→declaration name consistency

**Benefits**: Each component has single responsibility, integrates seamlessly with existing dispatcher pattern, independently testable.

### 3. Existing Handler Framework Supports Direct Integration

**Current State**:
- Dispatcher pattern with predicate + visitor handlers
- Mappers (DeclMapper, ExprMapper) for node tracking
- Exact type matching (not `isa<>`) for handler selection

**Integration**: New components follow existing patterns - no framework changes needed. Registration via `registerWith()`, handler ordering handled via lazy validation.

### 4. Deterministic Overload Ordering Essential for Consistency

**Requirement**: Same overload set must produce same indices regardless of:
- Processing order (File A before B vs B before A)
- Insertion order (register foo(int) before foo(double) vs reverse)

**Solution**: `OverloadSet::compareSignatures()` provides lexicographic ordering by:
1. Parameter count (ascending)
2. Parameter types (mangled names, lexicographic)
3. Return type (tie-breaker)

### 5. Five-Phase Implementation Minimizes Risk

**Phases**:
- **Week 1**: OverloadRegistry (foundation, 100% tested)
- **Week 2**: NameMangler refactor (backward compatible API)
- **Week 3**: Handler integration (registration hooks)
- **Week 4**: CallSiteValidator (optional for MVP)
- **Week 5**: End-to-end validation (real-world tests)

**Risk Mitigation**: Each phase independently testable, feature flags for rollback, existing tests run after each phase.

---

## Decisions Needed

### 1. NameMangler Constructor API Change Strategy

**Question**: How to handle breaking change to `NameMangler` constructor?

**Options**:
- **A**: Direct change - all callers must update (breaking change, clean migration)
- **B**: Overloaded constructor - backward compatible but maintains old behavior
- **C**: Factory pattern - `NameMangler::create(Context, registry)` and `NameMangler::createLegacy(Context)`

**Recommendation**: **Option A** - Direct change with clear migration path
- Only ~10 callsites in codebase (FunctionHandler, MethodHandler, etc.)
- Compiler errors guide migration
- No legacy code maintenance burden
- Clean API for future development

**Decision Required**: Approve breaking change or require backward compatibility?

---

### 2. Call Site Validation Timing

**Question**: When should CallSiteValidator run?

**Options**:
- **A**: After each CallExpr creation (immediate, may miss late registrations)
- **B**: Post-translation pass (delayed, requires separate traversal)
- **C**: Lazy validation (validates when both callee and call site are ready)

**Recommendation**: **Option C** - Lazy validation
- Naturally handles handler ordering (no explicit dependencies)
- Validates exactly once per call site
- Optional for MVP (can disable without breaking translation)

**Decision Required**: Accept lazy validation approach or require immediate validation?

---

### 3. Overload Registry Persistence

**Question**: Should OverloadRegistry persist across multiple transpilation runs?

**Options**:
- **A**: Clear between runs - fresh state each time (simpler, testing-friendly)
- **B**: Persist across runs - incremental transpilation support (complex, caching needed)

**Recommendation**: **Option A** for Phase 1
- Simpler implementation and testing
- Each transpilation run is independent (matches current behavior)
- Can add persistence in future phase if needed

**Decision Required**: Is incremental transpilation a Phase 1 requirement?

---

### 4. Template Overload Support Scope

**Question**: Should Phase 1 include template function overloading?

**Current Plan**: No - templates deferred to future enhancement

**Rationale**:
- Template instantiation tracking adds significant complexity
- Current codebase has limited template overload usage
- Can be added incrementally without breaking existing work

**Decision Required**: Confirm templates are out of scope for Phase 1?

---

### 5. Error Handling Strategy for Validation

**Question**: What should happen when CallSiteValidator detects mismatch?

**Options**:
- **A**: Fatal error - abort transpilation (strict, prevents bad output)
- **B**: Warning - continue with best-effort (permissive, allows partial success)
- **C**: Configurable - flag controls behavior (flexible, testing-friendly)

**Recommendation**: **Option C** - Configurable
- Default: Warning (prevents blocking on edge cases)
- Strict mode: Fatal error (for CI/CD pipelines)
- Test mode: Collect all errors (comprehensive reporting)

**Decision Required**: Approve configurable error handling?

---

## Blockers

**None identified.** All dependencies are internal to the transpiler:

- **No external libraries required**: Uses existing Clang AST APIs
- **No tooling changes**: Works with current build system (CMake)
- **No breaking API changes to public interfaces**: Only internal refactoring
- **No data migration**: Fresh registry each run

---

## Next Step

**Immediate Action**: Begin Phase 1 implementation

**Concrete Tasks**:
1. Create feature branch: `git checkout -b feature/robust-overloading`
2. Implement `include/OverloadRegistry.h` with full documentation
3. Implement `src/OverloadRegistry.cpp` with singleton pattern
4. Create comprehensive test suite: `tests/unit/OverloadRegistryTest.cpp`
5. Verify 100% code coverage for OverloadRegistry
6. Commit Phase 1 deliverables

**Estimated Timeline**: 1 week for Phase 1 (foundation)

**Validation Criteria**:
- All OverloadRegistry tests passing (15+ test cases)
- Code coverage ≥ 95% for new code
- Documentation complete with examples
- Zero compiler warnings
- Ready for Phase 2 (NameMangler integration)

**Command to start**:
```bash
git checkout -b feature/robust-overloading
mkdir -p tests/unit
touch include/OverloadRegistry.h
touch src/OverloadRegistry.cpp
touch tests/unit/OverloadRegistryTest.cpp
```

---

## Dependencies for Success

**Technical Dependencies**:
- Clang 18+ headers (already available)
- GoogleTest framework (already integrated)
- CMake 3.20+ (current version sufficient)

**Knowledge Dependencies**:
- Understanding of Clang AST FunctionDecl API ✓
- Familiarity with existing dispatcher pattern ✓
- Knowledge of name mangling principles ✓

**Resource Dependencies**:
- 5 weeks development time
- Access to real-world validation test suite ✓
- Ability to run full test suite (~500 tests) ✓

---

## Risk Summary

**Low-Risk Implementation**:
- ✓ Incremental approach with clear phase boundaries
- ✓ Each phase independently testable
- ✓ Backward compatibility maintained where feasible
- ✓ Feature flags for gradual rollout
- ✓ Comprehensive test coverage

**Monitored Risks**:
- Breaking existing tests (mitigated by extensive regression testing)
- Handler ordering dependencies (mitigated by lazy validation)
- Performance concerns (mitigated by profiling and optimization)

**Overall Risk Level**: **Low to Medium** - Well-planned with clear mitigations

---

**Prepared by**: Claude Sonnet 4.5
**Review Status**: Pending approval for Phase 1 start
**Implementation Ready**: Yes - all design decisions documented, APIs specified, test strategy defined

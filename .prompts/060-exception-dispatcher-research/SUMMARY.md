# Exception Dispatcher Integration Research - Summary

## One-liner
Comprehensive analysis of exception handling components (TryCatchTransformer, ThrowTranslator, ExceptionFrameGenerator) reveals clear path to dispatcher integration requiring name mangling fixes, AST-based code generation refactoring, and test migration (37-55 hours estimated).

## Version
v1 (2026-01-03)

## Key Findings

### 1. Manual Name Mangling is Critical Blocker
**Impact**: HIGH - Correctness Issue

- **TryCatchTransformer** uses `RD->getNameAsString() + "__dtor"` (line 251)
- **ThrowTranslator** uses `RD->getNameAsString() + "__ctor"` (line 196)
- Both components use `RD->getNameAsString()` for type names (no namespace prefix)
- **Risk**: Exception type matching will fail if namespace/class names don't match RecordHandler output
- **Fix**: Replace with `cpptoc::mangle_class()`, `cpptoc::mangle_constructor()`, `cpptoc::mangle_destructor()`
- **Estimated effort**: 2-3 hours

### 2. String-Based Code Generation Violates Pipeline Architecture
**Impact**: HIGH - Architectural Violation

- TryCatchTransformer returns `std::string`, should return `clang::Stmt*`
- ThrowTranslator returns `std::string`, should return `clang::Expr*`
- Violates C++ AST → C AST → C Code pipeline
- Placeholder methods (`stmtToString()`, `exprToString()`) cannot translate complex expressions
- **Solution**: Refactor to create C AST nodes using CNodeBuilder
- **Estimated effort**: 10-15 hours

### 3. Dispatcher Pattern is Well-Defined and Consistent
**Impact**: MEDIUM - Implementation Guidance

- All handlers follow same pattern: `registerWith()`, `canHandle()`, `handleNodeType()`
- Handlers access mappers via dispatcher: `getDeclMapper()`, `getStmtMapper()`, `getExprMapper()`
- Recursive dispatch pattern: `disp.dispatch(cppCtx, cCtx, childNode)` → `mapper.getCreated(childNode)`
- **Critical pattern**: CompoundStmtHandler checks `isa<Expr>(stmt)` to dispatch expressions-as-statements
- This pattern is essential for ThrowExpr (expressions used as statements)

### 4. ExceptionFrameGenerator Needs No Dispatcher Integration
**Impact**: LOW - Reduced Scope

- ExceptionFrameGenerator is a pure code generation utility (not an AST handler)
- Generates runtime support structures (exception_support.h)
- No technical debt, all 17 tests pass
- Can remain as service class called by TryStmtHandler
- **No effort needed** for this component

### 5. Test Migration is Straightforward but Time-Consuming
**Impact**: MEDIUM - Testing Strategy

- **Unit tests** (TryCatchTransformerTest, ThrowTranslatorTest): Need rewrite for AST assertions
- **Integration tests** (ExceptionHandlingIntegrationTest, etc.): Minimal changes (runtime behavior)
- Existing dispatcher test pattern is well-established (see MethodHandlerDispatcherTest)
- **Estimated effort**: 12-16 hours

## Decisions Needed

### 1. Service Class vs. Inline Handler Logic
**Question**: Should TryCatchTransformer and ThrowTranslator remain as service classes called by handlers, or should their logic be inlined into TryStmtHandler/ThrowExprHandler?

**Option A**: Keep service classes
- Pro: Preserves existing code structure, easier migration
- Pro: Clear separation of concerns (handler = dispatch, transformer = logic)
- Con: Extra layer of indirection

**Option B**: Inline into handlers
- Pro: Simpler architecture, one less abstraction
- Pro: Easier to maintain (all logic in one place)
- Con: Larger handler classes

**Recommendation**: Start with Option A (keep service classes), refactor to Option B later if needed.

### 2. ExceptionMapper for Context Passing
**Question**: Do we need a dedicated ExceptionMapper for exception-specific context (frame variable names, action table names)?

**Current mappers**:
- DeclMapper, TypeMapper, ExprMapper, StmtMapper - for AST node mappings
- PathMapper - for file path mappings

**Exception-specific context**:
- Frame variable name (e.g., `frame`, `frame_nested_1`)
- Action table name (e.g., `actions_table_0`)
- Current exception type (for re-throw)

**Options**:
- Use fixed runtime names (`__cxx_exception_stack` accessed via thread-local)
- Store in new ExceptionMapper
- Pass via additional dispatcher method parameters

**Recommendation**: Start without ExceptionMapper (use fixed runtime names), add if complexity increases.

### 3. Test Migration Strategy
**Question**: Migrate existing tests or write new tests first?

**Option A**: Migrate existing tests first
- Pro: Ensures behavior preservation
- Con: Delays new functionality verification

**Option B**: Write new dispatcher tests first, keep old tests for regression
- Pro: Validates new architecture immediately
- Pro: Old tests catch regressions
- Con: More test code overall

**Recommendation**: Option B - Write new dispatcher tests, keep old tests until migration complete.

## Blockers

None - All information gathered, ready to proceed to planning phase.

## Next Step

**Create planning prompt (061-exception-dispatcher-plan)**

Planning phase should address:
1. Detailed refactoring strategy (service class vs. inline)
2. Incremental migration plan (minimize breakage)
3. Test-first approach (new dispatcher tests before refactoring)
4. ExceptionMapper decision (need vs. don't need)
5. Frame variable naming strategy (nested try-catch blocks)
6. Re-throw implementation (frame access mechanism)

## Appendix: Effort Breakdown

| Task | Estimated Hours | Risk Level |
|------|----------------|------------|
| Fix manual name mangling | 2-3 | Low |
| Create TryStmtHandler | 3-5 | Medium |
| Create ThrowExprHandler | 3-5 | Medium |
| Refactor TryCatchTransformer (string → AST) | 5-8 | High |
| Refactor ThrowTranslator (string → AST) | 5-7 | High |
| Migrate unit tests | 6-8 | Medium |
| Write new dispatcher tests | 4-5 | Low |
| Fix integration tests | 2-3 | Low |
| Documentation | 2-3 | Low |
| Buffer (unexpected issues) | 5-8 | - |
| **TOTAL** | **37-55 hours** | - |

**Timeline**: 5-7 working days (assuming 8-hour workdays)

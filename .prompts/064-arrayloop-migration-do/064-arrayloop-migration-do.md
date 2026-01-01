# Prompt 064: Migrate ArrayLoopGenerator from HandlerContext to Dispatcher Pattern

## Objective

Migrate ArrayLoopGenerator from the legacy HandlerContext pattern to the modern dispatcher pattern, eliminating the **last production code reference to HandlerContext** and achieving 100% production code retirement.

**Success Impact**: This migration completes the production code phase of HandlerContext retirement, moving the project from 89% to ~95% completion (only test code will remain).

## Context

**Background Documents**:
- @HANDLERCONTEXT_RETIREMENT_STATUS.md - Overall retirement status (89% complete)
- @STATICMEMBER_VERIFICATION_COMPLETE.md - Recent successful migration reference
- @.planning/phases/54-range-for-loops/PLAN.md - ArrayLoopGenerator design context

**Current State**:
- **File**: `include/handlers/ArrayLoopGenerator.h` (header-only implementation)
- **Pattern**: Uses `HandlerContext& ctx_` member (lines 51, 70, 155)
- **Usage**: No test files use ArrayLoopGenerator (verified with grep)
- **Dependencies**: RangeTypeAnalyzer, LoopVariableAnalyzer
- **Implementation**: No .cpp file exists (header-only class)

**Architecture Context**:
ArrayLoopGenerator is a helper class for Phase 54 (range-for loop translation). It generates index-based for loops for C array iteration, translating `for (T x : arr)` to `for (size_t i = 0; i < N; ++i) { T x = arr[i]; }`.

**Reference Migration** (StaticMemberTranslator → StaticDataMemberHandler):
```cpp
// OLD (HandlerContext pattern):
class StaticMemberTranslator {
    HandlerContext& ctx_;
    explicit StaticMemberTranslator(HandlerContext& ctx) : ctx_(ctx) {}
    // Used: ctx_.builder, ctx_.cppAST, ctx_.cAST
};

// NEW (Dispatcher pattern):
class StaticDataMemberHandler {
    CNodeBuilder& builder_;
    clang::ASTContext& cppContext_;
    clang::ASTContext& cContext_;

    explicit StaticDataMemberHandler(
        CNodeBuilder& builder,
        clang::ASTContext& cppCtx,
        clang::ASTContext& cCtx
    ) : builder_(builder), cppContext_(cppCtx), cContext_(cCtx) {}
};
```

## Requirements

### Phase 1: Code Migration

1. **Update ArrayLoopGenerator.h**:
   - Remove `#include "handlers/HandlerContext.h"` (line 51)
   - Add required includes:
     ```cpp
     #include "helpers/CNodeBuilder.h"
     #include "clang/AST/ASTContext.h"
     ```
   - Replace constructor parameter and member (lines 70, 155):
     ```cpp
     // OLD:
     explicit ArrayLoopGenerator(HandlerContext& ctx) : ctx_(ctx) {}
     HandlerContext& ctx_;

     // NEW:
     explicit ArrayLoopGenerator(
         CNodeBuilder& builder,
         clang::ASTContext& cppContext,
         clang::ASTContext& cContext
     ) : builder_(builder), cppContext_(cppContext), cContext_(cContext) {}

     CNodeBuilder& builder_;
     clang::ASTContext& cppContext_;
     clang::ASTContext& cContext_;
     ```
   - Update all method implementations that reference `ctx_`:
     - Replace `ctx_.builder` → `builder_`
     - Replace `ctx_.cppAST` → `cppContext_`
     - Replace `ctx_.cAST` → `cContext_`

2. **Find and Update Call Sites**:
   - Search for all files that instantiate or use ArrayLoopGenerator
   - Update constructor calls to pass explicit dependencies
   - Verify compilation after each call site update

### Phase 2: Verification

1. **Code Reference Check**:
   ```bash
   # Should return 0 (no active HandlerContext references in production):
   grep -r "HandlerContext" include/ src/ --include="*.cpp" --include="*.h" | \
     grep -v "comment\|DEPRECATED\|//" | wc -l
   ```

2. **Build Verification**:
   ```bash
   cd build
   cmake .. -DLLVM_DIR=/opt/homebrew/opt/llvm/lib/cmake/llvm \
            -DClang_DIR=/opt/homebrew/opt/llvm/lib/cmake/clang
   make -j8
   ```

3. **Test Execution** (if ArrayLoopGenerator has tests):
   - Identify test targets that exercise ArrayLoopGenerator
   - Run all relevant tests
   - Verify 100% pass rate

### Phase 3: Documentation

1. **Create Migration Report**: `ARRAYLOOP_MIGRATION_COMPLETE.md`
   - Summary of changes
   - Before/after code snippets
   - Build and test results
   - HandlerContext reference count verification

2. **Update Retirement Status**: Update `HANDLERCONTEXT_RETIREMENT_STATUS.md`
   - Mark ArrayLoopGenerator as COMPLETE
   - Update production code retirement percentage (should be 100%)
   - Update overall retirement percentage (~95%)

3. **Create SUMMARY.md** with:
   - One-liner: Substantive description of outcome
   - Key changes made
   - Verification results
   - Next step (HandlerTestFixture migration)

## Output Specification

**Primary Output**: Modified source files (in place)
- `include/handlers/ArrayLoopGenerator.h` (modified)
- Any call site files (modified)

**Documentation Output**: `.prompts/064-arrayloop-migration-do/`
- `ARRAYLOOP_MIGRATION_COMPLETE.md` - Migration report
- `SUMMARY.md` - Executive summary
- Update `HANDLERCONTEXT_RETIREMENT_STATUS.md` (in project root)

## Success Criteria

1. ✅ ArrayLoopGenerator.h has no HandlerContext references
2. ✅ All HandlerContext includes removed
3. ✅ Constructor updated with explicit dependencies
4. ✅ All method implementations updated (ctx_ → builder_/cppContext_/cContext_)
5. ✅ All call sites updated and compiling
6. ✅ Project builds successfully (no compilation errors)
7. ✅ Production code HandlerContext reference count = 0
8. ✅ All relevant tests passing (if any exist)
9. ✅ Migration report created and committed
10. ✅ HANDLERCONTEXT_RETIREMENT_STATUS.md updated showing 100% production code retirement

## Migration Steps (Detailed)

```bash
# Step 1: Create working branch (if using git flow)
git checkout develop
git pull origin develop

# Step 2: Update ArrayLoopGenerator.h
# - Edit includes, constructor, members, method bodies
# - Use Edit tool for surgical changes

# Step 3: Find call sites
grep -r "ArrayLoopGenerator" include/ src/ --include="*.cpp" --include="*.h"

# Step 4: Update each call site
# - Change constructor calls: ArrayLoopGenerator(ctx) → ArrayLoopGenerator(builder, cppCtx, cCtx)
# - Verify dependencies are available at call site

# Step 5: Build verification
cd build
cmake .. -DLLVM_DIR=/opt/homebrew/opt/llvm/lib/cmake/llvm \
         -DClang_DIR=/opt/homebrew/opt/llvm/lib/cmake/clang
make -j8 2>&1 | tee ../arrayloop_build.log

# Step 6: Run tests (if applicable)
# Find tests that use ArrayLoopGenerator
grep -r "ArrayLoopGenerator" tests/ --include="*.cpp"
# Run identified test targets

# Step 7: Verify HandlerContext elimination in production code
grep -r "HandlerContext" include/ src/ --include="*.cpp" --include="*.h" | \
  grep -v "//" | grep -v "DEPRECATED"
# Expected: 0 results

# Step 8: Create migration report
# Document changes, verification, metrics

# Step 9: Commit
git add .
git commit -m "refactor(arrayloop): Migrate ArrayLoopGenerator from HandlerContext to dispatcher pattern

- Replace HandlerContext dependency with explicit CNodeBuilder and ASTContext dependencies
- Update constructor signature with direct dependency injection
- Migrate all ctx_ member accesses to builder_/cppContext_/cContext_
- Achieves 100% production code HandlerContext retirement

Verification:
- Build: SUCCESS
- Tests: [test results]
- Production HandlerContext references: 0

Part of HandlerContext retirement initiative (now 95% complete)."
```

## Expected Challenges and Solutions

**Challenge 1**: ArrayLoopGenerator might be called from HandlerContext-based code
- **Solution**: If call site still uses HandlerContext, extract dependencies: `ctx.builder`, `ctx.cppAST`, `ctx.cAST` and pass explicitly

**Challenge 2**: Method implementations may have complex ctx_ usage patterns
- **Solution**: Search and replace methodically:
  - `ctx_.builder` → `builder_`
  - `ctx_.cppAST` → `cppContext_`
  - `ctx_.cAST` → `cContext_`

**Challenge 3**: Build errors due to missing includes
- **Solution**: Add required includes at top of ArrayLoopGenerator.h:
  ```cpp
  #include "helpers/CNodeBuilder.h"
  #include "clang/AST/ASTContext.h"
  ```

## Quality Checklist

Before considering this task complete:

- [ ] ArrayLoopGenerator.h compiles without errors
- [ ] No HandlerContext references in ArrayLoopGenerator.h
- [ ] All call sites updated and compiling
- [ ] Full project builds successfully
- [ ] Production code grep shows 0 HandlerContext references
- [ ] All tests passing (or no tests exist for ArrayLoopGenerator)
- [ ] Migration report created with metrics
- [ ] HANDLERCONTEXT_RETIREMENT_STATUS.md updated
- [ ] SUMMARY.md created with substantive one-liner
- [ ] Changes committed with descriptive message

## Time Estimate

**Total**: 2-4 hours
- Code migration: 1-2 hours (straightforward dependency injection)
- Build verification: 0.5 hours
- Test execution: 0.5-1 hour (if tests exist)
- Documentation: 0.5-1 hour

## Next Step After Completion

After achieving 100% production code retirement:
- **Next Priority**: HandlerTestFixture migration (3-5 hours, unblocks 10 integration tests)
- **File**: `.prompts/065-handlertest-fixture-migration/065-handlertest-fixture-migration.md`

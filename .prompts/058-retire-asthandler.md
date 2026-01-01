<objective>
Retire the legacy ASTHandler.h base class and fully migrate all descendant handlers to the CppToCVisitorDispatcher pattern.

This is part of the broader build cleanup effort following CMakeLists.txt refactoring. The codebase has migrated to a dispatcher-based architecture with static handler methods, making the instance-based ASTHandler inheritance hierarchy obsolete and creating maintenance burden.

End goal: Clean, consistent codebase using only the dispatcher pattern with no legacy handler infrastructure remaining.
</objective>

<context>
**Current Architecture:**
- Modern: `CppToCVisitorDispatcher` in `include/dispatch/CppToCVisitorDispatcher.h`
  - Uses static handler methods registered via `registerWith(dispatcher)`
  - Handlers are stateless functions with signature: `(const CppToCVisitorDispatcher&, const ASTContext&, ASTContext&, const NodeType*)`
  - Examples: RecordHandler, TypeHandler, ParameterHandler (already migrated)

- Legacy: `ASTHandler` in `include/handlers/ASTHandler.h`
  - Abstract base class with virtual methods: `canHandle()`, `handleDecl()`, `handleStmt()`, `handleExpr()`
  - Requires instance creation and HandlerContext dependency
  - 6 descendants still using it (see files_to_refactor below)

**Why This Matters:**
The legacy ASTHandler pattern creates confusion for new code, prevents dispatcher optimization, and increases build complexity. Recent test failures (RecordHandlerTest, FunctionHandlerTest) were caused by mixing both patterns.

**Recent Context:**
- Commit 6da8e27: Cleaned CMakeLists.txt, disabled RecordHandlerTest (85 test cases need dispatcher refactoring)
- FunctionHandlerTest was successfully migrated to dispatcher pattern (3 tests passing)
- This task completes the architecture unification

@include/handlers/ASTHandler.h - The legacy base class to retire
@include/dispatch/CppToCVisitorDispatcher.h - The modern dispatcher pattern
@include/dispatch/RecordHandler.h - Reference example of correct dispatcher pattern
@include/dispatch/TypeHandler.h - Another reference example
</context>

<requirements>
**Phase 1: Dependency Analysis**

1. **Find All ASTHandler Descendants:**
   Search for: `class.*Handler.*:.*public.*ASTHandler`
   Known files requiring migration:
   - `include/handlers/MethodHandler.h`
   - `include/dispatch/ConstructorHandler.h` (partially migrated)
   - `include/handlers/VariableHandler.h`
   - `include/handlers/StatementHandler.h`
   - `include/handlers/ExpressionHandler.h`
   - `include/handlers/DestructorHandler.h`

2. **Find All ASTHandler Usage:**
   Search codebase for:
   - `#include "handlers/ASTHandler.h"`
   - `ASTHandler*` (pointer declarations)
   - `std::unique_ptr<ASTHandler>`
   - `canHandle()` virtual method calls
   - `handleDecl()`, `handleStmt()`, `handleExpr()` virtual method calls

3. **Identify Test Dependencies:**
   Find all test files that instantiate these handlers or use ASTHandler API
   Check CMakeLists.txt for any commented-out tests related to these handlers

**Phase 2: Handler Migration (One at a Time)**

For each of the 6 handlers, perform migration in this order:
1. MethodHandler
2. VariableHandler
3. StatementHandler
4. ExpressionHandler
5. DestructorHandler
6. ConstructorHandler (finish migration - it's partially done)

**Migration Pattern for Each Handler:**

Given a legacy handler like this:
```cpp
// include/handlers/MethodHandler.h
class MethodHandler : public ASTHandler {
public:
    bool canHandle(const clang::Decl* D) const override;
    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override;
};
```

Transform it to dispatcher pattern like this:
```cpp
// include/dispatch/MethodHandler.h
namespace cpptoc {

class MethodHandler {
public:
    // Predicate function
    static bool canHandle(const clang::Decl* D);

    // Visitor function
    static void handleMethod(
        const CppToCVisitorDispatcher& dispatcher,
        const clang::ASTContext& cppCtx,
        clang::ASTContext& cCtx,
        const clang::CXXMethodDecl* method
    );

    // Registration function
    static void registerWith(CppToCVisitorDispatcher& dispatcher);
};

} // namespace cpptoc
```

Implementation pattern:
```cpp
// src/dispatch/MethodHandler.cpp
void MethodHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        // Predicate
        [](const clang::Decl* D) {
            return MethodHandler::canHandle(D);
        },
        // Visitor
        [](const CppToCVisitorDispatcher& disp,
           const clang::ASTContext& cppCtx,
           clang::ASTContext& cCtx,
           const clang::Decl* D) {
            auto* method = llvm::cast<clang::CXXMethodDecl>(D);
            MethodHandler::handleMethod(disp, cppCtx, cCtx, method);
        }
    );
}
```

**Phase 3: Update All References**

For each migrated handler:
1. Update all `#include` statements to point to `include/dispatch/` instead of `include/handlers/`
2. Replace instance-based calls (`handler->handleDecl(...)`) with dispatcher registration
3. Remove HandlerContext dependencies - use mapper classes instead
4. Update CMakeLists.txt to use `src/dispatch/` source files

**Phase 4: Remove Legacy Infrastructure**

Only after ALL 6 handlers are migrated:
1. Delete `include/handlers/ASTHandler.h`
2. Delete empty `include/handlers/` directory (if no other files remain)
3. Remove ASTHandler references from CMakeLists.txt
4. Update any documentation referring to the old pattern

**Phase 5: Verification**

1. Ensure all tests compile and pass
2. Check that no `#include "handlers/ASTHandler.h"` remains in codebase
3. Verify CMakeLists.txt has no references to deleted files
4. Run full build: `cmake --build build --parallel 10`
5. Run test suite: `cd build && ctest --output-on-failure`
</requirements>

<implementation>
**Migration Strategy:**
- Migrate handlers ONE AT A TIME to minimize risk
- After each handler migration, rebuild and verify tests still pass
- Use git commits after each successful handler migration
- If any migration fails, you can revert just that handler

**Pattern Consistency:**
- Follow the exact pattern used in RecordHandler and TypeHandler (already in dispatcher pattern)
- All handler static methods should be in `cpptoc` namespace
- Use `registerWith()` as the registration method name consistently
- Predicate functions return `bool`, visitor functions return `void`

**HandlerContext Replacement:**
The old pattern used `HandlerContext& ctx` for:
- `ctx.getCContext()` → Pass `clang::ASTContext& cCtx` directly as parameter
- `ctx.getCppContext()` → Pass `const clang::ASTContext& cppCtx` directly as parameter
- `ctx.registerDecl()` → Access via dispatcher's DeclMapper: `dispatcher.getDeclMapper().insert(cppDecl, cDecl)`
- `ctx.getBuilder()` → Create CNodeBuilder instance: `clang::CNodeBuilder builder(cCtx)`

**Avoid Common Pitfalls:**
- Don't delete ASTHandler.h until ALL descendants are migrated (build will fail)
- Don't mix old and new patterns in the same handler file
- Always update both header AND implementation files together
- Remember to update CMakeLists.txt after moving files from handlers/ to dispatch/
</implementation>

<verification>
Before declaring complete, verify your work thoroughly:

**Build Verification:**
```bash
# Clean rebuild
rm -rf build && mkdir build
cd build && cmake ..
cmake --build . --parallel 10
```

Expected: 100% build success with no errors

**Test Verification:**
```bash
cd build
ctest --output-on-failure
```

Expected: All enabled tests pass (some may be disabled from previous work, that's OK)

**Code Search Verification:**
```bash
# Should return NO results:
grep -r "ASTHandler" include/
grep -r "#include \"handlers/ASTHandler.h\"" .

# Should return NO results (legacy handler directory):
ls include/handlers/ 2>/dev/null

# Should have all handlers in dispatch/ directory:
ls include/dispatch/*Handler.h
```

Expected files in `include/dispatch/`:
- CppToCVisitorDispatcher.h
- RecordHandler.h (already exists)
- TypeHandler.h (already exists)
- MethodHandler.h (migrated)
- VariableHandler.h (migrated)
- StatementHandler.h (migrated)
- ExpressionHandler.h (migrated)
- DestructorHandler.h (migrated)
- ConstructorHandler.h (fully migrated)

**CMakeLists.txt Verification:**
```bash
grep -i "ASTHandler" CMakeLists.txt
```

Expected: No matches (all references removed)

**Git Status:**
```bash
git status
```

Expected changes:
- Deleted: `include/handlers/ASTHandler.h`
- Deleted: `include/handlers/` directory (if empty)
- Modified: 6 handler header files (moved to dispatch/)
- Modified: 6 handler implementation files
- Modified: CMakeLists.txt
- Modified: Any test files that used these handlers
</verification>

<success_criteria>
**Completed when:**
1. ✅ All 6 handler files migrated from instance-based to static dispatcher pattern
2. ✅ All handlers moved from `include/handlers/` to `include/dispatch/`
3. ✅ `ASTHandler.h` deleted from codebase
4. ✅ No `#include "handlers/ASTHandler.h"` references remain
5. ✅ CMakeLists.txt updated with no ASTHandler references
6. ✅ Full build succeeds: `cmake --build build --parallel 10`
7. ✅ All enabled tests pass: `ctest --output-on-failure`
8. ✅ Code search shows NO legacy pattern usage
9. ✅ All changes committed with clear commit messages
10. ✅ Architecture is now 100% dispatcher-based (no mixed patterns)

**Quality Indicators:**
- Each handler migration is a separate git commit
- Commit messages follow pattern: "refactor(handlers): Migrate [HandlerName] to dispatcher pattern"
- Build remains green after each individual handler migration
- No commented-out code or TODO markers in final result
- Consistent code style matching existing dispatcher handlers (RecordHandler, TypeHandler)
</success_criteria>

<constraints>
**DO NOT:**
- Delete ASTHandler.h before all descendants are migrated (build will fail)
- Skip the verification steps between handler migrations
- Leave any handlers in a half-migrated state
- Mix instance-based and static patterns in the same handler
- Remove files still referenced by CMakeLists.txt without updating it first

**WHY These Constraints Matter:**
- Deleting ASTHandler.h too early causes cascading build failures across all descendant handlers, making it difficult to isolate issues. Migrate first, then delete.
- Skipping verification between migrations means you won't know which specific handler migration broke the build if tests fail later.
- Half-migrated handlers create maintenance nightmares - developers won't know which pattern to follow.
- Mixed patterns in one handler file violates Single Responsibility and makes code impossible to reason about.
- CMakeLists.txt errors prevent the entire project from building, blocking all progress.

**MUST:**
- Commit after each successful handler migration (provides rollback points)
- Follow exact pattern from RecordHandler/TypeHandler (maintains consistency)
- Run build verification after each handler (catches issues early)
- Update both .h and .cpp files together (prevents linker errors)
- Use TodoWrite to track progress across the 6 handler migrations
</constraints>

<parallel_tool_calling>
This is a complex, multi-file refactoring task. For maximum efficiency:

1. When analyzing dependencies (Phase 1), invoke Read and Grep tools in parallel for all files
2. During migration phases, you can migrate multiple INDEPENDENT handlers in parallel if they don't share dependencies
3. After making changes, run build and test verification in parallel when possible
4. Use background execution for long-running builds while preparing next steps

Example parallel execution:
```
Read(MethodHandler.h) + Read(VariableHandler.h) + Read(StatementHandler.h) in single message
```

After tool results, reflect on quality before proceeding:
- Are all dependencies identified correctly?
- Does the migration preserve all functionality?
- Are there edge cases in the handler logic that need special attention?
</parallel_tool_calling>

<output>
**File Operations:**
Migration will touch these files:

Moved/Refactored:
- `include/handlers/MethodHandler.h` → `include/dispatch/MethodHandler.h`
- `include/handlers/VariableHandler.h` → `include/dispatch/VariableHandler.h`
- `include/handlers/StatementHandler.h` → `include/dispatch/StatementHandler.h`
- `include/handlers/ExpressionHandler.h` → `include/dispatch/ExpressionHandler.h`
- `include/handlers/DestructorHandler.h` → `include/dispatch/DestructorHandler.h`
- Corresponding `.cpp` files in `src/handlers/` → `src/dispatch/`

Deleted:
- `include/handlers/ASTHandler.h` (legacy base class)
- `include/handlers/` directory (if empty after migrations)

Modified:
- `CMakeLists.txt` (update source file references, remove ASTHandler)
- Any test files using these handlers (update to dispatcher pattern)
- Any other files with `#include "handlers/*Handler.h"` (update paths)

**Commit Strategy:**
Each handler migration should be a separate commit:
1. `git commit -m "refactor(handlers): Migrate MethodHandler to dispatcher pattern"`
2. `git commit -m "refactor(handlers): Migrate VariableHandler to dispatcher pattern"`
3. ... (continue for all 6 handlers)
4. `git commit -m "refactor(handlers): Remove legacy ASTHandler base class"`

Final commit after verification:
```
git commit -m "refactor(handlers): Complete migration to dispatcher pattern

- Migrated 6 handlers from instance-based ASTHandler to static dispatcher pattern
- Deleted legacy ASTHandler.h base class
- Moved all handlers to include/dispatch/ and src/dispatch/
- Updated CMakeLists.txt to reference new handler locations
- Architecture is now 100% dispatcher-based

Verified:
- Full build passes (100%)
- All enabled tests pass
- No ASTHandler references remain in codebase

Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
"
```
</output>

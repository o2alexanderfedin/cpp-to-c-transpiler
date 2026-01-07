# Complete SourceLocation Refactoring

## Objective

Systematically verify and complete the SourceLocation refactoring across all handlers in the transpiler codebase. Ensure every handler creates C AST nodes with valid SourceLocations (never using default `clang::SourceLocation()` constructor).

## Context

### Previous Work Completed
@.prompts/076-source-location-mapping-research/source-location-mapping-research.md - Research established the SourceLocationMapper approach with 15 passing tests.

**POC Implementation**: VariableHandler was successfully refactored as proof-of-concept (src/dispatch/VariableHandler.cpp:222-240):

```cpp
// Get valid SourceLocation for C AST node
std::string targetPath = disp.getCurrentTargetPath();
if (targetPath.empty()) {
    targetPath = disp.getTargetPath(cppASTContext, D);
}
SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

// Create C variable with VALID location
clang::VarDecl* cVar = clang::VarDecl::Create(
    cASTContext,
    cDeclContext,
    targetLoc,     // ✅ VALID (was: clang::SourceLocation())
    targetLoc,     // ✅ VALID (was: clang::SourceLocation())
    &II,
    cType,
    cASTContext.getTrivialTypeSourceInfo(cType),
    cStorageClass
);
```

### Architecture Context
- **TargetContext** owns SourceLocationMapper (src/TargetContext.cpp:48)
- **CppToCVisitorDispatcher** provides access via `getTargetContext().getLocationMapper()`
- **All handlers** have access to dispatcher, so can use this pattern
- **CodeGenerator** can now emit #line directives with valid locations

### Critical Design Principle
**Never use `clang::SourceLocation()`** - this returns an invalid location that confuses CodeGenerator. Always use `locMapper.getStartOfFile(targetPath)` which returns valid location (line 1, column 1).

## Requirements

### Phase 1: Discovery and Analysis

1. **Search for remaining usages**:
   - Use Grep tool to find all `clang::SourceLocation()` in `src/dispatch/` handlers
   - Search pattern: `clang::SourceLocation\(\)`
   - Focus on handler files: `*Handler.cpp`, `*Dispatcher.cpp`
   - Exclude test files initially (will handle separately)

2. **Categorize findings**:
   - Group by handler type (Function, Record, Method, Constructor, etc.)
   - Identify which AST node creation calls use invalid locations
   - Count total occurrences per file

3. **Create detailed report** in `.prompts/077-sourcelocation-complete-refactor-do/analysis-report.md`:
   ```markdown
   # SourceLocation Refactoring Analysis

   ## Summary
   - Total handlers analyzed: X
   - Handlers needing refactoring: Y
   - Total `clang::SourceLocation()` occurrences: Z

   ## Breakdown by Handler

   ### FunctionHandler (src/dispatch/FunctionHandler.cpp)
   - Line 123: FunctionDecl::Create() - 2 locations
   - Line 456: ParmVarDecl::Create() - 2 locations
   - Total: 4 occurrences

   ### RecordHandler (src/dispatch/RecordHandler.cpp)
   - Line 89: RecordDecl::Create() - 2 locations
   - Line 234: FieldDecl::Create() - 3 locations
   - Total: 5 occurrences

   [Continue for all handlers...]

   ## Refactoring Strategy
   1. Start with most-used handlers (highest test coverage)
   2. Apply VariableHandler pattern consistently
   3. Run tests after each handler
   4. Document any edge cases
   ```

### Phase 2: Systematic Refactoring

For **each handler** with `clang::SourceLocation()` usages:

1. **Read the handler file** completely to understand context
2. **Apply the VariableHandler pattern**:
   - Add at start of relevant function:
     ```cpp
     // Get valid SourceLocation for C AST node
     std::string targetPath = disp.getCurrentTargetPath();
     if (targetPath.empty()) {
         targetPath = disp.getTargetPath(cppASTContext, D);
     }
     SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
     clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);
     ```
   - Replace all `clang::SourceLocation()` with `targetLoc`
   - **Important**: Some AST nodes take multiple locations (start/end) - use `targetLoc` for all

3. **Handle edge cases**:
   - If handler creates multiple AST nodes, reuse same `targetLoc`
   - If handler processes different source files, get `targetPath` per-file
   - For TypeSourceInfo, use: `cASTContext.getTrivialTypeSourceInfo(cType, targetLoc)`

4. **Verify changes**:
   - Build after each handler refactoring
   - Run handler-specific unit tests
   - Check for any new warnings/errors

### Phase 3: Test Coverage

1. **Run full test suite**:
   ```bash
   cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build
   cmake --build . --target all
   ctest --output-on-failure
   ```

2. **Verify specific test categories**:
   - SourceLocationMapper tests: 15 tests (should remain 100% passing)
   - Dispatcher tests: 4 tests (should remain 100% passing)
   - Handler unit tests: Verify no regressions
   - E2E tests: Check generated C code has valid #line directives

3. **Check E2E test files** that were recently failing:
   - tests/e2e/phase47/EnumE2ETest.cpp
   - tests/e2e/phase5/StructsE2ETest.cpp
   - Verify they now generate C code with valid locations

### Phase 4: Verification and Cleanup

1. **Final search**: Re-run grep to confirm **zero** `clang::SourceLocation()` in handlers:
   ```bash
   grep -r "clang::SourceLocation()" src/dispatch/
   ```
   Expected: No matches (or only in comments/documentation)

2. **Review CodeGenerator integration**:
   - Read `src/CodeGenerator.cpp`
   - Verify `printDeclWithLineDirective()` works correctly
   - Check that generated .c files have #line directives

3. **Document patterns** in `.prompts/077-sourcelocation-complete-refactor-do/refactoring-patterns.md`:
   - Common patterns used
   - Edge cases encountered
   - Handler-specific notes
   - Testing notes

## Output Specification

Create these files in `.prompts/077-sourcelocation-complete-refactor-do/`:

1. **analysis-report.md**: Discovery phase results (categorized list of all occurrences)
2. **refactoring-log.md**: Chronological log of changes made (one entry per handler)
3. **refactoring-patterns.md**: Patterns and edge cases documentation
4. **SUMMARY.md**: Executive summary (required format below)

### Refactoring Log Format

```markdown
# SourceLocation Refactoring Log

## 2025-01-06: FunctionHandler

**File**: src/dispatch/FunctionHandler.cpp
**Lines changed**: 123, 456, 789
**Occurrences fixed**: 6
**Pattern applied**: Standard VariableHandler pattern
**Tests run**: FunctionHandlerTest (12/12 passing)
**Notes**: TypeSourceInfo required extra location parameter

## 2025-01-06: RecordHandler

[Continue for each handler...]
```

## Success Criteria

✅ **Discovery Complete**:
- All handlers searched
- All `clang::SourceLocation()` occurrences catalogued
- Analysis report created with counts

✅ **Refactoring Complete**:
- All handlers updated to use VariableHandler pattern
- Zero `clang::SourceLocation()` remaining in `src/dispatch/`
- Refactoring log documents all changes

✅ **Tests Passing**:
- Build succeeds with no new warnings
- SourceLocationMapper tests: 15/15 passing
- Dispatcher tests: 4/4 passing
- Handler unit tests: No regressions
- E2E tests: Valid #line directives in generated C code

✅ **Documentation Complete**:
- SUMMARY.md created with findings
- Refactoring patterns documented
- Edge cases noted

## SUMMARY.md Requirements

Must include:

- **One-liner**: Substantive description (e.g., "Refactored 23 handlers to use valid SourceLocations, eliminating 87 invalid location usages")
- **Version**: v1
- **Key Findings**:
  - Number of handlers refactored
  - Total occurrences fixed
  - Any patterns discovered
  - Test results
- **Files Created**: analysis-report.md, refactoring-log.md, refactoring-patterns.md
- **Decisions Needed**: Any edge cases requiring user input
- **Blockers**: External impediments (e.g., pre-existing test failures)
- **Next Step**: Concrete forward action (e.g., "Review generated C code for #line directives")

## Execution Notes

- **Work incrementally**: Refactor one handler at a time, test, commit
- **Use parallel tools**: Read multiple handlers simultaneously to understand patterns
- **Stream writes**: For large reports, write analysis as you discover (don't batch)
- **Verification first**: Always run grep search BEFORE claiming completion
- **Quality over speed**: Better to find all edge cases than to rush

## Expected Deliverables

1. Fully refactored handler codebase (all `src/dispatch/*.cpp` files)
2. Comprehensive analysis report showing what was found
3. Detailed refactoring log showing what was changed
4. Pattern documentation for future reference
5. SUMMARY.md with substantive findings
6. 100% test pass rate maintained

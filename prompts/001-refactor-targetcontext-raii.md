<objective>
Refactor TargetContext from Singleton pattern to RAII pattern to eliminate remaining race conditions and improve thread safety in parallel test execution.

This follows the successful refactoring of PathMapper, DeclMapper, TypeMapper, ExprMapper, and StmtMapper to RAII pattern, which achieved 100% test pass rate in parallel execution (849/849 tests).

End goal: Complete elimination of singleton pattern from the mapper infrastructure, ensuring full thread safety and test isolation.
</objective>

<context>
Project: C++ to C transpiler using Clang frontend
Language: C++17
Build system: CMake
Test framework: GoogleTest with CTest
Current status: All mapper classes successfully refactored to RAII (commit a037da7)

TargetContext is currently a singleton that provides the target C AST context. This singleton creates a shared state that can cause race conditions when tests run in parallel.

Review the codebase conventions in CLAUDE.md before starting.

Key files to examine:
@include/TargetContext.h - Current singleton implementation
@src/TargetContext.cpp - Implementation file
@include/mapping/TypeMapper.h - Example of successful RAII refactoring
@include/mapping/DeclMapper.h - Example of successful RAII refactoring
@src/TranspilerAPI.cpp - Main API that uses TargetContext
@tests/fixtures/DispatcherTestHelper.h - Test infrastructure
</context>

<requirements>
1. **Refactor TargetContext to RAII pattern**:
   - Remove static getInstance() method
   - Make constructor public
   - Add move constructor and move assignment operator (= default)
   - Delete copy constructor and copy assignment operator (= delete)
   - Remove static reset() method if present
   - Maintain all existing functionality

2. **Update all production code**:
   - Find all usages of TargetContext::getInstance()
   - Replace with local RAII instances
   - Pass references/pointers where needed (dependency injection)
   - Ensure proper lifetime management

3. **Update test infrastructure**:
   - Update DispatcherTestHelper to own TargetContext instance
   - Use std::unique_ptr<TargetContext> in DispatcherPipeline struct
   - Ensure each test gets isolated TargetContext instance

4. **Update all test files**:
   - Replace singleton calls with RAII instances
   - Ensure proper initialization order (TargetContext before other components that depend on it)

5. **Verify thread safety**:
   - Build the project successfully
   - Run all 849 tests in serial mode (ctest -j1) - expect 100% pass
   - Run all 849 tests in parallel mode (ctest -j8) - expect 100% pass
   - If any failures occur, analyze and fix them

6. **Git operations** (only if all tests pass 100%):
   - Stage all changes (git add .)
   - Commit with descriptive message following project conventions
   - Push to origin/develop
   - Create git flow release if this completes Phase 15 milestone
   - Merge to main if release created
</requirements>

<implementation>
Follow the exact same RAII refactoring pattern used for the mapper classes:

**Pattern from TypeMapper.h (lines 42-89)**:
```cpp
class TypeMapper {
public:
  TypeMapper() = default;  // Public constructor for RAII

  // Prevent copying
  TypeMapper(const TypeMapper&) = delete;
  TypeMapper& operator=(const TypeMapper&) = delete;

  // Allow move semantics
  TypeMapper(TypeMapper&&) = default;
  TypeMapper& operator=(TypeMapper&&) = default;

private:
  NodeMapper<clang::Type, clang::QualType> mapper_;
};
```

**Usage pattern from TranspilerAPI.cpp (lines 149-156)**:
```cpp
// RAII: Create mapper instances for this transpilation session
cpptoc::PathMapper mapper(".", ".");
cpptoc::DeclLocationMapper locMapper(mapper);
cpptoc::DeclMapper declMapper;
cpptoc::TypeMapper typeMapper;
```

Apply this same pattern to TargetContext. Consider:
- TargetContext likely creates/owns a clang::ASTContext for the C AST
- This is an expensive resource that should be managed with RAII
- The constructor may need parameters for initialization
- Components that depend on TargetContext should receive it via dependency injection

**Why RAII over Singleton**:
- Eliminates race conditions in parallel execution
- Provides clear ownership semantics
- Enables proper resource cleanup (automatic via destructor)
- Improves testability through instance isolation
- Follows modern C++ best practices (SOLID principles)

**Dependency injection approach**:
When passing TargetContext to other components, prefer:
1. Constructor injection: `Component(TargetContext& ctx)`
2. Pass by reference for non-owning access
3. Use std::unique_ptr for ownership transfer if needed

**DO NOT**:
- Use global variables or static instances
- Create backward-compatibility shims (getInstance() wrappers)
- Add "TODO" comments - implement fully
- Leave any singleton pattern remnants
</implementation>

<execution_steps>
1. **Research phase**:
   - Read TargetContext.h and TargetContext.cpp thoroughly
   - Identify all getInstance() call sites using grep/search
   - Identify all components that depend on TargetContext
   - Review how PathMapper and other mappers were refactored

2. **Refactor TargetContext header**:
   - Remove getInstance() declaration
   - Make constructor public (determine required parameters)
   - Add move semantics (= default)
   - Delete copy semantics (= delete)
   - Keep all existing methods

3. **Refactor TargetContext implementation**:
   - Remove getInstance() definition
   - Remove reset() definition if present
   - Update constructor accessibility
   - Ensure proper resource management in constructor/destructor

4. **Update production code** (systematic approach):
   - TranspilerAPI.cpp
   - CppToCFrontendAction.cpp
   - DispatcherTransformer.cpp
   - CCodePrinter.cpp
   - Any other files using TargetContext::getInstance()

5. **Update test infrastructure**:
   - DispatcherTestHelper.h - add TargetContext to DispatcherPipeline
   - DispatcherTestHelper.h - update createDispatcherPipeline() to create instance

6. **Build and verify**:
   - Run cmake build
   - Fix any compilation errors
   - If errors occur, analyze and fix systematically

7. **Run tests serially**:
   - Execute: ctest --output-on-failure -j1
   - Expect: 100% pass rate (849/849 tests)
   - If failures: analyze logs, fix issues, rebuild, retest

8. **Run tests in parallel**:
   - Execute: ctest --output-on-failure -j8
   - Expect: 100% pass rate (849/849 tests)
   - If failures: analyze race conditions, fix, rebuild, retest

9. **Git operations** (only after 100% pass rate):
   - git add .
   - git commit with message following conventions (include Co-Authored-By)
   - git push origin develop
   - Check if Phase 15 complete - if so, create release
   - If release created, merge to main

For maximum efficiency, when multiple independent operations are needed (reading files, searching code), invoke all relevant tools simultaneously in parallel.
</execution_steps>

<output>
Modified files:
- `./include/TargetContext.h` - RAII pattern applied
- `./src/TargetContext.cpp` - Singleton pattern removed
- `./src/TranspilerAPI.cpp` - Updated to use RAII instances
- `./tests/fixtures/DispatcherTestHelper.h` - Updated pipeline struct
- All test files using TargetContext - Updated to RAII pattern
- Any other production code using TargetContext - Updated
</output>

<verification>
Before declaring complete, verify ALL of the following:

1. ✅ **Code quality**:
   - No getInstance() calls remain in codebase
   - No static TargetContext instances exist
   - All components receive TargetContext via dependency injection
   - Move semantics properly implemented
   - Copy operations properly deleted

2. ✅ **Build success**:
   - cmake --build build completes without errors
   - No compiler warnings related to TargetContext

3. ✅ **Test results**:
   - Serial execution: 849/849 tests pass (100%)
   - Parallel execution: 849/849 tests pass (100%)
   - No race conditions detected
   - No test crashes or hangs

4. ✅ **Git operations**:
   - Changes committed with proper message format
   - Pushed to origin/develop successfully
   - Working directory clean (no uncommitted changes)
   - Release created if Phase 15 complete

Use TodoWrite extensively to track progress through all steps. Mark tasks in_progress before starting, completed immediately after finishing.

Run all verification checks systematically. Do not skip any verification step.
</verification>

<success_criteria>
**Must achieve ALL of the following**:

1. TargetContext fully refactored to RAII pattern (no singleton remnants)
2. All production code updated to use RAII instances
3. All test code updated to use RAII instances
4. Project builds successfully with no errors or warnings
5. All 849 tests pass in serial mode (100% pass rate)
6. All 849 tests pass in parallel mode with -j8 (100% pass rate)
7. Changes committed and pushed to origin/develop
8. Git flow release created and merged if Phase 15 complete

**Failure conditions** (must fix before completing):
- Any compilation errors or warnings
- Any test failures (serial or parallel)
- Any race conditions detected
- Any singleton pattern remnants
- Any uncommitted changes
- Any placeholders or TODO comments

This is a critical refactoring for thread safety. Take the time to do it thoroughly and correctly. The mapper refactoring succeeded - apply the same careful, systematic approach here.
</success_criteria>

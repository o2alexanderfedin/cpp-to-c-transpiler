# Function Handler Integration - Implementation Prompt

<objective>
Integrate FunctionHandler into the CppToCVisitorDispatcher chain of responsibility pattern, following the established TranslationUnitHandler architecture.

**Purpose**: Enable dispatcher-based translation of C++ free functions to C functions, preparing the foundation for comprehensive AST traversal.

**Output**: Updated dispatcher registration, FunctionHandler integration, and verification tests.

**Scope**: Function declarations ONLY - no statement/expression handling yet. Function bodies will remain empty (nullptr) in this phase.
</objective>

<context>
**Existing Architecture**:
- @src/dispatch/TranslationUnitHandler.cpp - Reference implementation pattern
- @include/dispatch/TranslationUnitHandler.h - Handler interface and registration pattern
- @src/dispatch/CppToCVisitorDispatcher.cpp - Dispatcher implementation
- @include/dispatch/CppToCVisitorDispatcher.h - Dispatcher interface

**Function Handler (Already Exists)**:
- @include/handlers/FunctionHandler.h - Function translation logic
- @src/handlers/FunctionHandler.cpp - Implementation (uses HandlerContext, not dispatcher)

**Key Challenge**: FunctionHandler currently uses HandlerContext (old architecture), needs adaptation to dispatcher pattern with cppASTContext/cASTContext parameters.
</context>

<requirements>

## Functional Requirements

1. **Adapt FunctionHandler to Dispatcher Pattern**:
   - Convert from `handleDecl(const clang::Decl* D, HandlerContext& ctx)` signature
   - To dispatcher signature: `handleFunction(const CppToCVisitorDispatcher& disp, const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::Decl* D)`
   - Preserve existing translation logic (parameter translation, return type handling)

2. **Follow TranslationUnitHandler Pattern Exactly**:
   - `static void registerWith(CppToCVisitorDispatcher& dispatcher)` - Registration entry point
   - `static bool canHandle(const clang::Decl* D)` - Predicate using exact type matching (D->getKind())
   - `static void handleFunction(...)` - Visitor following dispatcher signature
   - Use assertions for preconditions (null checks, type verification)

3. **Type Safety**:
   - Use `D->getKind() == clang::Decl::Function` for EXACT type matching (not isa<>)
   - Exclude CXXMethodDecl (methods are handled separately later)
   - Assert preconditions in both canHandle and handleFunction

4. **Integration Points**:
   - Register with dispatcher in main visitor initialization
   - Get C TranslationUnit from PathMapper via `disp.getPathMapper().getOrCreateTU(targetPath)`
   - Add translated function to C TranslationUnit's DeclContext

5. **Function Body Handling**:
   - For this phase, create functions with nullptr body (no statement translation yet)
   - Add comment/note in code explaining this is intentional for Phase 1
   - Body translation will be added in future phase with StatementHandler

## Quality Requirements

1. **Consistency**:
   - Match TranslationUnitHandler's structure exactly (file organization, naming, comments)
   - Use same error handling patterns (assertions, llvm::cast checks)
   - Follow same documentation style in header comments

2. **SOLID Principles**:
   - Single Responsibility: Handler only translates function declarations
   - Open/Closed: Uses dispatcher's extension points (addHandler)
   - Dependency Inversion: Depends on dispatcher abstraction

3. **Testing**:
   - Create unit test verifying FunctionHandler registration
   - Test canHandle predicate (true for FunctionDecl, false for CXXMethodDecl)
   - Test basic function translation (signature only, no body)

## Constraints

1. **NO Statement/Expression Translation**:
   - Do not implement function body translation yet
   - Set body parameter to nullptr when creating C FunctionDecl
   - This is explicitly out of scope for this phase

2. **Preserve Existing FunctionHandler Logic**:
   - Keep translateType() logic for reference-to-pointer conversion
   - Keep translateParameters() logic
   - Only change: adapt to dispatcher signature and remove HandlerContext dependency

3. **Build Requirements**:
   - Must compile with existing CMakeLists.txt
   - No new dependencies beyond existing Clang/LLVM
</requirements>

<implementation>

## Architecture Pattern to Follow

**From TranslationUnitHandler.h**:
```cpp
class TranslationUnitHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);
private:
    static bool canHandle(const clang::Decl* D);
    static void handleTranslationUnit(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );
};
```

**Adapt FunctionHandler to this exact pattern**.

## Critical Dispatcher Integration Steps

1. **Get Target Path**:
   ```cpp
   std::string targetPath = disp.getTargetPath(cppASTContext, D);
   ```

2. **Get or Create C TranslationUnit**:
   ```cpp
   cpptoc::PathMapper& pathMapper = disp.getPathMapper();
   clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);
   ```

3. **Add Translated Declaration to C TU**:
   ```cpp
   cFunc->setDeclContext(cTU);
   cTU->addDecl(cFunc);
   ```

4. **Register Node Location** (for AST tracking):
   ```cpp
   pathMapper.setNodeLocation(cFunc, targetPath);
   ```

## Adaptation Strategy

**Current FunctionHandler uses**:
- `ctx.getBuilder()` → Replace with direct `clang::FunctionDecl::Create()`
- `ctx.getCContext()` → Use `cASTContext` parameter
- `ctx.registerDecl(cppFunc, cFunc)` → Use `pathMapper.setNodeLocation(cFunc, targetPath)`

**Translation workflow**:
1. Cast D to FunctionDecl
2. Extract function properties (name, return type, parameters)
3. Translate types using existing translateType() logic
4. Create C FunctionDecl with translated signature
5. Set nullptr body (explicitly no statement translation yet)
6. Add to C TranslationUnit

## What to Avoid

1. **Do NOT implement statement/expression translation** - that's a future phase
2. **Do NOT use isa<> for type checking** - use getKind() for exact matching (safer)
3. **Do NOT create new HandlerContext references** - dispatcher pattern uses direct AST contexts
4. **Do NOT skip registration with dispatcher** - must call registerWith() from main visitor
5. **Do NOT forget assertions** - they catch bugs early and document preconditions

## Files to Modify

1. **include/dispatch/FunctionHandler.h** (create new or adapt existing):
   - Convert to static handler class matching TranslationUnitHandler pattern
   - Update signatures to dispatcher pattern
   - Add comprehensive documentation

2. **src/dispatch/FunctionHandler.cpp** (create new or adapt existing):
   - Implement registerWith, canHandle, handleFunction
   - Adapt existing translation logic to dispatcher context
   - Add nullptr body with comment explaining phase limitation

3. **src/CppToCConsumer.cpp** (or main visitor initialization):
   - Add FunctionHandler::registerWith(dispatcher) call
   - Ensure registration happens before dispatching begins

4. **tests/unit/handlers/FunctionHandlerDispatcherTest.cpp** (create new):
   - Test registration
   - Test canHandle predicate
   - Test basic function translation (verify signature, not body)
</implementation>

<output>
**Primary deliverables**:

If adapting existing files:
- `include/handlers/FunctionHandler.h` - Adapted to dispatcher pattern
- `src/handlers/FunctionHandler.cpp` - Adapted implementation
- Move to `include/dispatch/FunctionHandler.h` and `src/dispatch/FunctionHandler.cpp` if reorganizing

If creating new dispatcher-specific files:
- `include/dispatch/FunctionHandler.h` - New dispatcher-pattern handler
- `src/dispatch/FunctionHandler.cpp` - New implementation delegating to existing logic

**Integration**:
- `src/CppToCConsumer.cpp` - Add FunctionHandler registration

**Testing**:
- `tests/unit/dispatch/FunctionHandlerDispatcherTest.cpp` - Verification tests

**Build**:
- Update `CMakeLists.txt` if adding new files
</output>

<verification>

## Pre-Submission Checklist

Before declaring complete, verify:

1. **Build Success**:
   ```bash
   cmake --build build --target cpptoc_core
   ```
   Must compile without errors or warnings.

2. **Pattern Consistency**:
   - [ ] FunctionHandler header matches TranslationUnitHandler structure
   - [ ] Registration uses same pattern (registerWith static method)
   - [ ] Predicate uses getKind() for exact type matching
   - [ ] Handler signature matches dispatcher pattern exactly

3. **Type Safety**:
   - [ ] Assertions check D is not null
   - [ ] Assertions verify D is FunctionDecl (not subclass)
   - [ ] canHandle excludes CXXMethodDecl (returns false for methods)

4. **Integration**:
   - [ ] FunctionHandler registered in main visitor initialization
   - [ ] Translated functions added to C TranslationUnit
   - [ ] Node locations tracked in PathMapper

5. **Phase Scope**:
   - [ ] Function bodies set to nullptr (no statement translation)
   - [ ] Code comment explains this is intentional for Phase 1
   - [ ] No statement/expression handling implemented

6. **Testing**:
   - [ ] Unit test for registration exists
   - [ ] Unit test for canHandle predicate exists
   - [ ] Unit test verifies basic function signature translation
   - [ ] Tests pass: `ctest -R FunctionHandler`

7. **Documentation**:
   - [ ] Header comments explain handler purpose and scope
   - [ ] Comments document Phase 1 limitation (no bodies)
   - [ ] Algorithm documented in header (like TranslationUnitHandler)
</verification>

<summary_requirements>
Create `.prompts/048-function-handler-integration-do/SUMMARY.md`

**Template**:
```markdown
# Function Handler Integration Summary

**{One-liner describing outcome, e.g., "FunctionHandler integrated into dispatcher with signature-only translation"}**

## Version
v1

## Key Findings
- {What was implemented}
- {Key integration points}
- {Known limitations (no body translation)}

## Files Created
- `path/to/file` - Description

## Decisions Needed
{Any architectural choices needing user approval, or "None"}

## Blockers
{External issues, or "None"}

## Next Step
{Concrete action, e.g., "Run tests" or "Implement StatementHandler for body translation"}

---
*Confidence: High*
*Full output: N/A (Do prompt)*
```

**Emphasize**:
- Files created/modified
- Test coverage status
- Phase 1 scope (signatures only)
- Next step (likely: verify with integration tests or add statement handling)
</summary_requirements>

<success_criteria>

## Must Complete

- [ ] FunctionHandler adapted to dispatcher pattern
- [ ] Handler registered with CppToCVisitorDispatcher
- [ ] canHandle predicate correctly filters FunctionDecl (excludes methods)
- [ ] handleFunction creates C function with translated signature
- [ ] Function bodies explicitly set to nullptr (no statement translation)
- [ ] Translated functions added to C TranslationUnit
- [ ] Core library builds without errors
- [ ] Unit tests verify handler behavior
- [ ] SUMMARY.md created with files list and next step

## Definition of Done

- Build passes: `cmake --build build --target cpptoc_core`
- Tests pass: `ctest -R FunctionHandler` (if tests created)
- Code follows TranslationUnitHandler pattern exactly
- Documentation explains Phase 1 limitation
- Ready for next phase: StatementHandler integration
</success_criteria>

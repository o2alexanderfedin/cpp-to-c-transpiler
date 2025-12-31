# Implement RecordHandler for Dispatcher Architecture

## Objective

Create a new RecordHandler in the dispatcher architecture (`src/dispatch/`, `include/dispatch/`) that translates C++ struct/class declarations to C struct declarations. This handler will follow the Chain of Responsibility pattern established by FunctionHandler, ParameterHandler, and other dispatch handlers, and integrate with the unified NodeMapper system.

**Why this matters**: The current RecordHandler lives in `src/handlers/` (old architecture using HandlerContext). We're migrating to the dispatcher architecture with proper separation of concerns, consistent patterns, and testability. This is part of the architectural migration where translation decisions belong in Stage 2 (CppToCVisitor/handlers), not Stage 3 (CodeGenerator).

## Context

### Architecture Overview

The transpiler uses a 3-stage pipeline:
1. **Stage 1**: C++ source → C++ AST (Clang frontend)
2. **Stage 2**: C++ AST → C AST (CppToCVisitor with dispatcher handlers)
3. **Stage 3**: C AST → C source files (CodeGenerator)

We're implementing Stage 2 handlers using the Chain of Responsibility pattern.

### Existing Dispatcher Architecture

**Pattern**: All handlers in `dispatch/` follow this structure:

```cpp
class SomeHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);
private:
    static bool canHandle(const clang::Decl* D);  // Predicate
    static void handleSomething(...);              // Visitor
};
```

**Integration Points**:
- `CppToCVisitorDispatcher` - central dispatcher with `dispatch(cppCtx, cCtx, node)` methods
- `NodeMapper<KeyT, ValueT>` - generic mapper for C++ node → C node mappings
- `DeclMapper` - type alias for `NodeMapper<clang::Decl, clang::Decl*>`
- `TypeMapper` - type alias for `NodeMapper<clang::Type, clang::QualType>`
- `PathMapper` - maps C++ source files to C target files

### Reference Implementations

**Study these handlers**:
- `include/dispatch/FunctionHandler.h` + `src/dispatch/FunctionHandler.cpp` - declaration handler pattern
- `include/dispatch/ParameterHandler.h` + `src/dispatch/ParameterHandler.cpp` - nested dispatch pattern
- `include/dispatch/TypeHandler.h` + `src/dispatch/TypeHandler.cpp` - type translation pattern
- `include/dispatch/CompoundStmtHandler.cpp` - recursive dispatch for child nodes

**Key Patterns**:
1. **Static registration**: `registerWith(dispatcher)` registers predicate + visitor
2. **Exact type matching**: `D->getKind() == Decl::Record` (not `isa<>` for exact match)
3. **Assert preconditions**: `assert(D && "D must not be null")`
4. **Recursive dispatch**: For nested nodes (fields, nested structs), call `disp.dispatch(...)`
5. **DeclMapper storage**: `declMapper.setCreated(cppDecl, cDecl)` after creation
6. **Retrieve via mapper**: `declMapper.getCreated(cppNode)` to retrieve translated nodes

### Old RecordHandler (DO NOT MIGRATE)

The existing `src/handlers/RecordHandler.cpp` uses the old architecture:
- Uses `HandlerContext` (old dependency injection)
- Includes vtable/polymorphism logic (lpVtbl injection, thunks)
- Will remain for backward compatibility during transition

**Do NOT migrate** the old handler. Create a **new, simpler** handler for the dispatcher architecture.

## Requirements

### Phase 1 Scope: Basic Struct/Class Translation

Implement RecordHandler with these features:

1. **Basic Struct Translation**
   - Match `clang::RecordDecl` (both struct and class)
   - Create C `RecordDecl` with translated fields
   - Handle empty structs (no fields)

2. **Class-to-Struct Conversion**
   - Convert C++ `class` keyword to C `struct` keyword
   - Normalize `TagTypeKind::Class` → `TagTypeKind::Struct`
   - C has no class keyword, no access specifiers

3. **Field Translation with Type Mapping**
   - Dispatch each field's type via `disp.dispatch(cppCtx, cCtx, fieldType)`
   - Retrieve translated type via `typeMapper.getCreated(fieldType)`
   - Create C `FieldDecl` with translated type
   - Convert C++ reference fields to pointer fields (TypeHandler responsibility)

4. **Nested Struct Support with Name Mangling**
   - Detect nested struct/class definitions
   - Flatten nested structs to top-level (C has limited nested struct support)
   - Mangle nested names using `OuterClass_InnerStruct` pattern
   - Example:
     ```cpp
     // C++:
     struct Outer {
         struct Inner { int x; };
         Inner inner;
     };

     // C (flattened with name mangling):
     struct Outer_Inner { int x; };
     struct Outer {
         struct Outer_Inner inner;
     };
     ```

5. **Forward Declaration Handling**
   - Detect forward declarations vs complete definitions
   - Use `cppRecord->isCompleteDefinition()` to check
   - Forward declarations: Create C RecordDecl without calling `startDefinition()`
   - Complete definitions: Call `startDefinition()`, translate fields, call `completeDefinition()`

### Exclusions (Future Phases)

**Do NOT implement** in this phase:
- ❌ Virtual methods / vtable logic (Phase 45+)
- ❌ Inheritance (base classes, polymorphism)
- ❌ lpVtbl field injection
- ❌ Thunks or offset calculations
- ❌ Constructor/destructor handling
- ❌ Static members
- ❌ Method translation (methods handled by MethodHandler)

For polymorphic classes, log a message and skip translation:
```cpp
if (cxxRecord->isPolymorphic()) {
    llvm::errs() << "[RecordHandler] Skipping polymorphic class (vtable support not implemented): "
                 << cxxRecord->getNameAsString() << "\n";
    return;
}
```

### Implementation Checklist

- [ ] Create `include/dispatch/RecordHandler.h`
  - [ ] Header documentation (purpose, responsibilities, usage example)
  - [ ] Static `registerWith(CppToCVisitorDispatcher&)` declaration
  - [ ] Static `canHandle(const clang::Decl*)` predicate declaration
  - [ ] Static `handleRecord(...)` visitor declaration
  - [ ] Helper method declarations (if needed)

- [ ] Create `src/dispatch/RecordHandler.cpp`
  - [ ] `registerWith()` - register predicate + visitor with dispatcher
  - [ ] `canHandle()` - match RecordDecl (both struct and class), exclude CXXMethodDecl parent
  - [ ] `handleRecord()` - main translation logic
    - [ ] Check if already processed via `declMapper.hasCreated()`
    - [ ] Skip polymorphic classes (log message)
    - [ ] Normalize class → struct
    - [ ] Handle forward declarations vs complete definitions
    - [ ] Create C RecordDecl in C ASTContext
    - [ ] Store in DeclMapper early (before translating fields)
    - [ ] Detect and translate nested structs (recursive dispatch with name mangling)
    - [ ] Translate fields (dispatch types, create FieldDecl)
    - [ ] Complete definition
    - [ ] Add to C TranslationUnit

- [ ] Update `CMakeLists.txt`
  - [ ] Add `src/dispatch/RecordHandler.cpp` to build targets

- [ ] Register handler in dispatcher initialization
  - [ ] Find where handlers are registered (likely in CppToCConsumer or main)
  - [ ] Add `RecordHandler::registerWith(dispatcher)`

- [ ] Create unit tests: `tests/unit/dispatch/RecordHandlerDispatcherTest.cpp`
  - [ ] Test basic struct translation (empty struct)
  - [ ] Test struct with primitive fields (int, float)
  - [ ] Test class-to-struct conversion (class keyword → struct)
  - [ ] Test nested struct with name mangling (Outer_Inner)
  - [ ] Test forward declaration vs complete definition
  - [ ] Test field type translation (via TypeHandler)
  - [ ] Test already-processed detection (DeclMapper)
  - [ ] Test polymorphic class skipping (log + return)

- [ ] Run all tests
  - [ ] Build: `cmake --build build`
  - [ ] Run unit tests: `ctest --test-dir build -R RecordHandlerDispatcherTest`
  - [ ] Fix any failures

- [ ] Integration test (optional but recommended)
  - [ ] Create `tests/integration/dispatch/RecordHandlerIntegrationTest.cpp`
  - [ ] Test full pipeline: C++ source → C++ AST → C AST → verify C RecordDecl
  - [ ] Test nested struct flattening

## Output Specification

### Files to Create

1. **include/dispatch/RecordHandler.h**
   - Location: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/dispatch/RecordHandler.h`
   - Pattern: Follow FunctionHandler.h structure
   - Documentation: Class-level and method-level comments

2. **src/dispatch/RecordHandler.cpp**
   - Location: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/RecordHandler.cpp`
   - Pattern: Follow FunctionHandler.cpp structure
   - Logging: Use `llvm::outs()` for debug messages, `llvm::errs()` for warnings

3. **tests/unit/dispatch/RecordHandlerDispatcherTest.cpp**
   - Location: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/unit/dispatch/RecordHandlerDispatcherTest.cpp`
   - Framework: Google Test (like other dispatcher tests)
   - Pattern: Follow BinaryOperatorHandlerDispatcherTest.cpp structure

### Files to Modify

1. **CMakeLists.txt**
   - Add `src/dispatch/RecordHandler.cpp` to existing handler list
   - Add test executable target for RecordHandlerDispatcherTest

2. **Dispatcher registration site** (find where handlers are registered)
   - Add `#include "dispatch/RecordHandler.h"`
   - Add `RecordHandler::registerWith(dispatcher);`

### Code Structure Template

```cpp
// include/dispatch/RecordHandler.h
#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"

namespace cpptoc {

class RecordHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Decl* D);

    static void handleRecord(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    // Helper: Translate nested structs with name mangling
    static void translateNestedRecords(
        const clang::RecordDecl* cppRecord,
        clang::RecordDecl* cRecord,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );

    // Helper: Translate fields
    static void translateFields(
        const clang::RecordDecl* cppRecord,
        clang::RecordDecl* cRecord,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
```

## Success Criteria

### Compilation
- [ ] All files compile without errors or warnings
- [ ] CMake configuration succeeds
- [ ] Build completes successfully

### Tests
- [ ] All unit tests pass (RecordHandlerDispatcherTest)
- [ ] No regressions in existing tests
- [ ] Test coverage includes:
  - Basic struct translation
  - Class-to-struct conversion
  - Field translation with type mapping
  - Nested struct with name mangling
  - Forward declaration handling
  - Polymorphic class skipping

### Integration
- [ ] Handler registered in dispatcher
- [ ] Can translate simple C++ structs to C
- [ ] Nested structs flatten correctly with `Outer_Inner` naming
- [ ] TypeMapper correctly retrieves translated field types
- [ ] DeclMapper correctly stores/retrieves RecordDecl mappings

### Code Quality
- [ ] Follows SOLID principles (SRP, OCP, DIP)
- [ ] Follows existing dispatcher handler patterns
- [ ] Proper error handling (assertions, null checks)
- [ ] Debug logging for development visibility
- [ ] No code duplication (DRY)
- [ ] Comments explain why, not what

## Edge Cases to Handle

1. **Anonymous structs**: `struct { int x; } instance;`
   - No name, but must create RecordDecl with `nullptr` IdentifierInfo

2. **Empty structs**: `struct Empty {};`
   - Valid in C++, but C requires at least one member
   - Leave empty for now (CodeGenerator can add dummy field if needed)

3. **Circular nested structs**:
   ```cpp
   struct A { struct B* b; };
   struct B { struct A* a; };
   ```
   - Forward declarations prevent infinite recursion

4. **Typedef'd nested structs**:
   ```cpp
   struct Outer {
       typedef struct Inner { int x; } InnerType;
   };
   ```
   - Handle typedef separately (TypedefHandler, future)

5. **Multiple nested levels**:
   ```cpp
   struct A { struct B { struct C { int x; }; }; };
   ```
   - Flatten to `A_B_C` pattern recursively

## Resources

### Clang AST API References

- `clang::RecordDecl::Create()` - create C RecordDecl
- `clang::FieldDecl::Create()` - create field declaration
- `RecordDecl::startDefinition()` - begin defining struct
- `RecordDecl::completeDefinition()` - finish defining struct
- `RecordDecl::isCompleteDefinition()` - check if forward decl or complete
- `RecordDecl::getTagKind()` - get TagTypeKind (Struct, Class, Union, Enum)
- `RecordDecl::fields()` - iterate over field declarations
- `CXXRecordDecl::isPolymorphic()` - check for virtual methods

### Existing Code References

**Dispatcher Pattern**:
- `include/dispatch/CppToCVisitorDispatcher.h:77-253` - Dispatcher class
- `src/dispatch/FunctionHandler.cpp:16-22` - Handler registration pattern
- `src/dispatch/CompoundStmtHandler.cpp:24-29` - Exact type matching with `getStmtClass()`

**Mapper Usage**:
- `include/mapping/NodeMapper.h` - Generic mapper template
- `include/mapping/DeclMapper.h` - DeclMapper type alias
- `src/dispatch/CompoundStmtHandler.cpp:46-48` - Check if already processed
- `src/dispatch/CompoundStmtHandler.cpp:110` - Store in mapper

**Type Translation**:
- `src/dispatch/TypeHandler.cpp` - Type translation patterns
- `src/dispatch/ParameterHandler.cpp` - Recursive dispatch for nested types

### Documentation

Read before implementing:
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/CLAUDE.md` - Architecture principles
- `include/dispatch/FunctionHandler.h` - Well-documented handler example
- `include/mapping/NodeMapper.h` - Generic mapper API

## SUMMARY.md Requirement

After completing the implementation, you MUST create:

**File**: `.prompts/049-struct-class-handlers-do/SUMMARY.md`

**Required Sections**:
```markdown
# RecordHandler Implementation Summary

**{One substantive sentence describing what was accomplished}**

## Version
v1 - Initial implementation

## Files Created
- include/dispatch/RecordHandler.h
- src/dispatch/RecordHandler.cpp
- tests/unit/dispatch/RecordHandlerDispatcherTest.cpp

## Key Implementation Details
- {Bullet points of important decisions made}
- {Patterns followed}
- {Notable challenges resolved}

## Test Results
- {Pass/fail status}
- {Coverage summary}

## Decisions Needed
- {Any open questions or choices user must make}
- {Or "None" if implementation is complete}

## Blockers
- {External dependencies or issues}
- {Or "None" if unblocked}

## Next Step
{Concrete next action, e.g., "Register handler with dispatcher" or "Test with validation suite"}
```

## Implementation Notes

### TDD Approach (Recommended)

1. **Red**: Write failing test first
   ```cpp
   TEST(RecordHandlerDispatcherTest, BasicStructTranslation) {
       // Create C++ struct AST
       // Call handler
       // Assert C struct created with correct fields
       FAIL(); // Test fails initially
   }
   ```

2. **Green**: Write minimal code to pass
   ```cpp
   void RecordHandler::handleRecord(...) {
       // Minimal implementation to pass test
   }
   ```

3. **Refactor**: Clean up while tests stay green
   ```cpp
   // Extract helpers, remove duplication
   // Tests still pass
   ```

### Debugging Tips

- Use `llvm::outs()` for progress messages
- Use `llvm::errs()` for warnings/errors
- Enable verbose output: `ctest -V`
- Print AST: `cppRecord->dump()` or `cRecord->dump()`
- Check mapper contents before/after translation

### Common Pitfalls

1. **Forgetting to store in DeclMapper**: Always call `declMapper.setCreated(cppDecl, cDecl)` after creation
2. **Creating duplicate nodes**: Check `declMapper.hasCreated()` before creating
3. **Wrong parent DeclContext**: Use `cASTContext.getTranslationUnitDecl()` for top-level structs
4. **Forgetting to complete definition**: Call `cRecord->completeDefinition()` after adding fields
5. **Not handling forward declarations**: Check `isCompleteDefinition()` before translating fields
6. **Name mangling inconsistency**: Use consistent separator (underscore) for nested names

### Logging Convention

```cpp
llvm::outs() << "[RecordHandler] Processing struct: " << cppRecord->getNameAsString() << "\n";
llvm::outs() << "[RecordHandler] Created C struct with " << cRecord->field_size() << " fields\n";
llvm::errs() << "[RecordHandler] WARNING: Skipping polymorphic class: " << name << "\n";
```

## Final Checklist Before Completion

- [ ] All files created in correct locations
- [ ] Handler registered with dispatcher
- [ ] All tests pass (unit + existing tests)
- [ ] No compiler warnings
- [ ] Code follows project conventions (CLAUDE.md guidelines)
- [ ] SUMMARY.md created with substantive content
- [ ] Committed and pushed to git
- [ ] Ready for next phase (method translation, inheritance)

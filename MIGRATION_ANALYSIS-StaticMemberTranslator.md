# StaticMemberTranslator Migration Analysis

**Document**: Migration preparation for StaticMemberTranslator
**Target Architecture**: Dispatcher pattern with CppToCVisitorDispatcher
**Status**: Analysis complete - Ready for implementation
**Date**: 2025-12-31

---

## Executive Summary

StaticMemberTranslator is a self-contained Phase 49 helper that translates C++ static data members to C global variables. Current implementation uses HandlerContext (not yet created) as dependency. Migration requires:

1. Create StaticMemberHandler following existing dispatcher pattern
2. Replace HandlerContext dependency with CppToCVisitorDispatcher
3. Migrate all translation logic from helper to handler
4. Register with dispatcher for integration

**Complexity**: LOW - Straightforward helper-to-handler migration
**Effort**: 2-3 hours including tests
**Risk**: LOW - Well-isolated functionality with existing unit tests

---

## Part 1: Public API Analysis

### Current Public Methods

#### 1. `detectStaticMembers(const CXXRecordDecl* record)`
- **Purpose**: Identify all static data members in a C++ class
- **Input**: C++ class declaration
- **Output**: Vector of VarDecl pointers to static members
- **Logic**:
  ```cpp
  Walk record->decls()
  For each decl:
      If VarDecl && isStaticDataMember() → add to vector
  Return staticMembers
  ```
- **Uses from Context**: NONE
- **Test Coverage**: Exists (NameManglerStaticMemberTest)
- **Migration**: Convert to static predicate in handler

**Status**: ✓ Can remain as-is (pure detection)

---

#### 2. `generateStaticDeclaration(VarDecl* staticMember, HandlerContext& ctx)`
- **Purpose**: Create C extern declaration for header file
- **Input**: Static member from C++ AST
- **Output**: C VarDecl with SC_Extern storage class
- **Pattern**:
  ```
  C++: static int count;
  C:   extern int Counter__count;
  ```
- **Logic Flow**:
  1. Get owning class from DeclContext
  2. Generate mangled name via `getMangledName()`
  3. Get C++ type (preserves const)
  4. Create C VarDecl in C TranslationUnit
  5. Set storage class to SC_Extern
  6. Return VarDecl

- **HandlerContext Dependencies**:
  - `ctx.getCContext()` → Get C ASTContext
  - `cContext.getTranslationUnitDecl()` → Get C TU
  - `cContext.Idents.get(mangledName)` → Get identifier

- **Migration Target**:
  - `cASTContext` parameter in visitor (passed directly)
  - `cASTContext.getTranslationUnitDecl()` (same call)
  - `cASTContext.Idents.get()` (same call)

**Status**: ✓ Direct conversion possible

---

#### 3. `generateStaticDefinition(VarDecl* staticMember, HandlerContext& ctx)`
- **Purpose**: Create C global variable definition for implementation file
- **Input**: Static member with definition
- **Output**: C VarDecl with SC_None and initializer
- **Pattern**:
  ```
  C++: int Counter::count = 0;
  C:   int Counter__count = 0;
  ```
- **Logic Flow**:
  1. Get owning class from DeclContext
  2. Generate mangled name via `getMangledName()`
  3. Get C++ type (preserves const)
  4. Get initializer expression
  5. Create C VarDecl in C TranslationUnit
  6. Set storage class to SC_None (global scope)
  7. Set initializer if present
  8. Return VarDecl

- **HandlerContext Dependencies**: Same as `generateStaticDeclaration()`

- **Migration Target**: Direct conversion to handler visitor

**Status**: ✓ Direct conversion possible

---

#### 4. `isStaticMemberDefinition(const VarDecl* varDecl)`
- **Purpose**: Identify out-of-class static member definitions
- **Input**: VarDecl to classify
- **Output**: Boolean - is this a static member definition?
- **Logic**: Check three conditions:
  1. `isStaticDataMember()` - is static member
  2. `isFileVarDecl()` - is at file scope
  3. `isThisDeclarationADefinition()` - has definition

- **Uses from Context**: NONE
- **Test Coverage**: Exists
- **Migration**: Convert to static predicate or utility

**Status**: ✓ Can remain as-is (pure logic)

---

#### 5. `getOwningClass(const VarDecl* definition)`
- **Purpose**: Find the class that owns a static member definition
- **Input**: Static member definition VarDecl
- **Output**: CXXRecordDecl of owning class
- **Logic**: Cast DeclContext to CXXRecordDecl
- **Uses from Context**: NONE
- **Test Coverage**: Exists
- **Migration**: Convert to static utility

**Status**: ✓ Can remain as-is (pure logic)

---

### Summary: Public Methods to Migrate

| Method | Type | Dependencies | Migration Path |
|--------|------|--------------|-----------------|
| `detectStaticMembers()` | Detection | None | Keep as static utility |
| `generateStaticDeclaration()` | Translation | ctx.getCContext() | Move to visitor, use cASTContext param |
| `generateStaticDefinition()` | Translation | ctx.getCContext() | Move to visitor, use cASTContext param |
| `isStaticMemberDefinition()` | Detection | None | Keep as static utility |
| `getOwningClass()` | Lookup | None | Keep as static utility |

---

## Part 2: Dependencies Analysis

### HandlerContext Requirements

StaticMemberTranslator uses HandlerContext for:

```cpp
// In generateStaticDeclaration() and generateStaticDefinition():
auto& cContext = ctx.getCContext();
auto* cTU = cContext.getTranslationUnitDecl();
// ... later:
&cContext.Idents.get(mangledName)
```

**Key Points**:
1. Only accesses `getCContext()` method
2. getCContext() returns `ASTContext&`
3. ASTContext provides standard Clang API
4. No special HandlerContext features used

### Dispatcher Architecture Features

**CppToCVisitorDispatcher provides**:

```cpp
// Mappers (not needed for static member translation)
cpptoc::PathMapper& getPathMapper() const;
cpptoc::DeclMapper& getDeclMapper() const;
cpptoc::TypeMapper& getTypeMapper() const;
cpptoc::ExprMapper& getExprMapper() const;
cpptoc::StmtMapper& getStmtMapper() const;

// Helper
std::string getTargetPath(...);
```

**For Static Member Handler**:
- DON'T need: DeclMapper, TypeMapper, ExprMapper, StmtMapper
- DON'T need: PathMapper or getTargetPath()
- DO need: Direct cASTContext parameter (passed in visitor)
- DO need: NameMangler (directly include and call)

### Migration: Dependency Mapping

| Current (HandlerContext) | New (Dispatcher) | Notes |
|--------------------------|------------------|-------|
| `ctx.getCContext()` | `cASTContext` param | Passed directly to visitor |
| `cContext.getTranslationUnitDecl()` | `cASTContext.getTranslationUnitDecl()` | Same API |
| `cContext.Idents.get()` | `cASTContext.Idents.get()` | Same API |
| N/A | `cppASTContext` param | Source AST context |
| N/A | `disp` parameter | For future recursive dispatch |

**Result**: ✓ Zero breaking changes - direct parameter substitution

---

## Part 3: Core Translation Logic

### Name Mangling Approach

**Current Implementation** (line 202-209):
```cpp
std::string getMangledName(
    CXXRecordDecl* record,
    VarDecl* member,
    HandlerContext& ctx
) {
    // Uses free function from NameMangler
    return cpptoc::mangle_static_member(member);
}
```

**Key Points**:
1. Single call to `cpptoc::mangle_static_member(member)`
2. Pattern: `ClassName__memberName`
3. NameMangler.h contains the function (line 235-237)
4. No HandlerContext interaction - just calls NameMangler

**Migration**:
- Direct `#include "NameMangler.h"`
- Call `cpptoc::mangle_static_member(member)` in handler
- No change to logic

**Example Manglings** (from tests):
```cpp
"Counter::count"     → "Counter__count"
"Outer::Inner::value" → "Outer__Inner__value"
```

**Test File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/unit/helpers/NameManglerStaticMemberTest.cpp`

---

### VarDecl Creation Logic

Both declaration and definition follow similar pattern:

#### Declare Creation (lines 80-89)
```cpp
VarDecl* cDecl = VarDecl::Create(
    cContext,                           // ASTContext - FROM cASTContext param
    cTU,                                // DeclContext - FROM cASTContext.getTranslationUnitDecl()
    SourceLocation(),                   // Begin location - empty is fine
    SourceLocation(),                   // Location - empty is fine
    &cContext.Idents.get(mangledName), // Identifier - FROM mangled name
    cType,                              // Type - FROM staticMember->getType()
    nullptr,                            // TypeSourceInfo - null is ok
    SC_Extern                           // Storage class - EXTERN for declaration
);
```

#### Definition Creation (lines 137-146)
```cpp
VarDecl* cDecl = VarDecl::Create(
    cContext,                           // ASTContext - FROM cASTContext param
    cTU,                                // DeclContext - FROM cASTContext.getTranslationUnitDecl()
    SourceLocation(),                   // Begin location
    SourceLocation(),                   // Location
    &cContext.Idents.get(mangledName), // Identifier - SAME mangled name
    cType,                              // Type - FROM staticMember->getType()
    nullptr,                            // TypeSourceInfo
    SC_None                             // Storage class - NONE for definition (global)
);
```

**Key Differences**:
1. Storage class: SC_Extern (declaration) vs SC_None (definition)
2. Definition adds initializer: `cDecl->setInit(cInitializer);`
3. Otherwise identical

**Special Handling**:
- Const qualifier: Preserved in cType (already in staticMember->getType())
- Initializer: Optional, extracted from staticMember->getInit()
- Type translation: Currently NO-OP (TODO comment in code)
  - Works for primitive types
  - Future: May need type translation for complex types

---

### Special Logic Preservation

**Item 1: Type Preservation**
```cpp
// From lines 68-72
QualType cppType = staticMember->getType();
// TODO: Translate C++ type to C type
// For now, use the same type (works for primitive types)
QualType cType = cppType;
```
**Action**: Keep as-is, preserve TODO comment for future enhancement

**Item 2: Initializer Preservation**
```cpp
// From line 126
Expr* initializer = staticMember->getInit();
// TODO: Translate initializer expression from C++ to C
// For now, use the same expression
Expr* cInitializer = initializer;
```
**Action**: Keep as-is, preserve TODO comment

**Item 3: Class Lookup Pattern**
```cpp
// From line 59
auto* record = dyn_cast<CXXRecordDecl>(staticMember->getDeclContext());
if (!record) {
    return nullptr; // Error handling
}
```
**Action**: Keep null check for safety

---

## Part 4: Integration Requirements

### Handler Registration Pattern

**Reference** (from VariableHandler.h):
```cpp
class VariableHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Decl* D);
    static void handleVariable(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );
};
```

### StaticMemberHandler Will Have

```cpp
class StaticMemberHandler {
public:
    // Register with dispatcher
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    // Predicate: Identify static member VarDecls
    static bool canHandle(const clang::Decl* D);

    // Visitor: Translate static member to C global variable
    static void handleStaticMember(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    // Utility: Check if this is a member definition (optional, can keep in StaticMemberTranslator)
    static bool isStaticMemberDefinition(const clang::VarDecl* varDecl);
    static clang::CXXRecordDecl* getOwningClass(const clang::VarDecl* definition);
};
```

### Predicate Logic

**Question**: What should `canHandle()` match?

**Options**:
1. Match all VarDecl → Also catches global static variables
2. Match only static data members → Safer, more specific
3. Match based on DeclContext → Most accurate

**Recommended**: Option 2 - Match only static data members

```cpp
bool StaticMemberHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    if (D->getKind() != clang::Decl::Var) {
        return false; // Not a VarDecl at all
    }

    auto* varDecl = llvm::cast<clang::VarDecl>(D);

    // Only handle static DATA members (not instance members)
    // NOT instance members (handled by RecordHandler)
    // NOT local static variables (handled by VariableHandler)
    if (varDecl->isStaticDataMember()) {
        return true; // This is a static member!
    }

    return false;
}
```

**Rationale**:
- `isStaticDataMember()` is specific to class static members
- Distinguishes from file/function scope static (handled elsewhere)
- VariableHandler doesn't currently match static members
- No overlap with other handlers

---

## Part 5: Migration Checklist

### Phase 1: Create Handler Skeleton
- [ ] Create `/include/dispatch/StaticMemberHandler.h`
- [ ] Create `/src/dispatch/StaticMemberHandler.cpp`
- [ ] Implement basic structure with registerWith, canHandle, handleStaticMember
- [ ] Add #include for NameMangler

### Phase 2: Migrate Logic
- [ ] Copy detection and utility functions (detectStaticMembers, isStaticMemberDefinition, getOwningClass)
- [ ] Migrate generateStaticDeclaration() logic to handler
- [ ] Migrate generateStaticDefinition() logic to handler
- [ ] Replace HandlerContext with direct ASTContext parameters
- [ ] Update comments to reference new architecture

### Phase 3: Create Handler Tests
- [ ] Create `/tests/unit/dispatch/StaticMemberHandlerTest.cpp`
- [ ] Test predicate with various VarDecl types
- [ ] Test declaration generation with assertions on VarDecl properties
- [ ] Test definition generation with initializers
- [ ] Test error cases (nullptr inputs, non-members)

### Phase 4: Integration
- [ ] Register handler in TranslationUnitHandler (if needed)
- [ ] Verify handler matches static members in integration tests
- [ ] Run full test suite
- [ ] Verify no regressions in related tests

### Phase 5: Cleanup
- [ ] Keep or deprecate original StaticMemberTranslator class
  - Option A: Remove entirely (replace all usages with handler)
  - Option B: Keep as deprecated utility (may have other usages)
- [ ] Update CMakeLists.txt if structure changes
- [ ] Update CLAUDE.md with completion notes

---

## Part 6: Code Mappings

### HandlerContext → Dispatcher Equivalents

| Context Element | Old Location | New Location | Notes |
|-----------------|--------------|--------------|-------|
| C ASTContext | `ctx.getCContext()` | `cASTContext` parameter | Direct function parameter |
| C TranslationUnit | `cContext.getTranslationUnitDecl()` | `cASTContext.getTranslationUnitDecl()` | Same API call |
| Identifiers | `cContext.Idents.get(name)` | `cASTContext.Idents.get(name)` | Same API call |
| Name mangling | `cpptoc::mangle_static_member()` | `cpptoc::mangle_static_member()` | Direct function call |
| Mappers | Not used | Available via `disp` | Optional for future features |

### Visitor Signature Mapping

**Old Pattern** (with HandlerContext):
```cpp
void generateStaticDeclaration(
    VarDecl* staticMember,
    HandlerContext& ctx
) {
    auto& cContext = ctx.getCContext();
    // ... use cContext
}
```

**New Pattern** (with Dispatcher):
```cpp
void StaticMemberHandler::handleStaticMember(
    const CppToCVisitorDispatcher& disp,      // NEW: For future recursive dispatch
    const clang::ASTContext& cppASTContext,  // NEW: Source AST
    clang::ASTContext& cASTContext,          // REPLACES: ctx.getCContext()
    const clang::Decl* D                      // NEW: Dispatcher pattern
) {
    auto* varDecl = llvm::cast<clang::VarDecl>(D);
    // ... use cASTContext directly
}
```

---

## Part 7: Risk Assessment

### Low Risk Factors
1. ✓ Handler only creates VarDecl nodes, doesn't modify existing AST
2. ✓ No recursive dispatch needed (static members are leaves)
3. ✓ No complex type translation (TODO comments preserved)
4. ✓ Existing unit tests fully cover logic
5. ✓ Well-isolated functionality with clear boundaries

### Potential Issues
1. **Type Translation**: Currently disabled (lines 70-72, 121-123)
   - Mitigation: Keep TODO, add comment about future work

2. **Initialization Translation**: Currently disabled (lines 128-130)
   - Mitigation: Keep TODO, works for literal initializers

3. **Storage Class Handling**: SC_Extern vs SC_None is critical
   - Mitigation: Clear code comment explaining difference

### Testing Strategy
1. Predicate tests: Verify handler matches only static data members
2. Declaration tests: Verify extern VarDecl creation
3. Definition tests: Verify global VarDecl with initializer
4. Integration tests: Verify handler works in translation pipeline

---

## Part 8: Open Questions & Decisions

### Question 1: Should we keep StaticMemberTranslator class?

**Option A: Remove entirely**
- Pros: Clean migration, no legacy code
- Cons: Might be used elsewhere, requires broader refactoring

**Option B: Keep as deprecated utility**
- Pros: Backward compatible, gradual migration
- Cons: Dual implementations, technical debt

**Recommendation**: Search codebase for StaticMemberTranslator usage first, then decide

### Question 2: Where should handler be registered?

**Option A: TranslationUnitHandler**
- Registers all top-level handlers during TU translation

**Option B: Standalone registration**
- Called explicitly during initialization

**Option C: RecordHandler**
- Register when processing class declarations

**Recommendation**: Depends on when static members are encountered in translation flow. Check existing class handling pattern.

### Question 3: Should predicate handle definition vs declaration separately?

**Current Design**: Single predicate matches all static member VarDecls

**Alternative**: Separate predicates for declaration vs definition

**Recommendation**: Keep current design - same handler processes both, uses `isStaticMemberDefinition()` to branch logic

---

## Part 9: Files to Create/Modify

### Files to Create
```
/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/dispatch/StaticMemberHandler.h
/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/StaticMemberHandler.cpp
/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/unit/dispatch/StaticMemberHandlerTest.cpp
```

### Files to Modify
```
/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/CMakeLists.txt (if adding new source files)
/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/helpers/StaticMemberTranslator.h (optional: add deprecation notice)
/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/helpers/StaticMemberTranslator.cpp (optional: add deprecation notice)
```

### Files Using StaticMemberTranslator (requires search)
```
grep -r "StaticMemberTranslator" /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c --include="*.h" --include="*.cpp"
```

---

## Part 10: Summary Table

| Aspect | Status | Notes |
|--------|--------|-------|
| **Public Methods** | 5 methods | detectStaticMembers, generateStaticDeclaration, generateStaticDefinition, isStaticMemberDefinition, getOwningClass |
| **HandlerContext Usage** | Minimal | Only getCContext() method used |
| **Dispatcher Compatibility** | High | Direct parameter substitution possible |
| **Name Mangling** | Simple | Single function call to mangle_static_member() |
| **VarDecl Creation** | Straightforward | Standard Clang API, 2 variants (extern vs global) |
| **Type Translation** | Deferred | TODO comment, works for primitives |
| **Initializer Translation** | Deferred | TODO comment, works for literals |
| **Existing Tests** | Excellent | NameManglerStaticMemberTest.cpp fully covers logic |
| **Risk Level** | LOW | Well-isolated, no complex dependencies |
| **Estimated Effort** | 2-3 hours | Handler skeleton + logic migration + tests |

---

## Conclusion

StaticMemberTranslator is an ideal candidate for dispatcher pattern migration. The translation logic is straightforward, dependencies are minimal (only cASTContext), and existing tests provide excellent coverage. The handler can be implemented following the VariableHandler pattern with minimal changes to core logic.

**Next Steps**:
1. Search codebase for all StaticMemberTranslator usages
2. Verify current location in translation pipeline
3. Implement StaticMemberHandler following VariableHandler pattern
4. Create comprehensive unit tests
5. Integrate handler into translation pipeline
6. Run full test suite for regression verification

# Static Method Handler Architecture - Executive Summary

## Analysis Results

This analysis examined the dispatcher pattern implementation across FunctionHandler, RecordHandler, and NamespaceHandler to understand how static methods should be handled in the transpiler architecture.

---

## Key Findings

### 1. Established Dispatcher Pattern

The CppToCVisitorDispatcher uses **Chain of Responsibility** with:
- **Predicates** for filtering (canHandle)
- **Visitors** for processing (handleXXX)
- **Mappers** for retrieving/storing translations
- **Recursive dispatch** for child nodes

### 2. Type Matching Strategy

All handlers use **exact type matching** via `D->getKind()`:
```cpp
// CORRECT: Exact match
if (D->getKind() == clang::Decl::Function) { ... }

// WRONG: Would match derived types
if (llvm::isa<clang::FunctionDecl>(D)) { ... }  // Matches CXXMethodDecl!
```

**Critical:** For static methods, use:
```cpp
if (D->getKind() == clang::Decl::CXXMethod) {  // Exact type
    const auto* m = llvm::cast<clang::CXXMethodDecl>(D);
    return m->isStatic();  // Static filter
}
```

### 3. Parent Context Detection

Every declaration has a `getDeclContext()` indicating its parent:
```cpp
// Get method's class
const auto* classDecl = method->getParent();  // Always CXXRecordDecl

// Check if class is in namespace
if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
        classDecl->getDeclContext())) {
    // Apply namespace prefix to class name
    std::string nsPath = NamespaceHandler::getNamespacePath(ns);
}
```

### 4. Name Mangling Convention

**ALL separators use `__` (double underscore)** for C++ scope resolution:
- **Namespace level separator:** `__` (double underscore)
- **Class-to-method separator:** `__` (double underscore)

```
Namespace__ClassName__methodName

Examples:
- game::Entity::update() → game__Entity__update
- myns::Counter::getValue() → myns__Counter__getValue
- Counter::getValue() → Counter__getValue (no namespace)
```

**Why double underscore everywhere?**
- `__` consistently represents C++ scope resolution operator `::`
- Matches NamespaceHandler: `A::B` → `A__B`
- Matches RecordHandler: `namespace A { struct S; }` → `A__S`
- Matches nested structs: `Outer::Inner` → `Outer__Inner`
- **Consistency:** All `::` in C++ becomes `__` in C

### 5. Static vs Instance Method Distinction

| Aspect | Instance Methods | Static Methods |
|--------|------------------|-----------------|
| Handler | MethodHandler | StaticMethodHandler |
| Predicate | `!method->isStatic()` | `method->isStatic()` |
| First Parameter | `struct ClassName* this` | NONE |
| C Function Name | `ClassName__methodName` | `ClassName__methodName` |
| Registration | Phase 6 | Phase 7 |
| Dependencies | All of Phase 1-5 | All of Phase 1-6 |

**Critical:** Filters must be complementary:
- MethodHandler MUST return false for static methods
- StaticMethodHandler MUST return false for instance methods
- Prevents duplicate handling

### 6. Handler Registration Order

Must follow dependency chain:
```
1. TypeHandler (base types)
2. NamespaceHandler (scope tracking)
3. ParameterHandler (function signatures)
4. FunctionHandler (free functions)
5. RecordHandler (structs/classes)
6. MethodHandler (instance methods)
7. StaticMethodHandler (static methods)
```

**Why?** Each handler depends on outputs of previous handlers through mappers.

### 7. No This Parameter for Static Methods

Key translation difference:
```cpp
// Instance method: add 'this' parameter
void MethodHandler::handleMethod(...) {
    if (!method->isStatic()) {  // Instance method
        cParams.push_back(createThisParameter(...));  // Add 'this'
    }
}

// Static method: NO 'this' parameter
void StaticMethodHandler::handleStaticMethod(...) {
    // method->isStatic() is guaranteed true here
    // NO 'this' parameter added
    // Just translate regular parameters
}
```

---

## Architecture Recommendations

### 1. Create StaticMethodHandler

**New Files:**
- `include/dispatch/StaticMethodHandler.h`
- `src/dispatch/StaticMethodHandler.cpp`

**Pattern (follows FunctionHandler/RecordHandler):**
```cpp
class StaticMethodHandler {
    static void registerWith(CppToCVisitorDispatcher&);
    static bool canHandle(const clang::Decl*);
    static void handleStaticMethod(...);
    // Helper methods
};
```

### 2. canHandle() Implementation

```cpp
bool StaticMethodHandler::canHandle(const clang::Decl* D) {
    assert(D);

    // Exact type matching
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    // Exclude special methods
    const auto* m = llvm::cast<clang::CXXMethodDecl>(D);
    if (llvm::isa<clang::CXXConstructorDecl>(m) ||
        llvm::isa<clang::CXXDestructorDecl>(m)) {
        return false;
    }

    // Match static methods
    return m->isStatic();
}
```

### 3. handleStaticMethod() Structure

Following established pattern:
1. Assert preconditions
2. Extract properties (name, class, namespace)
3. Check parent context (namespace prefix)
4. Mangle name (Namespace__ClassName__methodName)
5. Translate return type (dispatch to TypeMapper)
6. Translate parameters (dispatch to ParameterHandler)
7. Translate body (dispatch to StmtMapper)
8. Create C function (NO 'this' parameter)
9. Get target path and C TranslationUnit
10. Add to C TranslationUnit
11. Register location in PathMapper

### 4. Complementary Filter with MethodHandler

**Modify MethodHandler::canHandle():**
```cpp
bool MethodHandler::canHandle(const clang::Decl* D) {
    const auto* m = llvm::dyn_cast<clang::CXXMethodDecl>(D);
    if (!m) return false;

    // Exclude special methods
    if (llvm::isa<clang::CXXConstructorDecl>(m) ||
        llvm::isa<clang::CXXDestructorDecl>(m)) {
        return false;
    }

    // CRITICAL: Exclude static methods (let StaticMethodHandler handle them)
    return !m->isStatic();
}
```

### 5. Registration Placement

Register StaticMethodHandler AFTER MethodHandler in initialization:
```cpp
// In CppToCVisitor or main initialization
MethodHandler::registerWith(dispatcher);
StaticMethodHandler::registerWith(dispatcher);
```

This ensures clean separation with MethodHandler filtering instance methods and StaticMethodHandler filtering static methods.

---

## Design Rationale

### Why Separate StaticMethodHandler?

1. **Single Responsibility:** Each handler has one clear purpose
2. **Independent Testing:** Can test static method translation separately
3. **Maintainability:** Changes to static methods don't affect instance methods
4. **Consistency:** Follows dispatcher pattern used for all other declarations
5. **Clarity:** Code intent is explicit (handler name matches responsibility)

### Why Double Underscore for All Separators?

1. **`__` (double underscore):** Consistently represents C++ `::` scope resolution
2. **Matches project-wide convention:**
   - NamespaceHandler: `A::B` → `A__B`
   - RecordHandler: `namespace A { struct S; }` → `A__S`
   - Nested structs: `Outer::Inner` → `Outer__Inner`
3. **Single source of truth:** All C++ scope operators become `__` in C
4. **Avoids confusion:** No mixed separator rules to remember
5. **Avoids collisions:** Unique naming pattern prevents name conflicts

### Why This Registration Order?

1. **Dependency order:** Handler can only use outputs from previously registered handlers
2. **Mapper availability:** TypeMapper and DeclMapper must be populated before use
3. **Forward references:** RecordHandler creates structs needed by method handlers
4. **Logical flow:** Scopes → declarations → methods

---

## Implementation Notes

### File Modifications

**New Files:**
- `include/dispatch/StaticMethodHandler.h` - Header with interface
- `src/dispatch/StaticMethodHandler.cpp` - Implementation

**Modified Files:**
- `src/handlers/MethodHandler.cpp` - Add `!m->isStatic()` filter to canHandle()
- Initialization code that registers handlers - Add StaticMethodHandler registration

**Existing Files (No Changes):**
- CppToCVisitorDispatcher pattern remains unchanged
- Mapper interfaces remain unchanged
- No changes to FunctionHandler, RecordHandler, NamespaceHandler

### Backward Compatibility

- StaticMethodHandler is NEW - no compatibility concerns
- MethodHandler change is ADDITIVE (excluding static methods it previously didn't handle correctly)
- All existing instance method tests should pass

### Testing Strategy

**Unit Tests (StaticMethodHandlerTest):**
- Test canHandle() predicate
- Test handleStaticMethod() translation
- Test name mangling
- Test parameter translation
- Test return type translation
- Test namespace prefix application

**Integration Tests:**
- Class with both static and instance methods
- Static and instance methods in namespace
- Parameter type conversions
- Return type conversions

**Verification:**
- All existing tests continue to pass
- New tests cover static method cases
- Dispatcher correctly routes static vs instance methods

---

## Summary Table

| Question | Answer |
|----------|--------|
| **How to identify static methods?** | Use `D->getKind() == Decl::CXXMethod` AND `method->isStatic()` |
| **How to name in C?** | `ClassName__methodName` or `Namespace__ClassName__methodName` |
| **What's different from free functions?** | Class context (parent DeclContext is CXXRecordDecl) |
| **What's different from instance methods?** | NO 'this' parameter, static filter in predicate |
| **Where to check parent context?** | `method->getParent()` → class, `class->getDeclContext()` → namespace |
| **Registration order matters?** | YES - after NamespaceHandler, ParameterHandler, RecordHandler, MethodHandler |
| **Pattern summary?** | registerWith(), canHandle(), handleStaticMethod() + helpers |

---

## Next Steps

1. **Create StaticMethodHandler files** using provided templates
2. **Implement canHandle()** with exact type matching and isStatic() filter
3. **Implement handleStaticMethod()** following FunctionHandler pattern
4. **Modify MethodHandler** to exclude static methods
5. **Register StaticMethodHandler** after MethodHandler
6. **Write unit tests** for predicate and translation
7. **Write integration tests** for complete classes
8. **Verify backward compatibility** with existing tests
9. **Run linting** before committing
10. **Document** any deviations from pattern

---

## References

- **Dispatcher Pattern:** `include/dispatch/CppToCVisitorDispatcher.h`
- **FunctionHandler Pattern:** `include/dispatch/FunctionHandler.h`, `src/dispatch/FunctionHandler.cpp`
- **RecordHandler Pattern:** `include/dispatch/RecordHandler.h`, `src/dispatch/RecordHandler.cpp`
- **NamespaceHandler:** `include/dispatch/NamespaceHandler.h`, `src/dispatch/NamespaceHandler.cpp`
- **MethodHandler (Comparison):** `include/handlers/MethodHandler.h`, `src/handlers/MethodHandler.cpp`

---

## Documents

- **Detailed Analysis:** `STATIC_METHOD_HANDLER_ANALYSIS.md`
- **Quick Reference:** `STATIC_METHOD_QUICK_REFERENCE.md`
- **This Summary:** `STATIC_METHOD_HANDLER_SUMMARY.md`

# Static Method Handler - Quick Reference

## Pattern Summary

### Registration
```cpp
// In initialization
StaticMethodHandler::registerWith(dispatcher);
```

### canHandle() Predicate
```cpp
bool StaticMethodHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // 1. Exact type matching
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    // 2. Exclude constructors/destructors
    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // 3. Match static methods ONLY
    return method->isStatic();
}
```

### Name Mangling
```
Simple:       ClassName__methodName
Namespaced:   Namespace__ClassName__methodName
Nested NS:    Namespace1__Namespace2__ClassName__methodName

Separators:
- Single underscore (_) between class and method
- Double underscore (__) between namespace levels
```

---

## Implementation Checklist

- [ ] Create `include/dispatch/StaticMethodHandler.h`
- [ ] Create `src/dispatch/StaticMethodHandler.cpp`
- [ ] Implement `canHandle()` - match static CXXMethodDecl only
- [ ] Implement `handleStaticMethod()` - translator
- [ ] Implement `mangleStaticMethodName()` - name mangling
- [ ] Implement `getClassName()` - extract class name
- [ ] Implement `translateParameters()` - parameter delegation
- [ ] Call `NamespaceHandler::getNamespacePath()` for namespace prefix
- [ ] Dispatch parameter translation to ParameterHandler
- [ ] Dispatch type translation to TypeMapper
- [ ] Dispatch body translation to StmtMapper
- [ ] Add to C TranslationUnit via PathMapper
- [ ] Register location in PathMapper

---

## Key Differences from MethodHandler

| Aspect | Instance Method | Static Method |
|--------|-----------------|---------------|
| Filter | `!method->isStatic()` | `method->isStatic()` |
| First Parameter | `this` pointer | NONE |
| Signature | `ClassName_method(struct ClassName* this, ...)` | `ClassName_method(...)` |
| Handler | MethodHandler | StaticMethodHandler |

---

## DeclContext Checking Pattern

```cpp
// Check if class is in namespace
const auto* classDecl = method->getParent();  // Always CXXRecordDecl

if (const auto* nsDecl = llvm::dyn_cast<clang::NamespaceDecl>(
        classDecl->getDeclContext())) {
    // Class is in namespace
    std::string nsPrefix = NamespaceHandler::getNamespacePath(nsDecl);
    if (!nsPrefix.empty()) {
        className = nsPrefix + "__" + className;
    }
}
```

---

## Registration Order

```cpp
TypeHandler::registerWith(dispatcher);              // 1st
NamespaceHandler::registerWith(dispatcher);         // 2nd
ParameterHandler::registerWith(dispatcher);         // 3rd
FunctionHandler::registerWith(dispatcher);          // 4th
RecordHandler::registerWith(dispatcher);            // 5th
MethodHandler::registerWith(dispatcher);            // 6th
StaticMethodHandler::registerWith(dispatcher);      // 7th
```

**Why:** StaticMethodHandler depends on:
- TypeHandler (for return type translation)
- NamespaceHandler (for namespace paths)
- ParameterHandler (for parameter translation)
- RecordHandler (for class definitions)
- MethodHandler already registered (no conflict due to isStatic() filter)

---

## No Overlap Guarantee

```
CXXMethodDecl
├─ Constructor → ConstructorHandler
├─ Destructor → DestructorHandler
└─ Regular Method
   ├─ isStatic() == true → StaticMethodHandler
   └─ isStatic() == false → MethodHandler
```

**Filters ensure zero overlap:**
- MethodHandler: `!isa<Constructor> && !isa<Destructor> && !isStatic()`
- StaticMethodHandler: `!isa<Constructor> && !isa<Destructor> && isStatic()`

---

## Testing Cases

### Unit Tests
- [ ] Simple static method (no params, void return)
- [ ] Static method with parameters
- [ ] Static method with return value
- [ ] Static method in namespace
- [ ] Static method with reference parameters (→ pointers)
- [ ] canHandle() filters correctly
- [ ] Parameter translation
- [ ] Return type translation

### Integration Tests
- [ ] Class with instance AND static methods
- [ ] Namespace class with both method types
- [ ] Static method call expressions
- [ ] Parameter type conversions

---

## Common Pitfalls

| Pitfall | Prevention |
|---------|-----------|
| Using `isa<FunctionDecl>` instead of `getKind()` | Use `getKind() == Decl::CXXMethod` |
| Forgetting to check `isStatic()` | Always add `method->isStatic()` check |
| Adding 'this' parameter | Guard with `!method->isStatic()` in MethodHandler |
| Wrong separator (single vs double) | Use `_` for class, `__` for namespace |
| Not checking namespace of class | Call `getParent()->getDeclContext()` |
| Not handling parameter dispatch | Delegate to ParameterHandler via dispatch() |
| Not handling type dispatch | Delegate to TypeMapper via dispatch() |
| Incorrect registration order | Place AFTER NamespaceHandler, ParameterHandler |

---

## File Locations

- Dispatcher header: `include/dispatch/CppToCVisitorDispatcher.h`
- StaticMethodHandler header: `include/dispatch/StaticMethodHandler.h` (NEW)
- StaticMethodHandler impl: `src/dispatch/StaticMethodHandler.cpp` (NEW)
- Reference handlers: `src/dispatch/FunctionHandler.cpp`, `src/dispatch/RecordHandler.cpp`
- MethodHandler (comparison): `src/handlers/MethodHandler.cpp`

---

## Verification Commands

```bash
# Find all CXXMethodDecl in test files
grep -r "isStatic()" /path/to/tests/

# Find MethodHandler registrations
grep -r "MethodHandler::registerWith" /path/to/src/

# Check for type mismatches
grep -r "getKind().*Function" /path/to/src/dispatch/
```

---

## Example Translation

**C++ Code:**
```cpp
namespace game {
    class Entity {
    public:
        int health;
        void takeDamage(int amount) { health -= amount; }
        static int getMaxEntities() { return 100; }
    };
}
```

**C Code (Expected):**
```c
// Forward declarations and struct
struct game__Entity {
    int health;
};

// Instance method
void game__Entity_takeDamage(struct game__Entity* this, int amount) {
    this->health -= amount;
}

// Static method (NO 'this' parameter)
int game__Entity_getMaxEntities(void) {
    return 100;
}
```

---

## Debugging Tips

1. **Check canHandle() filtering:**
   - Add debug output to canHandle()
   - Verify `getKind()` matches expected kind
   - Verify `isStatic()` returns true for static methods

2. **Check handleStaticMethod() translation:**
   - Verify name mangling is correct
   - Verify namespace prefix applied
   - Verify no 'this' parameter added
   - Verify parameters dispatched correctly

3. **Check dispatcher setup:**
   - Verify registration order is correct
   - Verify MethodHandler excludes static methods
   - Verify StaticMethodHandler registered

4. **Debug output:**
   ```cpp
   llvm::outs() << "[StaticMethodHandler] " << what << " → " << result << "\n";
   ```

---

## Performance Notes

- No significant overhead vs MethodHandler
- Single boolean check (`isStatic()`) per method
- Name mangling is O(n) where n = namespace depth
- Parameter translation delegated to existing handlers
- Type translation delegated to existing handlers

---

## Future Enhancements

- [ ] Full overload resolution with parameter-based mangling
- [ ] Template static methods
- [ ] Constexpr static methods
- [ ] Static method pointers/function pointers
- [ ] Static inline methods
- [ ] Static data members (separate handler)

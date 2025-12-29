# C TranslationUnit - Quick Reference Guide

## TL;DR

```
ONE Shared ASTContext (TargetContext singleton)
    │
    ├─ C_TU1 (Vector3D.cpp)   → Vector3D.h, Vector3D.c
    ├─ C_TU2 (Matrix4x4.cpp)  → Matrix4x4.h, Matrix4x4.c
    └─ C_TU3 (main.cpp)       → main.h, main.c

Flow:
  C++ Decl → Builder creates in shared context → Add to per-file C_TU → Emit code
```

---

## Creation

| Task | Code | File |
|------|------|------|
| Get singleton | `TargetContext& ctx = TargetContext::getInstance();` | Any |
| Get shared context | `clang::ASTContext& actx = targetCtx.getContext();` | Any |
| Create builder | `CNodeBuilder builder(targetCtx.getContext());` | CppToCConsumer |
| Create per-file C_TU | `clang::TranslationUnitDecl* c_tu = targetCtx.createTranslationUnit();` | CppToCConsumer |
| Pass to visitor | `CppToCVisitor visitor(..., c_tu, ...);` | CppToCConsumer |

**File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCConsumer.cpp:50-68`

---

## Adding Declarations

| Type | Code | Pattern |
|------|------|---------|
| Any | `C_TranslationUnit->addDecl(node);` | Universal |
| Struct | After `Builder.structDecl()` | Example 2.2 |
| Enum | After `m_enumTranslator->translateEnum()` | Example 2.1 |
| Constructor | After creating func + map | Example 2.3 |
| Method | After creating func + map | Example 2.4 |
| Function | After creating func | Example 2.5 |

**Key**: Add to BOTH per-file C_TU AND shared map if cross-file reference needed.

**File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCVisitor.cpp:200-5338`

---

## Code Generation

| Step | Code | Pattern |
|------|------|---------|
| Count | `std::distance(C_TU->decls().begin(), C_TU->decls().end());` | Example 3.3 |
| Iterate | `for (auto *D : C_TU->decls()) { ... }` | Example 3.1-3.2 |
| Header | `headerGen.printDecl(D, true);` | Example 3.1 |
| Impl | `implGen.printDecl(D, false);` | Example 3.2 |

**File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCConsumer.cpp:263-293`

---

## Cross-File References

| Operation | Code | File |
|-----------|------|------|
| Store | `targetCtx.getCtorMap()[mangled] = func;` | CppToCVisitor |
| Lookup | `auto it = targetCtx.getCtorMap().find(mangled);` | CppToCVisitor |
| Verify | `if (it != map.end()) { func = it->second; }` | CppToCVisitor |

**Maps**:
- `ctorMap` - Constructors
- `methodMap` - Methods
- `dtorMap` - Destructors

**Key**: Use mangled names as keys (strings), not pointers!

---

## Data Structures

### TargetContext (Singleton)
```cpp
class TargetContext {
    static TargetContext* instance;  // ONE instance
    std::unique_ptr<clang::ASTContext> Context;  // Shared for ALL files
    std::map<string, FunctionDecl*> ctorMap, methodMap, dtorMap;
};
```

### CppToCVisitor
```cpp
class CppToCVisitor {
    clang::TranslationUnitDecl* C_TranslationUnit;  // Per-file
    std::map<CXXRecordDecl*, RecordDecl*> cppToCMap;  // Per-file
    TargetContext& targetCtx;  // Reference to shared
};
```

### TranslationUnit (Clang)
```cpp
TranslationUnitDecl {
    vector<Decl*> Decls;  // Iterable via decls()
    void addDecl(Decl*);  // Adds to Decls
};
```

---

## Common Patterns

### Pattern 1: Create and Add Struct
```cpp
// Create via Builder (goes to shared context + shared TU)
RecordDecl *s = Builder.structDecl(name, fields);

// Add to per-file C_TU (CRITICAL!)
C_TranslationUnit->addDecl(s);

// Track mapping
cppToCMap[cpp_class] = s;
```

### Pattern 2: Create Constructor and Share
```cpp
// Create function
FunctionDecl *ctor = Builder.funcDecl(...);

// Add to per-file C_TU
C_TranslationUnit->addDecl(ctor);

// Share with other files
targetCtx.getCtorMap()[mangledName] = ctor;
```

### Pattern 3: Use Constructor from Another File
```cpp
// Lookup
auto it = targetCtx.getCtorMap().find(mangledName);
if (it != targetCtx.getCtorMap().end()) {
    FunctionDecl *ctor = it->second;
    // Use in new CallExpr
}
```

### Pattern 4: Emit Code from C_TU
```cpp
for (auto *D : C_TU->decls()) {
    if (!D->isImplicit()) {
        generator.printDecl(D, headerOnly);
    }
}
```

---

## Important Points

1. **One ASTContext**: All C nodes created in same context (type safety)
2. **Per-File TU**: Each source file gets separate C_TranslationUnit
3. **Two-Step Add**: Create via Builder (shared context) THEN add to per-file C_TU
4. **Map Keys**: Use mangled names (strings) not pointers
5. **Iteration**: Always iterate per-file C_TU, not shared TU
6. **Type Translation**: Convert between C++ context and shared context types
7. **Cleanup**: Call `TargetContext::cleanup()` at program exit

---

## Troubleshooting

| Problem | Cause | Solution |
|---------|-------|----------|
| Decl not in output | Not added to per-file C_TU | Add `C_TU->addDecl(node)` |
| Cross-file ref fails | Not in shared map | Add to `targetCtx.get*Map()` |
| Type mismatch | Mixed contexts | Use `translateTypeToCContext()` |
| Empty output | Empty C_TU | Check all visitor methods add to C_TU |
| Duplicate output | In both shared and per-file TU | Remove from shared TU add |

---

## File Locations

| Component | Header | Implementation |
|-----------|--------|-----------------|
| TargetContext | `/include/TargetContext.h` | `/src/TargetContext.cpp` |
| CppToCVisitor | `/include/CppToCVisitor.h` | `/src/CppToCVisitor.cpp` |
| CppToCConsumer | `/include/CppToCConsumer.h` | `/src/CppToCConsumer.cpp` |
| CNodeBuilder | `/include/CNodeBuilder.h` | (Header-only) |

---

## Key Lines of Code

### Create C_TU
**CppToCConsumer.cpp:60**
```cpp
clang::TranslationUnitDecl* C_TU = targetCtx.createTranslationUnit();
```

### Add to C_TU
**CppToCVisitor.cpp:226, 449, 761, etc.**
```cpp
C_TranslationUnit->addDecl(node);
```

### Iterate C_TU
**CppToCConsumer.cpp:263, 289**
```cpp
for (auto *D : C_TU->decls()) { ... }
```

### Store in map
**CppToCVisitor.cpp:1031** (method example)
```cpp
targetCtx.getMethodMap()[MangledName] = CFunc;
```

### Lookup in map
**CppToCVisitor.cpp:~3000** (usage example)
```cpp
auto it = targetCtx.getMethodMap().find(mangledName);
if (it != targetCtx.getMethodMap().end()) {
    FunctionDecl *func = it->second;
}
```

---

## Memory Management

```
TargetContext (singleton)
  ├─ Owns ASTContext (unique_ptr)
  │  ├─ Owns all Decl* nodes (automatic via ASTContext)
  │  └─ Nodes added to C_TU are references (not copies)
  │
  └─ Maps (string -> Decl*)
     ├─ Keys: mangled names (std::string)
     └─ Values: pointers to nodes in ASTContext

Result: No manual cleanup needed (except TargetContext::cleanup())
```

---

## Summary

**Current Architecture**:
- ONE shared ASTContext for all C nodes
- ONE C_TranslationUnit per source file
- Declarations explicitly added to per-file C_TU
- Cross-file references via shared maps
- Code generation from per-file C_TU

**To Create Multiple C_TUs from One File**:
```cpp
C_TU1 = targetCtx.createTranslationUnit();  // First module
C_TU2 = targetCtx.createTranslationUnit();  // Second module
C_TU3 = targetCtx.createTranslationUnit();  // Third module

// Route declarations based on filter logic
if (isVectorClass) C_TU1->addDecl(node);
if (isMatrixClass) C_TU2->addDecl(node);
if (isUtility)     C_TU3->addDecl(node);
```

**All C_TU1/2/3 share same ASTContext (type compatible)**

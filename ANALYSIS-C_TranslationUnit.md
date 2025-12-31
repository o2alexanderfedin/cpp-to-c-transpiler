# C TranslationUnit Creation and Management Analysis

## Executive Summary

The transpiler uses a **3-stage pipeline** with **separate ASTContexts** for C++ parsing and C output generation:

1. **C++ ASTContext**: One per source file (from Clang frontend)
2. **Shared Target ASTContext**: ONE for all C nodes (managed by TargetContext singleton)
3. **Per-File C_TranslationUnit**: ONE per source file in shared target context

This design enables:
- Multi-file transpilation with proper file-based output
- Shared cross-file references (constructors, methods, destructors)
- Clean separation between C++ parsing and C code generation

---

## Architecture Overview

### 1. TargetContext (Singleton) - Shared for ALL Files

**Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/TargetContext.h`

```cpp
class TargetContext {
private:
    // Infrastructure for target ASTContext
    std::unique_ptr<clang::DiagnosticConsumer> DiagClient;
    std::unique_ptr<clang::FileManager> FileMgr;
    std::unique_ptr<clang::SourceManager> SourceMgr;
    std::unique_ptr<clang::DiagnosticsEngine> Diagnostics;
    std::unique_ptr<clang::TargetInfo> Target;
    std::unique_ptr<clang::IdentifierTable> Idents;
    std::unique_ptr<clang::SelectorTable> Selectors;
    std::unique_ptr<clang::Builtin::Context> Builtins;

    // THE SHARED TARGET ASTCONTEXT
    std::unique_ptr<clang::ASTContext> Context;  // ONE for all files!

    // Singleton instance
    static TargetContext* instance;

    // Shared maps across files (use mangled names as keys!)
    std::map<std::string, clang::FunctionDecl *> ctorMap;
    std::map<std::string, clang::FunctionDecl *> methodMap;
    std::map<std::string, clang::FunctionDecl *> dtorMap;

public:
    static TargetContext& getInstance();  // Singleton access
    static void cleanup();

    clang::ASTContext& getContext();                    // Get shared target context
    clang::TranslationUnitDecl* createTranslationUnit(); // Create ONE C_TU per file

    // Access shared maps
    std::map<std::string, clang::FunctionDecl *>& getCtorMap();
    std::map<std::string, clang::FunctionDecl *>& getMethodMap();
    std::map<std::string, clang::FunctionDecl *>& getDtorMap();
};
```

**Key Points**:
- ONE shared ASTContext for all C output nodes
- Each file creates its OWN C_TranslationUnit in this shared context
- Maps use **mangled names as keys** (not pointers) to work across different C++ ASTContexts
- Singleton pattern ensures only one instance across entire transpilation run

---

## Data Flow: How C_TUs Are Created and Used

### Flow Diagram

```
For Each C++ Source File:
    ├─ Clang Frontend
    │  └─ Parses into C++ ASTContext (file-specific)
    │
    ├─ CppToCConsumer::HandleTranslationUnit()
    │  ├─ Get TargetContext singleton
    │  ├─ Create CNodeBuilder(targetCtx.getContext())  // Uses SHARED context
    │  ├─ Create per-file C_TranslationUnit in shared context:
    │  │  └─ C_TU = targetCtx.createTranslationUnit()
    │  │
    │  ├─ Create CppToCVisitor()
    │  │  ├─ Pass C_TU to visitor
    │  │  └─ Pass TargetContext for shared maps
    │  │
    │  ├─ Traverse C++ AST
    │  │  └─ CppToCVisitor creates C nodes in shared context
    │  │  └─ CppToCVisitor adds declarations to its C_TU
    │  │
    │  ├─ Generate code from C_TU
    │  │  └─ Emit .h and .c files
    │  │
    │  └─ Output .h and .c files
    │
    └─ NEXT FILE...
```

---

## 1. CppToCConsumer - Creation Point

**Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCConsumer.cpp`

```cpp
void CppToCConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    // === GET SHARED TARGET CONTEXT ===
    TargetContext& targetCtx = TargetContext::getInstance();

    // === CREATE CNODEBUILDER WITH SHARED CONTEXT ===
    // All C nodes from ALL files are created in this shared context
    clang::CNodeBuilder Builder(targetCtx.getContext());

    // === CREATE PER-FILE C_TRANSLATIONUNIT ===
    // Each source file gets its OWN C_TU in the shared target context
    clang::TranslationUnitDecl* C_TU = targetCtx.createTranslationUnit();
    llvm::outs() << "[Bug #30 FIX] Created C_TU @ " << (void*)C_TU
                 << " for file: " << InputFilename << "\n";

    // === CREATE VISITOR WITH C_TU ===
    // Pass the C_TU to the Visitor so it knows where to add declarations
    CppToCVisitor Visitor(Context, Builder, targetCtx, fileOriginTracker,
                          C_TU, InputFilename);
    Visitor.TraverseDecl(TU);

    // === PROCESS TEMPLATE INSTANTIATIONS ===
    Visitor.processTemplateInstantiations(TU);

    // === VALIDATE C_TU ===
    auto CTU_DeclCount = std::distance(C_TU->decls().begin(), C_TU->decls().end());
    llvm::outs() << "C TranslationUnit has " << CTU_DeclCount
                 << " generated declarations\n";

    // === GENERATE CODE FROM C_TU ===
    // Iterate over C_TU declarations (not original C++ TU!)
    for (auto *D : C_TU->decls()) {
        if (!D->isImplicit()) {
            headerGen.printDecl(D, true);   // Declaration only for headers
        }
    }
    for (auto *D : C_TU->decls()) {
        if (!D->isImplicit()) {
            implGen.printDecl(D, false);    // Full definition for implementation
        }
    }

    // === WRITE OUTPUT FILES ===
    outputMgr.writeFiles(headerContent, implContent);
}
```

**Critical Points**:
1. **One C_TU per file**: `targetCtx.createTranslationUnit()` creates a new TranslationUnit
2. **Shared ASTContext**: Builder uses `targetCtx.getContext()` - all C nodes go here
3. **Visitor receives C_TU**: Visitor stores and adds declarations to this C_TU
4. **CodeGen uses C_TU**: NOT the original C++ TU
5. **Iteration over C_TU**: `for (auto *D : C_TU->decls())`

---

## 2. CppToCVisitor - Declaration Addition

**Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/CppToCVisitor.h`

```cpp
class CppToCVisitor : public clang::RecursiveASTVisitor<CppToCVisitor> {
    clang::ASTContext &Context;              // C++ source context (file-specific)
    clang::CNodeBuilder &Builder;
    TargetContext &targetCtx;                 // Shared target context access
    cpptoc::FileOriginTracker &fileOriginTracker;

    // === PER-FILE C_TRANSLATIONUNIT ===
    clang::TranslationUnitDecl* C_TranslationUnit;  // Passed in constructor

public:
    explicit CppToCVisitor(clang::ASTContext &Context,
                           clang::CNodeBuilder &Builder,
                           TargetContext &targetCtx,
                           cpptoc::FileOriginTracker &tracker,
                           clang::TranslationUnitDecl *C_TU,  // <-- RECEIVED HERE
                           const std::string& currentFile = "");

    clang::TranslationUnitDecl* getCTranslationUnit() const {
        return C_TranslationUnit;
    }
};
```

### Where Declarations Are Added to C_TU

In **CppToCVisitor.cpp**, declarations are explicitly added:

```cpp
// === ENUM DECLARATIONS ===
bool VisitEnumDecl(clang::EnumDecl *ED) {
    // ... translation logic ...
    clang::EnumDecl *C_Enum = m_enumTranslator->translateEnum(ED);

    // Add to per-file C_TU
    C_TranslationUnit->addDecl(C_Enum);
    llvm::outs() << "  -> C enum added to C_TU\n";
}

// === STRUCT DECLARATIONS ===
bool VisitCXXRecordDecl(clang::CXXRecordDecl *D) {
    // ... create struct from class ...
    clang::RecordDecl *CStruct = /* created by Builder */;

    // Track as already added
    cppToCMap[D] = CStruct;

    // Add to per-file C_TU
    C_TranslationUnit->addDecl(CStruct);
    llvm::outs() << "    -> Created struct and added to C_TU\n";
}

// === FUNCTION DECLARATIONS ===
bool VisitFunctionDecl(clang::FunctionDecl *FD) {
    // ... create C function ...
    clang::FunctionDecl *CFunc = /* created */;

    // Add to per-file C_TU
    C_TranslationUnit->addDecl(CFunc);
    llvm::outs() << "    -> Created function and added to C_TU\n";
}

// === CONSTRUCTOR DECLARATIONS ===
bool VisitCXXConstructorDecl(clang::CXXConstructorDecl *CD) {
    // ... create constructor function ...
    clang::FunctionDecl *CFunc = /* created */;

    // Add to per-file C_TU
    C_TranslationUnit->addDecl(CFunc);

    // ALSO add to shared TargetContext map for cross-file references
    targetCtx.getCtorMap()[MangledName] = CFunc;
}

// === DESTRUCTOR DECLARATIONS ===
bool VisitCXXDestructorDecl(clang::CXXDestructorDecl *DD) {
    // ... create destructor function ...
    clang::FunctionDecl *CFunc = /* created */;

    // Add to per-file C_TU
    C_TranslationUnit->addDecl(CFunc);

    // ALSO add to shared TargetContext map for cross-file references
    targetCtx.getDtorMap()[MangledName] = CFunc;
}
```

**Flow for Each Declaration**:
1. Create C AST node (using Builder with shared context)
2. **Add to per-file C_TU**: `C_TranslationUnit->addDecl(Node)`
3. If cross-file reference needed, also add to shared map

---

## 3. CNodeBuilder - Node Creation

**Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/CNodeBuilder.h`

CNodeBuilder creates nodes in the **shared target ASTContext**, but traditionally also added to shared TU:

```cpp
class CNodeBuilder {
private:
    ASTContext &Ctx;  // The SHARED target context!

public:
    // === STRUCT CREATION ===
    RecordDecl *structDecl(llvm::StringRef name,
                          llvm::ArrayRef<FieldDecl *> fields) {
        // Create struct in shared context
        RecordDecl *RD = RecordDecl::Create(Ctx, ...);
        RD->startDefinition();

        // Add fields
        for (FieldDecl *FD : fields) {
            FD->setDeclContext(RD);
            RD->addDecl(FD);  // <-- Fields added to struct
        }
        RD->completeDefinition();

        // OLD BUG: Add to shared TU
        Ctx.getTranslationUnitDecl()->addDecl(RD);  // <-- WRONG!

        return RD;
    }

    // === ENUM CREATION ===
    EnumDecl *enumDecl(llvm::StringRef name,
                      llvm::ArrayRef<std::pair<llvm::StringRef, int>> enumerators) {
        EnumDecl *ED = EnumDecl::Create(Ctx, ...);
        ED->startDefinition();

        // Add enumerators
        for (const auto &[enumName, enumValue] : enumerators) {
            EnumConstantDecl *ECD = EnumConstantDecl::Create(...);
            ED->addDecl(ECD);  // <-- Enumerators added to enum
        }
        ED->completeDefinition(...);

        // OLD BUG: Add to shared TU
        Ctx.getTranslationUnitDecl()->addDecl(ED);  // <-- WRONG!

        return ED;
    }

    // === FUNCTION CREATION ===
    FunctionDecl *funcDecl(QualType retType,
                          llvm::StringRef name,
                          llvm::ArrayRef<ParmVarDecl *> params,
                          clang::Stmt *body = nullptr,
                          clang::CallingConv callConv = clang::CC_C,
                          bool isVariadic = false) {
        // ... create function type and FunctionDecl ...
        FunctionDecl *FD = FunctionDecl::Create(Ctx, ...);
        FD->setParams(params);
        if (body) FD->setBody(body);

        // OLD BUG: Add to shared TU
        Ctx.getTranslationUnitDecl()->addDecl(FD);  // <-- WRONG!

        return FD;
    }
};
```

**Critical Issue**: CNodeBuilder adds nodes to `Ctx.getTranslationUnitDecl()` which is the **shared TU**, not the per-file C_TU!

**The Fix (in CppToCVisitor)**:
```cpp
// Create node via Builder (goes to shared TU by default)
RecordDecl *CStruct = /* created via Builder.structDecl() */;

// ALSO add to per-file C_TU for proper output
C_TranslationUnit->addDecl(CStruct);  // <-- CRITICAL!
```

---

## 4. TargetContext Implementation

**Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/TargetContext.cpp`

```cpp
TargetContext::TargetContext() {
    llvm::outs() << "[Bug #30 FIX] Creating independent target ASTContext...\n";

    // 1. Create independent infrastructure (FileManager, SourceManager, etc.)
    clang::FileSystemOptions FileSystemOpts;
    FileMgr = std::make_unique<clang::FileManager>(FileSystemOpts);

    // 2. Create DiagnosticsEngine
    Diagnostics = std::make_unique<clang::DiagnosticsEngine>(DiagID, ...);

    // 3. Create SourceManager
    SourceMgr = std::make_unique<clang::SourceManager>(*Diagnostics, *FileMgr);

    // 4. Create TargetInfo
    std::string TargetTriple = llvm::sys::getDefaultTargetTriple();
    Target.reset(clang::TargetInfo::CreateTargetInfo(*Diagnostics, *TargetOpts));

    // 5. Create LangOptions for C11
    clang::LangOptions LangOpts;
    LangOpts.C11 = 1;
    Idents = std::make_unique<clang::IdentifierTable>(LangOpts);

    // 6. Create Builtin::Context and initialize with Target
    Builtins = std::make_unique<clang::Builtin::Context>();
    Builtins->InitializeTarget(*Target, nullptr);

    // 7. CREATE THE SHARED TARGET ASTCONTEXT
    Context = std::make_unique<clang::ASTContext>(
        LangOpts,
        *SourceMgr,
        *Idents,
        *Selectors,
        *Builtins,
        clang::TranslationUnitKind::TU_Complete
    );

    // 8. Initialize builtin types
    Context->InitBuiltinTypes(*Target, nullptr);

    llvm::outs() << "[Bug #30 FIX] Target ASTContext created @ "
                 << (void*)Context.get() << "\n";
}

TargetContext& TargetContext::getInstance() {
    if (!instance) {
        instance = new TargetContext();
    }
    return *instance;
}

clang::TranslationUnitDecl* TargetContext::createTranslationUnit() {
    // Create ONE C_TU in the shared context
    return clang::TranslationUnitDecl::Create(*Context);
}
```

**Key Points**:
1. Singleton pattern ensures ONE instance
2. Creates independent ASTContext infrastructure
3. All C nodes created in this shared context
4. Each call to `createTranslationUnit()` creates a new per-file TU

---

## Data Structures for C_TU Management

### 1. Per-File Storage (CppToCVisitor)

```cpp
class CppToCVisitor {
    // This file's C TranslationUnit
    clang::TranslationUnitDecl* C_TranslationUnit;  // Line 117

    // Maps for THIS file
    std::map<clang::CXXRecordDecl *, clang::RecordDecl *> cppToCMap;
    std::map<std::string, clang::FunctionDecl *> standaloneFuncMap;
    std::set<clang::FunctionDecl *> generatedFunctions;
};
```

### 2. Shared Storage (TargetContext)

```cpp
class TargetContext {
    // Shared across ALL files
    std::unique_ptr<clang::ASTContext> Context;  // ONE for all files

    std::map<std::string, clang::FunctionDecl *> ctorMap;      // Mangled name -> C ctor
    std::map<std::string, clang::FunctionDecl *> methodMap;    // Mangled name -> C method
    std::map<std::string, clang::FunctionDecl *> dtorMap;      // Mangled name -> C dtor
};
```

### 3. Relationships

```
C++ Source File 1 (Context1) → CppToCVisitor1 → C_TU1 (in shared context)
C++ Source File 2 (Context2) → CppToCVisitor2 → C_TU2 (in shared context)
C++ Source File 3 (Context3) → CppToCVisitor3 → C_TU3 (in shared context)

All C_TU1, C_TU2, C_TU3 share the same ASTContext (targetCtx.getContext())
All nodes added to their respective C_TU for per-file output
Cross-file references via TargetContext maps (ctorMap, methodMap, dtorMap)
```

---

## How to Create Multiple C_TUs for One .cpp Compilation

**Current Design**: ONE C_TU per source file

To create **multiple C_TUs for one .cpp**, you would:

### Option 1: Create Multiple C_TUs in Same Handler

```cpp
void CppToCConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    TargetContext& targetCtx = TargetContext::getInstance();
    clang::CNodeBuilder Builder(targetCtx.getContext());

    // === CREATE MULTIPLE C_TUs ===
    clang::TranslationUnitDecl* C_TU_Header = targetCtx.createTranslationUnit();
    clang::TranslationUnitDecl* C_TU_Impl = targetCtx.createTranslationUnit();
    clang::TranslationUnitDecl* C_TU_Tests = targetCtx.createTranslationUnit();

    // === SEPARATE DECLARATIONS AND DEFINITIONS ===
    // Create visitor for each TU with different filter logic
    CppToCVisitor VisitorHeader(Context, Builder, targetCtx, tracker, C_TU_Header);
    // Filter: declarations only
    // Traverse AST...

    CppToCVisitor VisitorImpl(Context, Builder, targetCtx, tracker, C_TU_Impl);
    // Filter: definitions only
    // Traverse AST...

    // === GENERATE THREE FILES ===
    // Generate from C_TU_Header → MyClass.h
    // Generate from C_TU_Impl → MyClass.c
    // Generate from C_TU_Tests → MyClass_test.c
}
```

### Option 2: Add Filtering Logic to CppToCVisitor

```cpp
class CppToCVisitor {
    enum OutputTarget {
        Header,      // Declarations only
        Implementation,  // Definitions only
        Tests        // Test code
    };

    OutputTarget currentTarget;

    bool VisitFunctionDecl(clang::FunctionDecl *FD) {
        // ... create C function ...
        clang::FunctionDecl *CFunc = /* ... */;

        // Add to appropriate C_TU based on output target
        if (currentTarget == Header) {
            C_TU_Header->addDecl(CFunc);
        } else if (currentTarget == Implementation) {
            C_TU_Impl->addDecl(CFunc);
        }
    }
};
```

### Option 3: Create Wrapper C_TU Manager

```cpp
class TranslationUnitManager {
    TargetContext& targetCtx;
    std::map<std::string, clang::TranslationUnitDecl*> tuMap;  // name -> C_TU

public:
    clang::TranslationUnitDecl* getOrCreateTU(const std::string& name) {
        if (!tuMap.count(name)) {
            tuMap[name] = targetCtx.createTranslationUnit();
        }
        return tuMap[name];
    }

    void addDeclToTU(const std::string& tuName, clang::Decl* D) {
        auto* tu = getOrCreateTU(tuName);
        tu->addDecl(D);
    }
};

// Usage:
TranslationUnitManager tuMgr(targetCtx);
tuMgr.addDeclToTU("header", struct_decl);
tuMgr.addDeclToTU("impl", function_def);
```

---

## Summary: C_TU Creation Points

| Component | Location | Responsibility |
|-----------|----------|-----------------|
| **TargetContext** | `TargetContext::createTranslationUnit()` | Creates one C_TU per file |
| **CppToCConsumer** | `HandleTranslationUnit()` | Calls `createTranslationUnit()` |
| **CppToCVisitor** | Constructor | Receives C_TU and stores it |
| **CNodeBuilder** | Methods like `structDecl()`, `funcDecl()` | Creates nodes in shared context |
| **CppToCVisitor (methods)** | `Visit*()` methods | Adds nodes to C_TU via `addDecl()` |

---

## Key Design Patterns

### 1. Singleton for Shared Context
```cpp
TargetContext& ctx = TargetContext::getInstance();  // Always returns same instance
```

### 2. Per-File TU Creation
```cpp
clang::TranslationUnitDecl* C_TU = targetCtx.createTranslationUnit();  // New TU per file
```

### 3. Cross-File Reference via Maps
```cpp
// In one file:
targetCtx.getCtorMap()[mangledName] = ctorFunc;

// In another file:
auto it = targetCtx.getCtorMap().find(mangledName);
if (it != targetCtx.getCtorMap().end()) {
    clang::FunctionDecl* ctorFunc = it->second;  // Get ctor from other file
}
```

### 4. Explicit Addition to C_TU
```cpp
// CNodeBuilder creates in shared context
RecordDecl* struct = Builder.structDecl(...);

// CppToCVisitor explicitly adds to per-file C_TU
C_TranslationUnit->addDecl(struct);
```

---

## Important Notes

1. **TranslationUnitDecl::Create** - Creates empty C_TU in given context
2. **addDecl()** - Adds declaration to TranslationUnit (order matters for output)
3. **decls()** - Returns range of declarations in TU
4. **Context vs. TranslationUnit**:
   - Context: Owns the memory, manages types
   - TranslationUnit: Organizes declarations for iteration/output

5. **Shared vs. Per-File**:
   - Shared ASTContext: All C nodes
   - Per-File C_TU: Declarations to output for that file
   - Shared Maps: Cross-file references (constructors, methods, destructors)

---

## Testing

See `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/TranslationIntegrationTest.cpp` for examples of how C_TUs are tested:

```cpp
// Test multi-file transpilation
// Verify each file gets its own C_TU
// Verify cross-file references work via TargetContext maps
```

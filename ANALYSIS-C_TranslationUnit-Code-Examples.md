# C TranslationUnit - Code Examples and Patterns

## 1. Creating C_TU in CppToCConsumer

**File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCConsumer.cpp`

### Example 1.1: Basic C_TU Creation

```cpp
void CppToCConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    // STEP 1: Get shared target context
    TargetContext& targetCtx = TargetContext::getInstance();

    // STEP 2: Create builder with shared context
    clang::CNodeBuilder Builder(targetCtx.getContext());

    // STEP 3: Create per-file C_TranslationUnit
    clang::TranslationUnitDecl* C_TU = targetCtx.createTranslationUnit();
    llvm::outs() << "[Bug #30 FIX] Created C_TU @ " << (void*)C_TU
                 << " for file: " << InputFilename << "\n";

    // STEP 4: Create visitor with this C_TU
    CppToCVisitor Visitor(Context, Builder, targetCtx, fileOriginTracker,
                          C_TU, InputFilename);

    // STEP 5: Traverse AST
    auto *TU = Context.getTranslationUnitDecl();
    Visitor.TraverseDecl(TU);

    // STEP 6: Process templates
    Visitor.processTemplateInstantiations(TU);

    // Validate
    auto CTU_DeclCount = std::distance(C_TU->decls().begin(),
                                      C_TU->decls().end());
    llvm::outs() << "C TranslationUnit has " << CTU_DeclCount
                 << " generated declarations\n";
}
```

### Example 1.2: Multiple C_TUs (Extended Design)

```cpp
// If you wanted to create multiple C_TUs from one source file:
class MultiModuleConsumer : public ASTConsumer {
private:
    TargetContext& targetCtx;
    std::map<std::string, clang::TranslationUnitDecl*> moduleMap;

public:
    void HandleTranslationUnit(clang::ASTContext &Context) override {
        // Create separate C_TU for each module
        clang::TranslationUnitDecl* C_TU_Interfaces =
            targetCtx.createTranslationUnit();
        clang::TranslationUnitDecl* C_TU_Implementations =
            targetCtx.createTranslationUnit();
        clang::TranslationUnitDecl* C_TU_Tests =
            targetCtx.createTranslationUnit();

        moduleMap["interfaces"] = C_TU_Interfaces;
        moduleMap["implementations"] = C_TU_Implementations;
        moduleMap["tests"] = C_TU_Tests;

        // Create builder
        clang::CNodeBuilder Builder(targetCtx.getContext());

        // Create visitor for each module
        // ... filter logic to route declarations to appropriate C_TU
    }
};
```

---

## 2. Adding Declarations to C_TU in CppToCVisitor

**File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCVisitor.cpp`

### Example 2.1: Adding Enum

```cpp
bool CppToCVisitor::VisitEnumDecl(clang::EnumDecl *ED) {
    // Skip system headers
    if (!fileOriginFilter->matches(ED)) {
        return true;
    }

    llvm::outs() << "Processing enum: " << ED->getName() << "\n";

    // Translate C++ enum to C enum
    clang::EnumDecl *C_Enum = m_enumTranslator->translateEnum(ED);

    if (C_Enum) {
        // BUG #2 FIX: Add enum to per-file C_TranslationUnit
        // EnumTranslator adds to shared TU, but we need it in per-file C_TU
        C_TranslationUnit->addDecl(C_Enum);

        llvm::outs() << "  -> C enum " << ED->getNameAsString()
                     << " created and added to C_TU\n";
    }

    return true;
}
```

### Example 2.2: Adding Struct from Class

```cpp
bool CppToCVisitor::VisitCXXRecordDecl(clang::CXXRecordDecl *D) {
    // Skip system headers, implicit decls, forward declarations
    if (!fileOriginFilter->matches(D)) return true;
    if (D->isImplicit()) return true;
    if (!D->isCompleteDefinition()) return true;

    llvm::outs() << "Processing class/struct: " << D->getName() << "\n";

    // Check if already processed
    if (cppToCMap.count(D)) {
        llvm::outs() << "  -> class " << D->getName()
                     << " already processed (in cppToCMap)\n";
        return true;
    }

    // CREATE STRUCT
    // Collect fields
    std::vector<clang::FieldDecl *> fields;
    for (auto *Field : D->fields()) {
        clang::QualType fieldTy = translateTypeToCContext(Field->getType());
        auto *C_Field = Builder.fieldDecl(fieldTy, Field->getName());
        fields.push_back(C_Field);
    }

    // Create struct via Builder
    clang::RecordDecl *CStruct =
        Builder.structDecl(D->getName(), fields);

    // BUG #3 FIX: Also add to per-file C_TranslationUnit
    // Builder.structDecl() adds to shared TU, but we need per-file C_TU
    C_TranslationUnit->addDecl(CStruct);
    llvm::outs() << "    -> Created struct: " << CStruct->getNameAsString()
                 << " and added to C_TU\n";

    // Track mapping
    cppToCMap[D] = CStruct;

    // CREATE METHODS
    std::vector<clang::FunctionDecl *> methods;
    for (auto *Method : D->methods()) {
        if (Method->isImplicit()) continue;

        clang::FunctionDecl *C_Method = /* create via Builder */;
        methods.push_back(C_Method);

        // Add method to per-file C_TU
        C_TranslationUnit->addDecl(C_Method);
    }

    return true;
}
```

### Example 2.3: Adding Constructor Function

```cpp
bool CppToCVisitor::VisitCXXConstructorDecl(clang::CXXConstructorDecl *CD) {
    // Get the class
    auto *ClassDecl = CD->getParent();
    auto MangledName = Mangler.getMangledName(CD);

    llvm::outs() << "Processing constructor: " << MangledName << "\n";

    // Create C function for constructor
    std::vector<clang::ParmVarDecl *> params;

    // Add 'this' parameter
    clang::QualType ClassType = /* get from cppToCMap */;
    clang::QualType ThisType = Builder.ptrType(ClassType);
    auto *ThisParam = Builder.param(ThisType, "this");
    params.push_back(ThisParam);

    // Add constructor parameters
    for (auto *Param : CD->parameters()) {
        // ... translate parameter type ...
        auto *C_Param = Builder.param(paramTy, Param->getName());
        params.push_back(C_Param);
    }

    // Create function body
    clang::Stmt *Body = /* translate constructor body */;

    // Create C function
    clang::FunctionDecl *CFunc = Builder.funcDecl(
        Builder.voidType(),  // Constructors return void
        MangledName,
        params,
        Body
    );

    // BUG #4 FIX: Also add to per-file C_TU
    C_TranslationUnit->addDecl(CFunc);
    llvm::outs() << "    -> Created constructor and added to C_TU\n";

    // BUG #5 FIX: Store in shared map for cross-file references
    targetCtx.getCtorMap()[MangledName] = CFunc;

    return true;
}
```

### Example 2.4: Adding Method Function

```cpp
bool CppToCVisitor::VisitCXXMethodDecl(clang::CXXMethodDecl *MD) {
    // Skip special methods handled elsewhere
    if (dyn_cast<clang::CXXConstructorDecl>(MD)) return true;
    if (dyn_cast<clang::CXXDestructorDecl>(MD)) return true;
    if (dyn_cast<clang::CXXConversionDecl>(MD)) return true;

    auto MangledName = Mangler.getMangledName(MD);
    llvm::outs() << "Processing method: " << MangledName << "\n";

    // Create C function for method
    std::vector<clang::ParmVarDecl *> params;

    // Add 'this' parameter
    auto *ClassDecl = MD->getParent();
    auto It = cppToCMap.find(ClassDecl);
    if (It == cppToCMap.end()) {
        llvm::errs() << "Error: Class not yet translated: "
                     << ClassDecl->getName() << "\n";
        return true;
    }
    clang::RecordDecl *CStruct = It->second;
    clang::QualType ThisType = Builder.ptrType(Builder.getContext().getRecordType(CStruct));
    auto *ThisParam = Builder.param(ThisType, "this");
    params.push_back(ThisParam);

    // Add method parameters
    for (auto *Param : MD->parameters()) {
        clang::QualType paramTy = translateTypeToCContext(Param->getType());
        auto *C_Param = Builder.param(paramTy, Param->getName());
        params.push_back(C_Param);
    }

    // Translate return type
    clang::QualType retTy = translateTypeToCContext(MD->getReturnType());

    // Create function body
    clang::Stmt *Body = /* translate method body */;

    // Create C function
    clang::FunctionDecl *CFunc = Builder.funcDecl(
        retTy,
        MangledName,
        params,
        Body
    );

    // Add to per-file C_TU
    C_TranslationUnit->addDecl(CFunc);
    llvm::outs() << "    -> Created method and added to C_TU\n";

    // Store in shared map for cross-file references
    targetCtx.getMethodMap()[MangledName] = CFunc;

    return true;
}
```

### Example 2.5: Adding Standalone Function

```cpp
bool CppToCVisitor::VisitFunctionDecl(clang::FunctionDecl *FD) {
    // Skip methods, built-ins, implicit decls
    if (dyn_cast<clang::CXXMethodDecl>(FD)) return true;
    if (FD->isBuiltin()) return true;
    if (FD->isImplicit()) return true;
    if (!FD->hasBody()) return true;

    auto MangledName = Mangler.getMangledName(FD);
    llvm::outs() << "Processing function: " << FD->getName() << "\n";

    // Check if already generated
    if (generatedFunctions.count(FD)) {
        return true;
    }
    generatedFunctions.insert(FD);

    // Create C function
    std::vector<clang::ParmVarDecl *> params;
    for (auto *Param : FD->parameters()) {
        clang::QualType paramTy = translateTypeToCContext(Param->getType());
        auto *C_Param = Builder.param(paramTy, Param->getName());
        params.push_back(C_Param);
    }

    clang::QualType retTy = translateTypeToCContext(FD->getReturnType());
    clang::Stmt *Body = translateStmt(FD->getBody());

    clang::FunctionDecl *CFunc = Builder.funcDecl(
        retTy,
        MangledName,
        params,
        Body
    );

    // BUG #6 FIX: Add to per-file C_TU
    C_TranslationUnit->addDecl(CFunc);
    llvm::outs() << "    -> Created function and added to C_TU\n";

    // Track in per-file map
    standaloneFuncMap[MangledName] = CFunc;

    return true;
}
```

---

## 3. Iterating C_TU for Code Generation

**File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCConsumer.cpp`

### Example 3.1: Generate Header from C_TU

```cpp
// Generate header file (.h) - declarations only
std::string headerContent;
llvm::raw_string_ostream headerOS(headerContent);

CodeGenerator headerGen(headerOS, Context, InputFilename);

// Write standard headers and includes
headerOS << "// Generated from: " << InputFilename << "\n";
headerOS << "#pragma once\n\n";
headerOS << "#include <stdio.h>\n";
headerOS << "#include <stdlib.h>\n";
headerOS << "#include <string.h>\n";
headerOS << "#include <stdint.h>\n";
headerOS << "#include <stdbool.h>\n\n";

// Write user header includes
auto userHeaders = fileOriginTracker.getUserHeaderFiles();
for (const auto& headerPath : userHeaders) {
    if (headerPath == InputFilename) continue;  // Skip self-includes

    // ... calculate relative path ...

    headerOS << "#include \"" << includePath << "\"\n";
}
headerOS << "\n";

// CRITICAL: Iterate C_TU->decls(), not original C++ TU
for (auto *D : C_TU->decls()) {
    if (!D->isImplicit()) {
        headerGen.printDecl(D, true);  // true = declaration only
    }
}

headerOS.flush();
```

### Example 3.2: Generate Implementation from C_TU

```cpp
// Generate implementation file (.c) - full definitions
std::string implContent;
llvm::raw_string_ostream implOS(implContent);

CodeGenerator implGen(implOS, Context, InputFilename);

// Write comment and header
implOS << "// Generated from: " << InputFilename << "\n";
implOS << "// Implementation file\n\n";

// Include corresponding header
size_t lastSlash = InputFilename.find_last_of("/\\");
std::string baseName;
if (lastSlash != std::string::npos) {
    baseName = InputFilename.substr(lastSlash + 1);
} else {
    baseName = InputFilename;
}
size_t dotPos = baseName.find_last_of('.');
if (dotPos != std::string::npos) {
    baseName = baseName.substr(0, dotPos);
}
implOS << "#include \"" << baseName << ".h\"\n\n";

// CRITICAL: Iterate C_TU->decls(), not original C++ TU
for (auto *D : C_TU->decls()) {
    if (!D->isImplicit()) {
        implGen.printDecl(D, false);  // false = full definition
    }
}

implOS.flush();
```

### Example 3.3: Count Declarations in C_TU

```cpp
// Validate C_TU
auto CTU_DeclCount = std::distance(C_TU->decls().begin(),
                                   C_TU->decls().end());
llvm::outs() << "C TranslationUnit has " << CTU_DeclCount
             << " generated declarations\n";

if (CTU_DeclCount == 0) {
    llvm::errs() << "Warning: No C AST nodes generated. "
                 << "Input may contain unsupported C++ features.\n";
}

// Print declaration types
for (auto *D : C_TU->decls()) {
    if (auto *RD = dyn_cast<clang::RecordDecl>(D)) {
        llvm::outs() << "  - struct " << RD->getName() << "\n";
    } else if (auto *FD = dyn_cast<clang::FunctionDecl>(D)) {
        llvm::outs() << "  - function " << FD->getName() << "\n";
    } else if (auto *ED = dyn_cast<clang::EnumDecl>(D)) {
        llvm::outs() << "  - enum " << ED->getName() << "\n";
    }
}
```

---

## 4. Cross-File Reference Patterns

### Example 4.1: Store Constructor for Cross-File Use

```cpp
// In File 1 (Vector3D.cpp)
bool CppToCVisitor::VisitCXXConstructorDecl(clang::CXXConstructorDecl *CD) {
    // ... create C function CFunc ...

    // Add to per-file C_TU for File 1's output
    C_TranslationUnit->addDecl(CFunc);

    // ALSO store in shared map for File 2 to access
    std::string MangledName = Mangler.getMangledName(CD);
    targetCtx.getCtorMap()[MangledName] = CFunc;

    llvm::outs() << "Stored constructor in TargetContext: "
                 << MangledName << "\n";
}
```

### Example 4.2: Lookup Constructor for Cross-File Use

```cpp
// In File 2 (main.cpp)
clang::Expr *CppToCVisitor::translateConstructExpr(
    clang::CXXConstructExpr *CCE) {

    // Get the constructor being called
    auto *Constructor = CCE->getConstructor();
    std::string MangledName = Mangler.getMangledName(Constructor);

    // Look up the C function from ANY file
    auto& CtorMap = targetCtx.getCtorMap();
    auto It = CtorMap.find(MangledName);

    if (It != CtorMap.end()) {
        // Found constructor from another file
        clang::FunctionDecl *CFuncDecl = It->second;

        // Create call to that function
        std::vector<clang::Expr *> args;
        // ... add 'this' pointer ...
        // ... add constructor arguments ...

        clang::CallExpr *CallE = new (Ctx) clang::CallExpr(
            Ctx,
            new (Ctx) clang::DeclRefExpr(
                Ctx, CFuncDecl, false, CFuncDecl->getType(),
                clang::VK_LValue, clang::SourceLocation()),
            args,
            CFuncDecl->getReturnType(),
            clang::VK_PRValue,
            clang::SourceLocation()
        );

        return CallE;
    } else {
        llvm::errs() << "Error: Constructor not found: "
                     << MangledName << "\n";
        return nullptr;
    }
}
```

### Example 4.3: Lookup Method from Another File

```cpp
// Translate method call in any file
clang::Expr *CppToCVisitor::translateCallExpr(clang::CallExpr *CE) {
    auto *Callee = CE->getCalleeDecl();

    if (auto *MD = dyn_cast<clang::CXXMethodDecl>(Callee)) {
        // This is a method call
        std::string MangledName = Mangler.getMangledName(MD);

        // Look up the C function (might be from different file)
        auto& MethodMap = targetCtx.getMethodMap();
        auto It = MethodMap.find(MangledName);

        if (It != MethodMap.end()) {
            clang::FunctionDecl *CFuncDecl = It->second;

            // Build call with explicit 'this'
            std::vector<clang::Expr *> args;

            // Add 'this' from member expression
            auto *ThisExpr = /* extract from CE */;
            args.push_back(ThisExpr);

            // Add other arguments
            for (unsigned i = 0; i < CE->getNumArgs(); ++i) {
                args.push_back(translateExpr(CE->getArg(i)));
            }

            // Create call
            clang::CallExpr *CallE = new (Ctx) clang::CallExpr(
                Ctx,
                new (Ctx) clang::DeclRefExpr(
                    Ctx, CFuncDecl, false, CFuncDecl->getType(),
                    clang::VK_LValue, clang::SourceLocation()),
                args,
                CFuncDecl->getReturnType(),
                clang::VK_PRValue,
                clang::SourceLocation()
            );

            return CallE;
        }
    }

    return nullptr;
}
```

---

## 5. TargetContext Usage Patterns

### Example 5.1: Initialize TargetContext

```cpp
// Called once at start of transpilation
TargetContext& targetCtx = TargetContext::getInstance();

llvm::outs() << "TargetContext initialized:\n"
             << "  ASTContext @ " << (void*)&targetCtx.getContext() << "\n"
             << "  Target: " << llvm::sys::getDefaultTargetTriple() << "\n";
```

### Example 5.2: Create and Use Multiple C_TUs

```cpp
// File 1: Create C_TU1
clang::TranslationUnitDecl* C_TU1 = targetCtx.createTranslationUnit();
llvm::outs() << "Created C_TU1 @ " << (void*)C_TU1 << "\n";

// Process File 1, add declarations to C_TU1
// ...

// File 2: Create C_TU2 (in same shared context)
clang::TranslationUnitDecl* C_TU2 = targetCtx.createTranslationUnit();
llvm::outs() << "Created C_TU2 @ " << (void*)C_TU2 << "\n";

// Process File 2, add declarations to C_TU2
// ...

// File 3: Create C_TU3 (still in same shared context)
clang::TranslationUnitDecl* C_TU3 = targetCtx.createTranslationUnit();
llvm::outs() << "Created C_TU3 @ " << (void*)C_TU3 << "\n";

// Process File 3, add declarations to C_TU3
// ...

// All C_TU1, C_TU2, C_TU3 declarations are in same ASTContext
// This ensures type compatibility across files
```

### Example 5.3: Cleanup at Program Exit

```cpp
// In main.cpp or destructor
// Register cleanup to be called at exit
std::atexit([] {
    TargetContext::cleanup();
});

// Or explicitly:
// TargetContext::cleanup();
```

---

## 6. Common Patterns and Anti-Patterns

### Pattern: Correct Way to Add Declaration to C_TU

```cpp
// CORRECT: Add to per-file C_TU
bool VisitSomething(clang::SomeDecl *D) {
    // Create C node
    clang::SomeDecl *C_Node = /* create via Builder */;

    // ALWAYS add to per-file C_TU
    C_TranslationUnit->addDecl(C_Node);

    // If cross-file reference needed, ALSO add to map
    if (isPublic(D)) {
        targetCtx.getMethodMap()[mangledName] = C_Node;
    }

    return true;
}
```

### Anti-Pattern: Forgetting to Add to Per-File C_TU

```cpp
// WRONG: Only in shared TU (via Builder)
bool VisitSomething(clang::SomeDecl *D) {
    // Create C node
    clang::SomeDecl *C_Node = Builder.structDecl(...);
    // Builder adds to shared TU

    // FORGOT to add to per-file C_TU!
    // Result: Declaration doesn't get emitted to this file's .c/.h

    return true;
}
```

### Pattern: Type Translation Across Contexts

```cpp
// CORRECT: Translate types between C++ context and shared C context
clang::QualType CppToCVisitor::translateTypeToCContext(
    clang::QualType CppType) {

    // CppType is from Context (C++ ASTContext)
    // Need to convert to shared target context types

    if (CppType->isBuiltinType()) {
        // Map builtin types
        if (CppType == Context.IntTy) {
            return targetCtx.getContext().IntTy;  // From shared context
        }
        // ... etc ...
    }

    if (auto *RD = CppType->getAsCXXRecordDecl()) {
        // Look up translated struct
        auto It = cppToCMap.find(RD);
        if (It != cppToCMap.end()) {
            return targetCtx.getContext().getRecordType(It->second);
        }
    }

    // ... etc ...
}
```

---

## 7. Debugging C_TU Issues

### Check if Declaration is in C_TU

```cpp
// Debug: Check if struct is in C_TU
bool isInCTU(clang::TranslationUnitDecl* C_TU,
             clang::RecordDecl* struct_) {
    for (auto *D : C_TU->decls()) {
        if (D == struct_) {
            return true;
        }
    }
    return false;
}

// Usage
if (!isInCTU(C_TranslationUnit, CStruct)) {
    llvm::errs() << "ERROR: Struct not in C_TU!\n";
    C_TranslationUnit->addDecl(CStruct);  // Fix it
}
```

### Print C_TU Contents

```cpp
// Debug: Print what's in the C_TU
void printCTUContents(clang::TranslationUnitDecl* C_TU) {
    llvm::outs() << "C_TU Contents:\n";
    int structCount = 0, funcCount = 0, enumCount = 0;

    for (auto *D : C_TU->decls()) {
        if (auto *RD = dyn_cast<clang::RecordDecl>(D)) {
            llvm::outs() << "  [STRUCT] " << RD->getName() << "\n";
            structCount++;
        } else if (auto *FD = dyn_cast<clang::FunctionDecl>(D)) {
            llvm::outs() << "  [FUNC] " << FD->getName() << "\n";
            funcCount++;
        } else if (auto *ED = dyn_cast<clang::EnumDecl>(D)) {
            llvm::outs() << "  [ENUM] " << ED->getName() << "\n";
            enumCount++;
        } else {
            llvm::outs() << "  [OTHER] " << D->getDeclKindName() << "\n";
        }
    }

    llvm::outs() << "Summary: " << structCount << " structs, "
                 << funcCount << " functions, " << enumCount << " enums\n";
}
```

### Verify Cross-File Maps

```cpp
// Debug: Check cross-file maps
void verifyTargetContext(TargetContext& targetCtx) {
    auto& ctorMap = targetCtx.getCtorMap();
    auto& methodMap = targetCtx.getMethodMap();
    auto& dtorMap = targetCtx.getDtorMap();

    llvm::outs() << "TargetContext Maps:\n"
                 << "  Constructors: " << ctorMap.size() << "\n"
                 << "  Methods: " << methodMap.size() << "\n"
                 << "  Destructors: " << dtorMap.size() << "\n";

    for (const auto& [mangled, func] : ctorMap) {
        llvm::outs() << "    [CTOR] " << mangled << " -> "
                     << func->getName() << "\n";
    }
}
```

---

## Summary

Key takeaways for working with C TranslationUnits:

1. **Always create one C_TU per file**: `targetCtx.createTranslationUnit()`
2. **Always add to per-file C_TU**: `C_TranslationUnit->addDecl(node)`
3. **Use shared context for nodes**: `Builder.structDecl()` uses shared context
4. **Use shared maps for cross-file refs**: `targetCtx.getCtorMap()[name] = func`
5. **Iterate per-file C_TU for output**: `for (auto *D : C_TU->decls())`
6. **Translate types across contexts**: Use `translateTypeToCContext()`
7. **Verify cleanup**: Call `TargetContext::cleanup()` at exit

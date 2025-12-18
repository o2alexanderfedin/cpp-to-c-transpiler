# Module Documentation

**C++ to C Transpiler - Module Reference**

This document describes each module in the transpiler, its responsibilities, dependencies, and key APIs.

## Module Categories

1. [Core Infrastructure](#core-infrastructure)
2. [Translation Layer](#translation-layer)
3. [Feature Translators](#feature-translators)
4. [Analysis Modules](#analysis-modules)
5. [Code Generation](#code-generation)
6. [Runtime Library](#runtime-library)

---

## Core Infrastructure

### CppToCFrontendAction

**Location**: `include/CppToCFrontendAction.h`, `src/CppToCFrontendAction.cpp`

**Purpose**: Clang FrontendAction implementation for AST processing.

**Responsibilities**:
- Configure Clang compiler instance
- Create AST consumer
- Manage compilation lifecycle

**Key APIs**:
```cpp
class CppToCFrontendAction : public ASTFrontendAction {
protected:
    std::unique_ptr<ASTConsumer> CreateASTConsumer(
        CompilerInstance &CI,
        StringRef InFile) override;
};
```

**Dependencies**: Clang LibTooling

---

### CppToCConsumer

**Location**: `include/CppToCConsumer.h`, `src/CppToCConsumer.cpp`

**Purpose**: AST consumer that processes translation units.

**Responsibilities**:
- Receive complete AST from Clang
- Initialize visitors
- Coordinate translation
- Generate output files

**Key APIs**:
```cpp
class CppToCConsumer : public ASTConsumer {
public:
    void HandleTranslationUnit(ASTContext &Context) override;
private:
    CppToCVisitor visitor;
    FileOutputManager outputManager;
};
```

**Dependencies**: CppToCVisitor, FileOutputManager

---

### CNodeBuilder

**Location**: `include/CNodeBuilder.h` (header-only or minimal implementation)

**Purpose**: Simplify Clang C node creation with clean API.

**Responsibilities**:
- Encapsulate verbose Clang node creation
- Provide type-safe helpers
- Reduce boilerplate code

**Key APIs**:
```cpp
class CNodeBuilder {
    ASTContext &Ctx;
public:
    // Variable declarations
    VarDecl* intVar(StringRef name, int initVal);
    VarDecl* structVar(QualType type, StringRef name);

    // Expressions
    CallExpr* call(StringRef func, ArrayRef<Expr*> args);
    DeclRefExpr* ref(VarDecl *var);
    UnaryOperator* addrOf(Expr *expr);

    // Statements
    IfStmt* ifStmt(Expr *cond, Stmt *then, Stmt *els = nullptr);
    CompoundStmt* block(ArrayRef<Stmt*> stmts);
    ReturnStmt* returnStmt(Expr *expr = nullptr);
};
```

**Estimated Size**: 500-800 LOC

**Dependencies**: Clang AST

---

## Translation Layer

### CppToCVisitor

**Location**: `include/CppToCVisitor.h`, `src/CppToCVisitor.cpp`

**Purpose**: Main AST visitor for C++ to C translation.

**Responsibilities**:
- Traverse C++ AST
- Dispatch to feature translators
- Build C AST
- Coordinate transformation

**Key APIs**:
```cpp
class CppToCVisitor : public RecursiveASTVisitor<CppToCVisitor> {
public:
    // Class handling
    bool VisitCXXRecordDecl(CXXRecordDecl *D);
    bool VisitCXXMethodDecl(CXXMethodDecl *D);
    bool VisitCXXConstructorDecl(CXXConstructorDecl *D);
    bool VisitCXXDestructorDecl(CXXDestructorDecl *D);

    // Exception handling
    bool VisitCXXThrowExpr(CXXThrowExpr *E);
    bool VisitCXXTryStmt(CXXTryStmt *S);
    bool VisitCXXCatchStmt(CXXCatchStmt *S);

    // RTTI
    bool VisitCXXTypeidExpr(CXXTypeidExpr *E);
    bool VisitCXXDynamicCastExpr(CXXDynamicCastExpr *E);

    // Virtual functions
    bool VisitCXXMemberCallExpr(CXXMemberCallExpr *E);

    // Templates
    bool VisitClassTemplateSpecializationDecl(
        ClassTemplateSpecializationDecl *D);
    bool VisitFunctionTemplateDecl(FunctionTemplateDecl *D);
};
```

**Dependencies**: All feature translators, CNodeBuilder

---

## Feature Translators

### Exception Handling

#### ThrowTranslator

**Location**: `src/ThrowTranslator.cpp`

**Purpose**: Translate `throw` expressions to runtime calls.

**Translation**:
```cpp
// C++: throw MyException(42);
// C: cxx_throw(&exception, &__ti_MyException);
```

**Key APIs**:
```cpp
class ThrowTranslator {
public:
    CallExpr* translateThrow(CXXThrowExpr *E);
};
```

---

#### TryCatchTransformer

**Location**: `src/TryCatchTransformer.cpp`

**Purpose**: Transform try-catch blocks into setjmp/longjmp.

**Translation**:
```cpp
// C++: try { body; } catch (E& e) { handler; }
// C: if (setjmp(frame.jmpbuf) == 0) { body; } else { handler; }
```

**Key APIs**:
```cpp
class TryCatchTransformer {
public:
    Stmt* transformTryStmt(CXXTryStmt *S);
private:
    Stmt* generateExceptionFrame();
    Stmt* generateSetjmpCheck();
    Stmt* generateCatchHandlers(ArrayRef<CXXCatchStmt*> catches);
};
```

**Dependencies**: ExceptionFrameGenerator, ActionTableGenerator

---

#### ExceptionFrameGenerator

**Location**: `src/ExceptionFrameGenerator.cpp`

**Purpose**: Generate exception frame setup/cleanup code.

**Key APIs**:
```cpp
class ExceptionFrameGenerator {
public:
    VarDecl* createFrameVariable();
    Stmt* generateFramePush(VarDecl* frame);
    Stmt* generateFramePop(VarDecl* frame);
};
```

---

#### ActionTableGenerator

**Location**: `src/ActionTableGenerator.cpp`

**Purpose**: Generate action tables for destructor unwinding.

**Key APIs**:
```cpp
class ActionTableGenerator {
public:
    VarDecl* generateActionTable(
        ArrayRef<VarDecl*> localVars,
        const CFG& controlFlow);
};
```

**Dependencies**: CFGAnalyzer

---

### RTTI

#### TypeInfoGenerator

**Location**: `src/TypeInfoGenerator.cpp`

**Purpose**: Generate type_info structures for classes.

**Generated Code**:
```c
const struct __class_type_info __ti_MyClass = {
    .vtable_ptr = &__vt_class_type_info,
    .type_name = "7MyClass"
};
```

**Key APIs**:
```cpp
class TypeInfoGenerator {
public:
    VarDecl* generateTypeInfo(CXXRecordDecl *Class);
    VarDecl* generateSITypeInfo(CXXRecordDecl *Class);  // Single inheritance
    VarDecl* generateVMITypeInfo(CXXRecordDecl *Class); // Virtual/multiple
};
```

---

#### DynamicCastTranslator

**Location**: `src/DynamicCastTranslator.cpp`

**Purpose**: Translate dynamic_cast to runtime function.

**Translation**:
```cpp
// C++: dynamic_cast<Derived*>(base)
// C: cxx_dynamic_cast(base, &__ti_Base, &__ti_Derived, offset)
```

**Key APIs**:
```cpp
class DynamicCastTranslator {
public:
    CallExpr* translateDynamicCast(CXXDynamicCastExpr *E);
private:
    ptrdiff_t computeOffset(QualType src, QualType dst);
};
```

---

#### TypeidTranslator

**Location**: `src/TypeidTranslator.cpp`

**Purpose**: Translate typeid operator to type_info reference.

**Translation**:
```cpp
// C++: typeid(MyClass)
// C: &__ti_MyClass
```

**Key APIs**:
```cpp
class TypeidTranslator {
public:
    Expr* translateTypeid(CXXTypeidExpr *E);
};
```

---

### Virtual Functions

#### VtableGenerator

**Location**: `src/VtableGenerator.cpp`

**Purpose**: Generate vtable structures and initializers.

**Generated Code**:
```c
struct MyClass_vtable {
    void (*dtor)(struct MyClass*);
    int (*method)(struct MyClass*, int);
};

const struct MyClass_vtable __vtable_MyClass = {
    .dtor = MyClass_dtor,
    .method = MyClass_method
};
```

**Key APIs**:
```cpp
class VtableGenerator {
public:
    RecordDecl* generateVtableStruct(CXXRecordDecl *Class);
    VarDecl* generateVtableInitializer(CXXRecordDecl *Class);
};
```

**Dependencies**: VirtualMethodAnalyzer, OverrideResolver

---

#### VirtualCallTranslator

**Location**: `src/VirtualCallTranslator.cpp`

**Purpose**: Translate virtual calls to vtable dispatch.

**Translation**:
```cpp
// C++: obj->method(42)
// C: obj->vptr->method(obj, 42)
```

**Key APIs**:
```cpp
class VirtualCallTranslator {
public:
    Expr* translateVirtualCall(CXXMemberCallExpr *E);
};
```

---

#### VptrInjector

**Location**: `src/VptrInjector.cpp`

**Purpose**: Inject vptr field into polymorphic classes.

**Key APIs**:
```cpp
class VptrInjector {
public:
    void injectVptr(RecordDecl *Struct, QualType vtableType);
    Stmt* generateVptrInit(VarDecl *obj, VarDecl *vtable);
};
```

---

### Virtual Inheritance

#### VTTGenerator

**Location**: `src/VTTGenerator.cpp`

**Purpose**: Generate Virtual Table Tables for construction.

**Generated Code**:
```c
const void* __vtt_Diamond[] = {
    &__vtable_Diamond_primary,
    &__vtable_Diamond_Left_base,
    &__vtable_Diamond_Right_base
};
```

**Key APIs**:
```cpp
class VTTGenerator {
public:
    VarDecl* generateVTT(CXXRecordDecl *Class);
};
```

**Dependencies**: VirtualInheritanceAnalyzer

---

#### VirtualInheritanceAnalyzer

**Location**: `src/VirtualInheritanceAnalyzer.cpp`

**Purpose**: Analyze virtual inheritance hierarchies.

**Key APIs**:
```cpp
class VirtualInheritanceAnalyzer {
public:
    bool hasVirtualBase(CXXRecordDecl *Class);
    ArrayRef<CXXBaseSpecifier> getVirtualBases(CXXRecordDecl *Class);
    size_t computeVBaseOffset(CXXRecordDecl *Derived,
                              CXXRecordDecl *VBase);
};
```

---

### Coroutines

#### CoroutineDetector

**Location**: `src/CoroutineDetector.cpp`

**Purpose**: Detect coroutines and extract suspend points.

**Key APIs**:
```cpp
class CoroutineDetector {
public:
    bool isCoroutine(FunctionDecl *F);
    ArrayRef<SuspendPoint> findSuspendPoints(FunctionDecl *F);
};
```

---

#### StateMachineTransformer

**Location**: `src/StateMachineTransformer.cpp`

**Purpose**: Transform coroutine to state machine.

**Key APIs**:
```cpp
class StateMachineTransformer {
public:
    RecordDecl* generateFrameStruct(FunctionDecl *Coro);
    FunctionDecl* generateResumeFunction(FunctionDecl *Coro);
    Stmt* generateStateSwitch(ArrayRef<SuspendPoint> points);
};
```

**Dependencies**: SuspendPointIdentifier, PromiseTranslator

---

### Templates

#### TemplateMonomorphizer

**Location**: `src/TemplateMonomorphizer.cpp`

**Purpose**: Extract template instantiations and monomorphize.

**Key APIs**:
```cpp
class TemplateMonomorphizer {
public:
    ArrayRef<Decl*> monomorphizeTemplate(ClassTemplateDecl *TD);
    ArrayRef<Decl*> monomorphizeFunctionTemplate(FunctionTemplateDecl *FTD);
};
```

---

#### TemplateExtractor

**Location**: `src/TemplateExtractor.cpp`

**Purpose**: Extract instantiated templates from AST.

**Key APIs**:
```cpp
class TemplateExtractor {
public:
    ArrayRef<ClassTemplateSpecializationDecl*> extractInstantiations();
};
```

---

## Analysis Modules

### CFGAnalyzer

**Location**: `src/CFGAnalyzer.cpp`

**Purpose**: Control flow graph analysis for RAII and exceptions.

**Key APIs**:
```cpp
class CFGAnalyzer {
public:
    const CFG& getCFG(FunctionDecl *F);
    ArrayRef<CFGBlock*> getExitBlocks(const CFG& cfg);
    bool blockReaches(CFGBlock* from, CFGBlock* to);
};
```

---

### VirtualMethodAnalyzer

**Location**: `src/VirtualMethodAnalyzer.cpp`

**Purpose**: Analyze virtual method hierarchies.

**Key APIs**:
```cpp
class VirtualMethodAnalyzer {
public:
    ArrayRef<CXXMethodDecl*> getVirtualMethods(CXXRecordDecl *Class);
    bool isOverride(CXXMethodDecl *Method);
    CXXMethodDecl* findOverriddenMethod(CXXMethodDecl *Method);
};
```

---

### DependencyAnalyzer

**Location**: `src/DependencyAnalyzer.cpp`

**Purpose**: Track dependencies for include generation.

**Key APIs**:
```cpp
class DependencyAnalyzer {
public:
    void analyzeDecl(Decl *D);
    ArrayRef<std::string> getRequiredIncludes();
    bool needsRuntimeLibrary();
};
```

---

## Code Generation

### CodeGenerator

**Location**: `src/CodeGenerator.cpp`

**Purpose**: Generate C code from C AST using Clang printer.

**Key APIs**:
```cpp
class CodeGenerator {
public:
    void generateCode(Decl *D, raw_ostream &Out);
private:
    void injectLineDirective(SourceLocation Loc, raw_ostream &Out);
    PrintingPolicy createC99Policy();
};
```

---

### FileOutputManager

**Location**: `src/FileOutputManager.cpp`

**Purpose**: Manage output file generation (.h/.c pairs).

**Key APIs**:
```cpp
class FileOutputManager {
public:
    void generateHeader(StringRef filename, ArrayRef<Decl*> decls);
    void generateImplementation(StringRef filename, ArrayRef<Decl*> decls);
};
```

**Dependencies**: HeaderSeparator, IncludeGuardGenerator

---

### HeaderSeparator

**Location**: `src/HeaderSeparator.cpp`

**Purpose**: Separate declarations for header vs implementation.

**Key APIs**:
```cpp
class HeaderSeparator {
public:
    ArrayRef<Decl*> getHeaderDecls();
    ArrayRef<Decl*> getImplDecls();
    void analyzeDecl(Decl *D);
};
```

---

### IncludeGuardGenerator

**Location**: `src/IncludeGuardGenerator.cpp`

**Purpose**: Generate standard include guards.

**Key APIs**:
```cpp
class IncludeGuardGenerator {
public:
    std::string generateGuardName(StringRef filename);
    void emitGuardBegin(raw_ostream &Out, StringRef guard);
    void emitGuardEnd(raw_ostream &Out, StringRef guard);
};
```

---

### NameMangler

**Location**: `src/NameMangler.cpp`

**Purpose**: Generate readable C names from C++ names.

**Key APIs**:
```cpp
class NameMangler {
public:
    std::string mangleName(const NamedDecl *D);
    std::string mangleType(QualType T);
};
```

---

## Runtime Library

### exception_runtime.c

**Location**: `runtime/exception_runtime.c`

**Purpose**: PNaCl SJLJ exception handling implementation.

**Size**: 800-1200 bytes

**Key Functions**:
```c
void cxx_throw(void *exception, const void *type_info);
void cxx_frame_push(CXXExceptionFrame *frame);
void cxx_frame_pop(CXXExceptionFrame *frame);
void cxx_handle_exception(void);
```

---

### rtti_runtime.c

**Location**: `runtime/rtti_runtime.c`

**Purpose**: Itanium ABI RTTI implementation.

**Size**: 600-1000 bytes

**Key Functions**:
```c
void* cxx_dynamic_cast(const void *ptr,
                       const __class_type_info *src,
                       const __class_type_info *dst,
                       ptrdiff_t offset);

int cxx_type_matches(const __class_type_info *a,
                    const __class_type_info *b);
```

---

### memory_runtime.c

**Location**: `runtime/memory_runtime.c`

**Purpose**: Memory management for coroutines.

**Size**: 100-200 bytes

**Key Functions**:
```c
void* cxx_coro_alloc(size_t size);
void cxx_coro_free(void* ptr);
```

---

### vinherit_runtime.c

**Location**: `runtime/vinherit_runtime.c`

**Purpose**: Virtual inheritance support.

**Size**: 200-400 bytes

**Key Functions**:
```c
void* cxx_get_vbase(const void *obj,
                    const void *vtable,
                    unsigned vbase_idx);
```

---

## Module Dependencies

```
CppToCFrontendAction
└── CppToCConsumer
    ├── CppToCVisitor
    │   ├── CNodeBuilder
    │   ├── ThrowTranslator
    │   ├── TryCatchTransformer
    │   │   ├── ExceptionFrameGenerator
    │   │   └── ActionTableGenerator
    │   │       └── CFGAnalyzer
    │   ├── TypeInfoGenerator
    │   ├── DynamicCastTranslator
    │   ├── VtableGenerator
    │   │   └── VirtualMethodAnalyzer
    │   ├── VTTGenerator
    │   │   └── VirtualInheritanceAnalyzer
    │   └── StateMachineTransformer
    │       └── CoroutineDetector
    └── FileOutputManager
        ├── HeaderSeparator
        ├── IncludeGuardGenerator
        ├── CodeGenerator
        └── DependencyAnalyzer
```

---

**Document Version**: 1.0
**Last Updated**: 2025-12-18
**See Also**: [OVERVIEW.md](OVERVIEW.md), [EXTENSION_GUIDE.md](EXTENSION_GUIDE.md)

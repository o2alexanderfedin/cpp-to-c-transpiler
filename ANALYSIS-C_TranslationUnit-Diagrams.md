# C TranslationUnit Architecture - Visual Diagrams

## 1. Multi-File Transpilation Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         TRANSPILATION PIPELINE                           │
└─────────────────────────────────────────────────────────────────────────┘

INPUT FILES:
  ├─ Vector3D.cpp  ─────────┐
  ├─ Matrix4x4.cpp ─────────┤
  └─ main.cpp ───────────────┤
                             │
                             ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    STAGE 1: CLANG FRONTEND PARSING                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                           │
│  Each File Gets Its Own C++ ASTContext:                                 │
│                                                                           │
│  Vector3D.cpp  ──→ Context1 (C++ AST) ──→ TU1 (C++ decls)              │
│  Matrix4x4.cpp ──→ Context2 (C++ AST) ──→ TU2 (C++ decls)              │
│  main.cpp      ──→ Context3 (C++ AST) ──→ TU3 (C++ decls)              │
│                                                                           │
│  (These are IMMUTABLE - created by Clang frontend)                       │
│                                                                           │
└─────────────────────────────────────────────────────────────────────────┘
                             │
                             ▼
┌──────────────────────────────────────────────────────────────────────────┐
│              STAGE 2: CPPTOCONSUMER TRANSLATION SETUP                    │
├──────────────────────────────────────────────────────────────────────────┤
│                                                                            │
│  For Each C++ ASTContext:                                                │
│                                                                            │
│  1. Get TargetContext singleton (ONE for all files)                      │
│  2. Get shared target ASTContext from TargetContext                      │
│  3. Create CNodeBuilder(targetCtx.getContext())                          │
│  4. Create NEW C_TranslationUnit in shared context                       │
│  5. Pass C_TU to CppToCVisitor                                           │
│                                                                            │
│     ┌─────────────────────────────────────────────────────────┐          │
│     │       TargetContext (SINGLETON - ONE INSTANCE)          │          │
│     ├─────────────────────────────────────────────────────────┤          │
│     │  Shared Target ASTContext (for C output)                │          │
│     │  - IntTy, VoidTy, BoolTy, etc.                          │          │
│     │  - IdentifierTable, SelectorTable                       │          │
│     │  - TargetInfo, DiagnosticsEngine                        │          │
│     └─────────────────────────────────────────────────────────┘          │
│            ▲           ▲           ▲                                      │
│            │           │           │                                      │
│     ┌──────┴─┐  ┌──────┴─┐  ┌─────┴──┐                                   │
│     │ C_TU1  │  │ C_TU2  │  │ C_TU3  │  Per-file Translation Units      │
│     │ (for   │  │ (for   │  │ (for   │  Created in shared context       │
│     │Vector) │  │Matrix) │  │ main)  │                                   │
│     └────────┘  └────────┘  └────────┘                                   │
│                                                                            │
└──────────────────────────────────────────────────────────────────────────┘
                             │
                             ▼
┌──────────────────────────────────────────────────────────────────────────┐
│              STAGE 3: CPPTOCVISITOR TRANSLATION                          │
├──────────────────────────────────────────────────────────────────────────┤
│                                                                            │
│  For Each File's C++ AST:                                                │
│                                                                            │
│  CppToCVisitor.VisitCXXRecordDecl(Vector3D class):                       │
│    ├─ Create C struct: struct Vector3D { ... }                           │
│    ├─ Create in shared ASTContext (Builder.structDecl)                   │
│    ├─ Add to per-file C_TU: C_TU1->addDecl(struct)                       │
│    └─ Store in cppToCMap[Vector3D_class_ptr] = struct_ptr                │
│                                                                            │
│  CppToCVisitor.VisitCXXConstructorDecl(Vector3D::Vector3D()):            │
│    ├─ Create C function: struct Vector3D__ctor_3(...)                    │
│    ├─ Create in shared ASTContext                                        │
│    ├─ Add to per-file C_TU: C_TU1->addDecl(function)                     │
│    └─ Add to shared map: targetCtx.getCtorMap()[mangledName] = function  │
│                                                                            │
│  CppToCVisitor.VisitCXXMethodDecl(Vector3D::normalize()):                │
│    ├─ Create C function: Vector3D__normalize(struct Vector3D *this)      │
│    ├─ Create in shared ASTContext                                        │
│    ├─ Add to per-file C_TU: C_TU1->addDecl(function)                     │
│    └─ Add to shared map: targetCtx.getMethodMap()[mangledName] = func    │
│                                                                            │
└──────────────────────────────────────────────────────────────────────────┘
                             │
                             ▼
┌──────────────────────────────────────────────────────────────────────────┐
│              STAGE 4: CODE GENERATION FROM C_TU                          │
├──────────────────────────────────────────────────────────────────────────┤
│                                                                            │
│  For Each Per-File C_TU:                                                 │
│                                                                            │
│  Generate Vector3D.h:                                                    │
│    ├─ Iterate C_TU1->decls()                                             │
│    ├─ Print struct declarations                                          │
│    ├─ Print function declarations (declaration only)                     │
│    └─ Write to Vector3D.h                                                │
│                                                                            │
│  Generate Vector3D.c:                                                    │
│    ├─ Iterate C_TU1->decls()                                             │
│    ├─ Print struct definitions                                           │
│    ├─ Print function definitions (full body)                             │
│    ├─ #include "Vector3D.h"                                              │
│    └─ Write to Vector3D.c                                                │
│                                                                            │
│  Generate Matrix4x4.h, Matrix4x4.c, main.h, main.c similarly             │
│                                                                            │
└──────────────────────────────────────────────────────────────────────────┘

OUTPUT FILES:
  ├─ Vector3D.h     (declarations from C_TU1)
  ├─ Vector3D.c     (definitions from C_TU1)
  ├─ Matrix4x4.h    (declarations from C_TU2)
  ├─ Matrix4x4.c    (definitions from C_TU2)
  ├─ main.h         (declarations from C_TU3)
  └─ main.c         (definitions from C_TU3)
```

---

## 2. Data Flow: From C++ AST to C_TU to Output

```
┌──────────────────┐
│  C++ Class Decl  │
│  (Vector3D)      │
│  in Context1     │
└────────┬─────────┘
         │
         ▼
┌────────────────────────────────────────┐
│  CppToCVisitor.VisitCXXRecordDecl()   │
├────────────────────────────────────────┤
│  ┌─ Read C++ AST (Vector3D class)      │
│  ├─ Extract field declarations        │
│  ├─ Plan C struct layout               │
│  └─ Create C struct via Builder        │
└────────┬───────────────────────────────┘
         │
         ▼
┌────────────────────────────────────────┐
│  CNodeBuilder.structDecl()             │
├────────────────────────────────────────┤
│  1. Create RecordDecl in shared ctx    │
│  2. Add FieldDecls to struct           │
│  3. Add struct to shared TU            │◄── ADDS TO SHARED TU
│  4. Return struct pointer              │
└────────┬───────────────────────────────┘
         │ (struct created in shared context)
         │ (added to shared TU - NOT per-file!)
         ▼
┌────────────────────────────────────────┐
│  CppToCVisitor.VisitCXXRecordDecl()   │
│  (continuation)                        │
├────────────────────────────────────────┤
│  1. Receive struct from Builder        │
│  2. ALSO add to per-file C_TU:         │
│     C_TranslationUnit->addDecl(struct)◄── CRITICAL FIX!
│  3. Store in cppToCMap                 │
│  4. Return                             │
└────────┬───────────────────────────────┘
         │
         ▼
┌────────────────────────────────────────┐
│  C_TU1->decls() iteration              │
│  (in CodeGenerator)                    │
├────────────────────────────────────────┤
│  for (auto *D : C_TU1->decls()) {      │
│      if (!D->isImplicit()) {           │
│          headerGen.printDecl(D, true); │
│          implGen.printDecl(D, false);  │
│      }                                  │
│  }                                      │
└────────┬───────────────────────────────┘
         │
         ▼
┌────────────────────────────────────────┐
│  CodeGenerator.printDecl()             │
├────────────────────────────────────────┤
│  Match D->getTypeClass():              │
│  - RecordType: Print struct definition │
│  - FunctionType: Print function decl   │
│  - EnumType: Print enum constants      │
└────────┬───────────────────────────────┘
         │
         ▼
┌────────────────────────────────────────┐
│  Output Streams                        │
├────────────────────────────────────────┤
│  headerOS << "struct Vector3D { ... };"│
│  implOS   << "struct Vector3D { ... };"│
│  implOS   << "void Vector3D__ctor() {}"│
└────────┬───────────────────────────────┘
         │
         ▼
┌────────────────────────────────────────┐
│  FileOutputManager                     │
├────────────────────────────────────────┤
│  1. Get basename from InputFilename    │
│  2. Create Vector3D.h from headerOS    │
│  3. Create Vector3D.c from implOS      │
│  4. Write to disk                      │
└────────────────────────────────────────┘
```

---

## 3. TargetContext Singleton Structure

```
                     ┌──────────────────────────────────┐
                     │   TargetContext::instance        │
                     │  (static member - ONE only)      │
                     └────────────┬─────────────────────┘
                                  │
                                  ▼
                    ┌─────────────────────────────────────┐
                    │   TargetContext (SINGLETON)         │
                    ├─────────────────────────────────────┤
                    │                                     │
                    │  INFRASTRUCTURE:                    │
                    │  ├─ FileManager                     │
                    │  ├─ DiagnosticsEngine              │
                    │  ├─ SourceManager                  │
                    │  ├─ TargetInfo (host triple)       │
                    │  ├─ IdentifierTable                │
                    │  ├─ SelectorTable                  │
                    │  └─ Builtin::Context               │
                    │                                     │
                    │  SHARED TARGET ASTCONTEXT:         │
                    │  └─ Context (unique_ptr)           │◄─ CREATED ONCE
                    │      - IntTy, VoidTy, BoolTy       │
                    │      - Owns all C AST nodes        │
                    │                                     │
                    │  SHARED CROSS-FILE MAPS:           │
                    │  ├─ ctorMap (string -> FuncDecl*)  │
                    │  ├─ methodMap (string -> FuncDecl*)│
                    │  └─ dtorMap (string -> FuncDecl*)  │
                    │                                     │
                    │  PUBLIC METHODS:                    │
                    │  ├─ getInstance() -> ref           │
                    │  ├─ getContext() -> ASTContext&    │
                    │  ├─ createTranslationUnit() -> C_TU│
                    │  ├─ getCtorMap() -> map&           │
                    │  ├─ getMethodMap() -> map&         │
                    │  ├─ getDtorMap() -> map&           │
                    │  └─ cleanup()                       │
                    │                                     │
                    └─────────────┬───────────────────────┘
                                  │
                        ┌─────────┴─────────┬────────────┐
                        │                   │            │
                        ▼                   ▼            ▼
                   ┌─────────┐         ┌─────────┐  ┌─────────┐
                   │ C_TU1   │         │ C_TU2   │  │ C_TU3   │
                   │ (file1) │         │ (file2) │  │ (file3) │
                   │ ALL IN  │         │ ALL IN  │  │ ALL IN  │
                   │ SHARED  │         │ SHARED  │  │ SHARED  │
                   │ CONTEXT │         │ CONTEXT │  │ CONTEXT │
                   └─────────┘         └─────────┘  └─────────┘

    CRITICAL DESIGN:
    ├─ ONE TargetContext instance (singleton)
    ├─ ONE shared ASTContext
    ├─ MULTIPLE per-file C_TUs (all in shared context)
    └─ SHARED maps for cross-file references
```

---

## 4. Declaration Addition Flow

```
   CppToCVisitor Input              CNodeBuilder              Result
   ───────────────────────────────────────────────────────────────────

   C++ class: Vector3D
   ├─ Field: x (float)
   ├─ Field: y (float)
   ├─ Field: z (float)
   └─ Constructor()
                    │
                    ▼
   cppToCMap lookup: not found
                    │
                    ▼
   Create C struct via Builder.structDecl()
                    │
                    ├─► Create FieldDecl (x)
                    ├─► Create FieldDecl (y)
                    ├─► Create FieldDecl (z)
                    ├─► Create RecordDecl
                    ├─► Add fields to struct
                    ├─► Builder adds to shared TU (BUG!)
                    │
                    └─► Return RecordDecl*
                         │
                         ▼
                    RecordDecl* struct_ptr
                    (in shared context,
                     also in shared TU)
                         │
                         ▼
   Store in cppToCMap[Vector3D_ptr] = struct_ptr
                         │
                         ▼
   CRITICAL FIX:
   C_TranslationUnit->addDecl(struct_ptr)  ◄── NOW in per-file TU
                         │
                         ▼
   struct_ptr is now in BOTH:
   ├─ Shared target ASTContext (owner)
   ├─ Shared TU (from Builder)
   └─ Per-file C_TU (from visitor) ◄── WILL BE EMITTED


   CONSTRUCTOR: Vector3D::Vector3D()
                         │
                         ▼
   Create C function via Builder.funcDecl()
                         │
                    ├─► Create ParmVarDecl (this)
                    ├─► Create FunctionDecl
                    ├─► Set function body
                    ├─► Builder adds to shared TU
                    │
                    └─► Return FunctionDecl*
                         │
                         ▼
                    FunctionDecl* ctor_ptr
                    (in shared context)
                         │
                         ▼
   CRITICAL FIX:
   C_TranslationUnit->addDecl(ctor_ptr)  ◄── Add to per-file TU
                         │
                         ▼
   Cross-file sharing:
   targetCtx.getCtorMap()[mangledName] = ctor_ptr  ◄── Share with other files
```

---

## 5. Multi-File Reference Handling

```
File 1: Vector3D.cpp
┌─────────────────────────────────────┐
│ CppToCVisitor1                      │
├─────────────────────────────────────┤
│ Processes Vector3D class            │
│ Processes Vector3D::Vector3D()      │
│                                     │
│ Creates:                            │
│ ├─ struct Vector3D                  │
│ │  └─► Added to C_TU1               │
│ └─ Vector3D__ctor_3                 │
│    ├─► Added to C_TU1               │
│    └─► Stored in:                   │
│        targetCtx.getCtorMap()        │
│        ["_ZN8Vector3DC1ERfff"]       │
│                                     │
└─────────────────────────────────────┘
           │
           │ (creates Vector3D.h, Vector3D.c)
           ▼

File 2: main.cpp
┌─────────────────────────────────────┐
│ CppToCVisitor2                      │
├─────────────────────────────────────┤
│ Processes main() function           │
│ Encounters: Vector3D v(1.0, 2.0...) │
│                                     │
│ To translate constructor call:      │
│ 1. Lookup mangled name in           │
│    targetCtx.getCtorMap()           │
│    ["_ZN8Vector3DC1ERfff"]          │
│ 2. Find FunctionDecl* from File 1   │
│ 3. Use that FunctionDecl in call    │
│    Vector3D__ctor_3(&v, 1.0, 2.0...) │
│                                     │
│ Generates #include "Vector3D.h"     │
│                                     │
└─────────────────────────────────────┘
           │
           │ (creates main.h, main.c)
           ▼

LINKING:
main.c #includes Vector3D.h
main.c calls Vector3D__ctor_3() from Vector3D.c
Linker resolves symbols correctly
```

---

## 6. C_TU Iteration (Code Generation)

```
CppToCConsumer::HandleTranslationUnit()
       │
       ▼
   Validate C_TU
   ├─ Count declarations:
   │  auto DeclCount = std::distance(
   │      C_TU->decls().begin(),
   │      C_TU->decls().end());
   │  Output: "C TranslationUnit has 47 generated declarations"
   │
   └─ Check if empty:
      if (CTU_DeclCount == 0) {
          // Warning: no declarations
      }
       │
       ▼
   Generate Header File
   ├─ Open: headerOS
   ├─ Write: "#pragma once"
   ├─ Write: "#include <stdio.h>, etc."
   ├─ Write: User header includes
   ├─ Iterate C_TU:
   │  for (auto *D : C_TU->decls()) {  ◄── KEY LINE
   │      if (!D->isImplicit()) {
   │          headerGen.printDecl(D, true);
   │      }
   │  }
   └─ Flush to string
       │
       ▼
   Generate Implementation File
   ├─ Open: implOS
   ├─ Write: "#include \"Vector3D.h\""
   ├─ Iterate C_TU:
   │  for (auto *D : C_TU->decls()) {  ◄── KEY LINE
   │      if (!D->isImplicit()) {
   │          implGen.printDecl(D, false);
   │      }
   │  }
   └─ Flush to string
       │
       ▼
   Write Output Files
   └─ FileOutputManager::writeFiles(headerContent, implContent)
      ├─ Create Vector3D.h with headerContent
      ├─ Create Vector3D.c with implContent
      └─ Increment g_filesGeneratedCount++
```

---

## 7. Key Design Invariants

```
INVARIANT 1: Single Shared Target Context
┌─────────────────────────────────────────────────┐
│ ALL C AST nodes created in the same ASTContext  │
│ This allows cross-file type compatibility       │
│ IntTy, PointerType, etc. are shared globally    │
└─────────────────────────────────────────────────┘

INVARIANT 2: Per-File C_TU Organization
┌─────────────────────────────────────────────────┐
│ Each source file gets ONE C_TranslationUnit     │
│ All nodes for that file added to its C_TU       │
│ Enables per-file .h and .c generation           │
└─────────────────────────────────────────────────┘

INVARIANT 3: Cross-File References via Maps
┌─────────────────────────────────────────────────┐
│ When file B needs constructor from file A:      │
│ 1. Constructor added to ctorMap by visitor of A │
│ 2. Visitor of B looks up mangled name in map    │
│ 3. Reuses the FunctionDecl* from file A         │
│ 4. Linking combines object files               │
└─────────────────────────────────────────────────┘

INVARIANT 4: Builder Adds to Shared TU
┌─────────────────────────────────────────────────┐
│ CNodeBuilder.structDecl() and funcDecl():       │
│ ├─ Create node in shared context (correct)     │
│ ├─ Add to Ctx.getTranslationUnitDecl() (shared)│
│ └─ Don't add to per-file C_TU (BUG!)           │
│                                                 │
│ WORKAROUND in CppToCVisitor:                   │
│ ├─ Receive node from Builder                   │
│ ├─ ALSO: C_TranslationUnit->addDecl(node)     │
│ └─ Now node is in per-file C_TU (FIX!)        │
└─────────────────────────────────────────────────┘
```

---

## 8. Extension Point: Creating Multiple C_TUs

To create multiple C_TUs from a single source file:

```
File: main.cpp
  ├─ class Vector3D      (goes to Vector3D module)
  ├─ class Matrix4x4     (goes to Matrix4x4 module)
  └─ void main()         (goes to main module)

CURRENT: One C_TU per file
  └─ C_TU1 contains all declarations

EXTENDED: Multiple C_TUs per file
  ├─ C_TU_Vector = targetCtx.createTranslationUnit()
  ├─ C_TU_Matrix = targetCtx.createTranslationUnit()
  └─ C_TU_Main = targetCtx.createTranslationUnit()

  CppToCVisitor:
    VisitCXXRecordDecl(Vector3D) {
        C_TU_Vector->addDecl(struct);
    }
    VisitCXXRecordDecl(Matrix4x4) {
        C_TU_Matrix->addDecl(struct);
    }
    VisitFunctionDecl(main) {
        C_TU_Main->addDecl(function);
    }

  CodeGen:
    for (auto *D : C_TU_Vector->decls()) {
        // Generate Vector.h and Vector.c
    }
    for (auto *D : C_TU_Matrix->decls()) {
        // Generate Matrix.h and Matrix.c
    }
    for (auto *D : C_TU_Main->decls()) {
        // Generate main.h and main.c
    }

OUTPUT:
  ├─ Vector.h
  ├─ Vector.c
  ├─ Matrix.h
  ├─ Matrix.c
  ├─ main.h
  └─ main.c
```

---

## Summary

```
     C++ Source Files (Multiple)
              │
              ▼
    Clang Frontend → C++ AST (Multiple contexts)
              │
              ▼
    CppToCConsumer (For each file)
              ├─ TargetContext::getInstance()
              ├─ createTranslationUnit() → Per-file C_TU
              ├─ Create CppToCVisitor
              └─ Pass C_TU to visitor
                       │
                       ▼
              CppToCVisitor (For each file)
              ├─ Traverse C++ AST
              ├─ Create C nodes in shared ASTContext
              └─ Add nodes to per-file C_TU
                       │
                       ▼
              CodeGenerator (For each C_TU)
              ├─ Iterate C_TU->decls()
              ├─ Emit C code
              └─ Write .h and .c files
                       │
                       ▼
              Output Files (One pair per input file)
              ├─ file1.h, file1.c
              ├─ file2.h, file2.c
              └─ ...
```

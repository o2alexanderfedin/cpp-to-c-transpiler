# Stage 1: Research - extern "C" and Calling Convention Support

## Executive Summary

This document provides comprehensive technical analysis of Clang's AST representation of language linkage (`extern "C"`) and calling conventions, including detection strategies, C code generation approaches, edge cases, and implementation requirements for the C++ to C transpiler.

### Key Findings

1. **LinkageSpecDecl** wraps `extern "C" { }` blocks in the AST with language type detection
2. **FunctionDecl** provides `isExternC()`, `getLanguageLinkage()` APIs for linkage queries
3. **CallingConv** enum has 30+ values covering x86, x64, ARM, and specialized conventions
4. **Platform differences** exist between x86 (32-bit) and x86_64 (64-bit) calling conventions
5. **Recommended approach**: Strip `extern "C"` (redundant in pure C), preserve calling conventions with attributes
6. **Edge cases** include templates with extern "C" (illegal), function overloading (illegal), and platform incompatibilities

---

## 1. Clang AST Representation

### 1.1 LinkageSpecDecl

The `LinkageSpecDecl` class represents linkage specifications like `extern "C"` or `extern "C++"`.

**Class Definition:**
- Defined in `clang/AST/DeclCXX.h`
- Inherits from both `Decl` and `DeclContext`
- Official documentation: [LinkageSpecDecl Class Reference](https://clang.llvm.org/doxygen/classclang_1_1LinkageSpecDecl.html)

**Key Methods:**

```cpp
class LinkageSpecDecl : public Decl, public DeclContext {
public:
    // Language specification
    enum LanguageIDs {
        lang_c = 1,      // extern "C"
        lang_cxx = 2     // extern "C++"
    };

    LanguageIDs getLanguage() const;
    void setLanguage(LanguageIDs L);

    // Brace handling
    bool hasBraces() const;  // true for extern "C" { }, false for extern "C" func()

    // Location tracking
    SourceLocation getExternLoc() const;      // Location of 'extern' keyword
    SourceLocation getRBraceLoc() const;      // Right brace location (if hasBraces())
};
```

**Context Semantics:**
- **Semantic context**: Declarations within `extern "C"` belong to their enclosing namespace
- **Lexical context**: The LinkageSpecDecl itself
- Both contexts make declarations visible in the extern "C" scope

**Detection Example:**

```cpp
bool VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS) {
    if (LS->getLanguage() == LinkageSpecDecl::lang_c) {
        // This is extern "C"
        if (LS->hasBraces()) {
            // extern "C" { ... } block form
        } else {
            // extern "C" single declaration form
        }
    } else if (LS->getLanguage() == LinkageSpecDecl::lang_cxx) {
        // This is extern "C++"
    }
    return true;
}
```

### 1.2 Language Linkage Detection

The `LanguageLinkage` enum defines three linkage types:

**Enum Definition** (from `clang/Basic/Linkage.h`):

```cpp
enum LanguageLinkage {
    CLanguageLinkage,    // C language linkage
    CXXLanguageLinkage,  // C++ language linkage
    NoLanguageLinkage    // No language linkage
};
```

Source: [Linkage.h File Reference](https://clang.llvm.org/doxygen/include_2clang_2Basic_2Linkage_8h.html)

**FunctionDecl Methods:**

```cpp
class FunctionDecl {
public:
    // Check if function has C linkage
    bool isExternC() const;

    // Check if function has C++ linkage
    bool isExternCXX() const;

    // Get language linkage type
    LanguageLinkage getLanguageLinkage() const;
};
```

Official documentation: [FunctionDecl Class Reference](https://clang.llvm.org/doxygen/classclang_1_1FunctionDecl.html)

**Context-Based Detection:**

```cpp
class DeclContext {
public:
    // Check if context is within extern "C"
    bool isExternCContext() const;

    // Check if context is within extern "C++"
    bool isExternCXXContext() const;
};
```

**Key Differences:**

| Method | Purpose | Use Case |
|--------|---------|----------|
| `isExternC()` | Direct C linkage check | Quick boolean check for C linkage |
| `getLanguageLinkage()` | Full linkage type | Distinguish C vs C++ vs None |
| `isExternCContext()` | Context-based check | Check if declaration context has C linkage |

**Impact on Name Mangling:**

Functions with C linkage (`isExternC() == true`) should **not** be mangled. The transpiler's `NameMangler` must check this before applying C++ name mangling rules.

```cpp
std::string NameMangler::mangleFunctionName(FunctionDecl *FD) {
    // Skip mangling for extern "C" functions
    if (FD->isExternC()) {
        return FD->getName().str();  // Return unmangled name
    }

    // Apply namespace-aware C++ mangling
    std::vector<std::string> namespaces = extractNamespaceHierarchy(FD);
    std::string mangledName;
    for (const auto &ns : namespaces) {
        mangledName += ns + "_";
    }
    mangledName += FD->getName().str();
    return mangledName;
}
```

### 1.3 Calling Convention Representation

Calling conventions control argument passing, stack management, and register preservation across function calls.

**CallingConv Enum** (from `clang/Basic/Specifiers.h` and `llvm/IR/CallingConv.h`):

Source: [CallingConv Namespace Reference](https://llvm.org/doxygen/namespacellvm_1_1CallingConv.html)

**Complete List of Calling Conventions:**

```cpp
enum CallingConv {
    // Default conventions
    CC_C = 0,                  // __attribute__((cdecl)) - Default C convention

    // x86 (32-bit) conventions
    CC_X86StdCall = 64,        // __attribute__((stdcall)) - Windows API
    CC_X86FastCall = 65,       // __attribute__((fastcall)) - Register-based
    CC_X86ThisCall = 66,       // __attribute__((thiscall)) - C++ member functions
    CC_X86Pascal = 67,         // __attribute__((pascal)) - Legacy Pascal
    CC_X86VectorCall = 80,     // __attribute__((vectorcall)) - SIMD optimization
    CC_X86RegCall = 92,        // __attribute__((regcall)) - Intel register-based

    // x86_64 (64-bit) conventions
    CC_X86_64Win64 = 69,       // __attribute__((ms_abi)) - Microsoft x64 ABI
    CC_X86_64SysV = 68,        // __attribute__((sysv_abi)) - System V AMD64 ABI

    // ARM conventions
    CC_AAPCS = 71,             // __attribute__((pcs("aapcs"))) - ARM Procedure Call Standard
    CC_AAPCS_VFP = 72,         // __attribute__((pcs("aapcs-vfp"))) - ARM with VFP
    CC_AArch64VectorCall = 97, // __attribute__((aarch64_vector_pcs))
    CC_AArch64SVEPCS = 98,     // Scalable Vector Extension

    // Specialized conventions
    CC_Swift = 93,             // Swift calling convention
    CC_SwiftAsync = 94,        // Swift async functions
    CC_PreserveMost = 95,      // Preserve most registers
    CC_PreserveAll = 96,       // Preserve all registers
    CC_PreserveNone = 99,      // Preserve no registers (recent addition)

    // GPU/Kernel conventions
    CC_AMDGPUKernelCall = 100, // __attribute__((amdgpu_kernel))
    CC_DeviceKernel = 101,     // Device kernel functions

    // Miscellaneous
    CC_IntelOclBicc = 77,      // __attribute__((intel_ocl_bicc)) - Intel OpenCL
    CC_PnaclCall = 78,         // __attribute__((pnaclcall)) - PNaCl
    CC_M68kRTD = 102,          // __attribute__((m68k_rtd)) - Motorola 68000
};
```

**FunctionType::ExtInfo API:**

```cpp
class FunctionType {
public:
    class ExtInfo {
    public:
        // Get calling convention
        CallingConv getCallConv() const;

        // Other extension info
        bool getNoReturn() const;
        bool getProducesResult() const;
        bool getNoCallerSavedRegs() const;
        bool getNoCfCheck() const;
    };

    ExtInfo getExtInfo() const;
};
```

Source: [FunctionType::ExtInfo Class Reference](https://clang.llvm.org/doxygen/classclang_1_1FunctionType_1_1ExtInfo.html)

**Querying Calling Convention:**

```cpp
bool VisitFunctionDecl(clang::FunctionDecl *FD) {
    // Get function type
    const FunctionType *FT = FD->getType()->getAs<FunctionType>();
    if (!FT) return true;

    // Query calling convention
    CallingConv CC = FT->getExtInfo().getCallConv();

    switch (CC) {
        case CC_C:
            // Default C calling convention (cdecl)
            break;
        case CC_X86StdCall:
            // Windows stdcall convention
            break;
        case CC_X86FastCall:
            // Fastcall convention
            break;
        case CC_X86ThisCall:
            // C++ member function convention (thiscall)
            break;
        // ... handle other conventions
    }

    return true;
}
```

**Attribute Classes:**

Clang also provides attribute classes for calling conventions:

- `StdCallAttr` - `__attribute__((stdcall))`
- `FastCallAttr` - `__attribute__((fastcall))`
- `CdeclAttr` - `__attribute__((cdecl))`
- `VectorCallAttr` - `__attribute__((vectorcall))`
- etc.

These can be queried using:

```cpp
if (FD->hasAttr<StdCallAttr>()) {
    // Function has explicit stdcall attribute
}
```

---

## 2. Detection Strategies

### 2.1 extern "C" Detection

**Visitor Method Implementation:**

Add `VisitLinkageSpecDecl()` to `CppToCVisitor`:

```cpp
class CppToCVisitor : public clang::RecursiveASTVisitor<CppToCVisitor> {
public:
    // Visit linkage specification (extern "C" { }) blocks
    bool VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS);

private:
    // Track current extern "C" context
    bool inExternCBlock = false;
    std::vector<LinkageSpecDecl*> linkageStack;
};

bool CppToCVisitor::VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS) {
    if (LS->getLanguage() == LinkageSpecDecl::lang_c) {
        // Entering extern "C" block
        linkageStack.push_back(LS);
        inExternCBlock = true;

        if (LS->hasBraces()) {
            // Block form: extern "C" { ... }
            // Child declarations will be visited automatically
        } else {
            // Single declaration form: extern "C" void foo();
        }
    } else if (LS->getLanguage() == LinkageSpecDecl::lang_cxx) {
        // extern "C++" (rare, usually used to restore C++ linkage inside extern "C")
        inExternCBlock = false;
    }

    return true;  // Continue visiting children
}
```

**Function-Level Detection:**

Enhance `VisitFunctionDecl()` to query linkage:

```cpp
bool CppToCVisitor::VisitFunctionDecl(clang::FunctionDecl *FD) {
    // Query language linkage
    bool isExternC = FD->isExternC();
    LanguageLinkage linkage = FD->getLanguageLinkage();

    if (isExternC) {
        // Function has C linkage - suppress name mangling
        std::string unmangledName = FD->getName().str();
        // Generate C function with original name
    } else if (linkage == CXXLanguageLinkage) {
        // Function has C++ linkage - apply name mangling
        std::string mangledName = Mangler.mangleFunctionName(FD);
        // Generate C function with mangled name
    }

    return true;
}
```

**Handling Forward Declarations vs Definitions:**

```cpp
bool CppToCVisitor::VisitFunctionDecl(clang::FunctionDecl *FD) {
    // Skip forward declarations - only process definitions
    if (!FD->isThisDeclarationADefinition()) {
        return true;
    }

    // Check linkage for definitions
    bool isExternC = FD->isExternC();
    // ... process definition

    return true;
}
```

**Propagation to Nested Declarations:**

Declarations inside `extern "C" { }` blocks inherit C linkage automatically. The visitor will encounter them as child nodes of the `LinkageSpecDecl`.

```cpp
// C++ code:
extern "C" {
    void foo();     // FunctionDecl with C linkage
    int bar(int);   // FunctionDecl with C linkage
}

// AST structure:
// LinkageSpecDecl (lang_c, hasBraces=true)
//   |- FunctionDecl (foo, isExternC()=true)
//   |- FunctionDecl (bar, isExternC()=true)
```

### 2.2 Calling Convention Detection

**Querying FunctionDecl::getCallConv():**

```cpp
bool CppToCVisitor::VisitFunctionDecl(clang::FunctionDecl *FD) {
    // Get function type
    const FunctionType *FT = FD->getType()->getAs<FunctionType>();
    if (!FT) return true;

    // Get calling convention
    CallingConv CC = FT->getExtInfo().getCallConv();

    // Check if non-default
    if (CC != CC_C) {
        // Function has explicit calling convention
        std::string ccString = getCallingConvString(CC);
        // Store for code generation
    }

    return true;
}

std::string getCallingConvString(CallingConv CC) {
    switch (CC) {
        case CC_C:           return "cdecl";
        case CC_X86StdCall:  return "stdcall";
        case CC_X86FastCall: return "fastcall";
        case CC_X86ThisCall: return "thiscall";
        case CC_X86Pascal:   return "pascal";
        case CC_X86VectorCall: return "vectorcall";
        case CC_X86RegCall:  return "regcall";
        case CC_X86_64Win64: return "ms_abi";
        case CC_X86_64SysV:  return "sysv_abi";
        default:             return "unknown";
    }
}
```

**Detecting Platform Default vs Explicit Specification:**

- **Default convention**: `CC_C` (cdecl on most platforms)
- **Explicit specification**: Any non-CC_C value indicates explicit calling convention

Check if function has explicit calling convention attribute:

```cpp
bool hasExplicitCallingConv(FunctionDecl *FD) {
    // Check for explicit attributes
    if (FD->hasAttr<StdCallAttr>() ||
        FD->hasAttr<FastCallAttr>() ||
        FD->hasAttr<CdeclAttr>() ||
        FD->hasAttr<VectorCallAttr>()) {
        return true;
    }

    // Check if calling convention differs from default
    const FunctionType *FT = FD->getType()->getAs<FunctionType>();
    if (FT && FT->getExtInfo().getCallConv() != CC_C) {
        return true;
    }

    return false;
}
```

**Function Pointers with Calling Conventions:**

Function pointer types also carry calling convention information:

```cpp
// C++ code:
typedef void (__stdcall *StdCallFuncPtr)(int);

// Detection:
bool VisitTypedefDecl(clang::TypedefDecl *TD) {
    QualType underlyingType = TD->getUnderlyingType();

    if (const PointerType *PT = underlyingType->getAs<PointerType>()) {
        if (const FunctionProtoType *FPT = PT->getPointeeType()->getAs<FunctionProtoType>()) {
            CallingConv CC = FPT->getExtInfo().getCallConv();
            // Function pointer has calling convention
        }
    }

    return true;
}
```

**Member Function Calling Conventions:**

C++ member functions on Windows use `thiscall` by default:

```cpp
bool VisitCXXMethodDecl(clang::CXXMethodDecl *MD) {
    const FunctionType *FT = MD->getType()->getAs<FunctionType>();
    CallingConv CC = FT->getExtInfo().getCallConv();

    if (CC == CC_X86ThisCall) {
        // Default member function convention on Windows (x86)
        // In generated C code, 'this' becomes explicit first parameter
    }

    return true;
}
```

---

## 3. C Code Generation Strategy

### 3.1 extern "C" Functions - Analysis and Recommendation

**Option A: Pass Through (Skip Transpilation)**

Pros:
- Preserves exact original code
- No modifications needed

Cons:
- Requires mixed C/C++ compilation
- Generated code is not pure C
- Violates transpiler goal of producing C-only output

**Verdict**: ❌ Not viable for pure C output

---

**Option B: Strip and Note (Transpile, Add Comment)**

Approach:
- Transpile function normally
- Remove `extern "C"` (redundant in pure C)
- Add comment noting original linkage

Example:

```cpp
// C++ input:
extern "C" int add(int a, int b) {
    return a + b;
}

// Generated C output:
/* Originally: extern "C" */
int add(int a, int b) {
    return a + b;
}
```

Pros:
- Pure C output
- Documentation preserved via comments
- Name remains unmangled (correct behavior)
- Simple implementation

Cons:
- Comment-only documentation (not machine-readable)

**Verdict**: ✅ **RECOMMENDED** (simple, correct, pure C)

---

**Option C: Preserve with Conditional Compilation**

Approach:
- Use `#ifdef __cplusplus` guards
- Preserve `extern "C"` for C++ compilation

Example:

```cpp
// Generated C output:
#ifdef __cplusplus
extern "C" {
#endif

int add(int a, int b) {
    return a + b;
}

#ifdef __cplusplus
}
#endif
```

Pros:
- Can compile as both C and C++
- Preserves linkage information

Cons:
- More complex code generation
- Conditional compilation adds noise
- Not necessary for pure C target

**Verdict**: ⚠️ Viable for C/C++ compatibility, but not needed for pure C transpiler

---

**RECOMMENDATION FOR extern "C":**

**Adopt Option B: Strip and Note**

Rationale:
1. `extern "C"` is **redundant** in pure C (all C functions have C linkage by default)
2. Transpiler goal is **pure C output**, not C/C++ hybrid
3. Comment preserves information for human readers
4. Implementation is **simple** and **correct**
5. Name mangling suppression is handled separately in `NameMangler`

Implementation:
- Detect `extern "C"` via `FunctionDecl::isExternC()`
- Generate C function with original (unmangled) name
- Optionally add `/* extern "C" */` comment for documentation
- No special handling needed (C linkage is default in C)

### 3.2 Calling Conventions - Analysis and Recommendation

**Option A: Preserve with Attributes**

Approach:
- Use GCC/Clang `__attribute__` syntax
- Preserve calling convention in generated C code

Example:

```cpp
// C++ input:
int __stdcall WindowProc(int msg, int wparam);

// Generated C output:
int __attribute__((stdcall)) WindowProc(int msg, int wparam);
```

Pros:
- Fully preserves calling convention semantics
- Generated code behaves identically to original
- Compiler enforces calling convention
- Critical for Windows API interop

Cons:
- Platform-specific (not all compilers support all conventions)
- Requires target compiler to support attributes
- May fail on non-x86 platforms

**Verdict**: ✅ **RECOMMENDED** for safety-critical transpiler

---

**Option B: Document in Comments**

Approach:
- Strip calling convention
- Add comment noting original convention

Example:

```cpp
// C++ input:
int __stdcall WindowProc(int msg, int wparam);

// Generated C output:
/* __stdcall */
int WindowProc(int msg, int wparam);
```

Pros:
- Portable across all compilers
- No attribute support needed
- Simple implementation

Cons:
- Loses calling convention semantics
- Generated code may have different ABI than original
- Function pointer compatibility issues
- Incorrect for Windows API calls

**Verdict**: ❌ Not viable for correctness-critical transpiler

---

**Option C: Runtime Mode Configuration**

Approach:
- User chooses mode via command-line flag
- Mode 1: Preserve with attributes
- Mode 2: Document with comments

Pros:
- Flexibility for different use cases
- Allows portable mode for non-x86 targets

Cons:
- Additional complexity
- User must understand implications
- Default mode unclear

**Verdict**: ⚠️ Viable but adds complexity

---

**RECOMMENDATION FOR CALLING CONVENTIONS:**

**Adopt Option A: Preserve with Attributes**

Rationale:
1. **Correctness**: Calling conventions affect ABI and must be preserved
2. **Safety-critical**: Transpiler targets safety-critical systems where ABI errors are unacceptable
3. **Windows API**: `__stdcall` is mandatory for Windows API functions
4. **Function pointers**: Calling convention must match for compatibility
5. **Compiler support**: GCC/Clang support `__attribute__((calling_conv))` syntax

Implementation:
- Detect calling convention via `FunctionDecl::getType()->getAs<FunctionType>()->getExtInfo().getCallConv()`
- Map `CallingConv` enum to `__attribute__` string
- Emit attribute in generated C function declaration
- Handle platform incompatibilities with warnings

Attribute Mapping:

```cpp
std::string CNodeBuilder::getCallingConvAttribute(CallingConv CC) {
    switch (CC) {
        case CC_C:
            return "";  // Default, no attribute needed
        case CC_X86StdCall:
            return "__attribute__((stdcall))";
        case CC_X86FastCall:
            return "__attribute__((fastcall))";
        case CC_X86ThisCall:
            return "__attribute__((thiscall))";
        case CC_X86Pascal:
            return "__attribute__((pascal))";
        case CC_X86VectorCall:
            return "__attribute__((vectorcall))";
        case CC_X86RegCall:
            return "__attribute__((regcall))";
        case CC_X86_64Win64:
            return "__attribute__((ms_abi))";
        case CC_X86_64SysV:
            return "__attribute__((sysv_abi))";
        case CC_AAPCS:
            return "__attribute__((pcs(\"aapcs\")))";
        case CC_AAPCS_VFP:
            return "__attribute__((pcs(\"aapcs-vfp\")))";
        default:
            // Emit warning for unknown/unsupported convention
            return "";
    }
}
```

Code Generation Example:

```cpp
FunctionDecl* CNodeBuilder::funcDecl(
    llvm::StringRef name,
    QualType retType,
    llvm::ArrayRef<ParmVarDecl*> params,
    Stmt* body,
    CallingConv callConv) {

    // Create function type with calling convention
    FunctionProtoType::ExtProtoInfo EPI;
    EPI.ExtInfo = EPI.ExtInfo.withCallingConv(callConv);

    llvm::SmallVector<QualType, 4> paramTypes;
    for (ParmVarDecl *P : params) {
        paramTypes.push_back(P->getType());
    }

    QualType funcType = Ctx.getFunctionType(retType, paramTypes, EPI);

    // Create function declaration
    IdentifierInfo &II = Ctx.Idents.get(name);
    DeclarationName DN(&II);

    FunctionDecl *FD = FunctionDecl::Create(
        Ctx,
        Ctx.getTranslationUnitDecl(),
        SourceLocation(),
        SourceLocation(),
        DN,
        funcType,
        Ctx.getTrivialTypeSourceInfo(funcType),
        SC_None
    );

    FD->setParams(params);
    if (body) {
        FD->setBody(body);
    }

    return FD;
}
```

---

## 4. Edge Cases and Special Handling

### 4.1 extern "C" Edge Cases

#### Edge Case 1: extern "C" Function Overloading (Illegal)

C does not support function overloading, so `extern "C"` functions cannot be overloaded.

```cpp
// ILLEGAL C++ code (compiler error):
extern "C" {
    void foo(int x);
    void foo(double x);  // ERROR: redefinition
}
```

**Compiler behavior**: Clang rejects this with error: "declaration of 'foo' has a different language linkage"

**Transpiler handling**:
- Clang will fail to parse this code
- No special handling needed (compilation fails before transpilation)

---

#### Edge Case 2: extern "C" with Namespaces

Functions with C linkage can be declared inside namespaces, but they have C linkage (no namespace mangling).

```cpp
namespace MyNamespace {
    extern "C" void foo();  // Has C linkage, NOT MyNamespace::foo
}

// Can be called as:
MyNamespace::foo();  // In C++ (qualified)
foo();               // In C (unqualified)
```

**AST structure**:
- FunctionDecl parent context: NamespaceDecl
- FunctionDecl language linkage: CLanguageLinkage
- Effective name: `foo` (unmangled)

**Transpiler handling**:
- `FunctionDecl::isExternC()` returns `true`
- Suppress namespace mangling
- Generate C function with name `foo` (not `MyNamespace_foo`)

```cpp
std::string NameMangler::mangleFunctionName(FunctionDecl *FD) {
    // Check extern "C" BEFORE checking namespaces
    if (FD->isExternC()) {
        return FD->getName().str();  // Return unmangled name
    }

    // Apply namespace mangling for C++ functions
    std::vector<std::string> namespaces = extractNamespaceHierarchy(FD);
    // ...
}
```

---

#### Edge Case 3: extern "C" with Templates (Partial Support)

Template declarations cannot have C linkage, but explicit template specializations can.

```cpp
// ILLEGAL:
extern "C" template<typename T>
void foo(T x);  // ERROR: templates cannot have C linkage

// LEGAL:
template<typename T> void foo(T x);  // C++ template

extern "C" void foo(int x);  // Legal: explicit specialization with C linkage
```

**Compiler behavior**: Clang rejects template with extern "C" linkage

**Transpiler handling**:
- Template declarations: Process normally (C++ linkage)
- Explicit specializations with extern "C": Suppress mangling
- No special template handling needed (templates already require manual instantiation)

---

#### Edge Case 4: extern "C" Static Functions

Static functions can have C linkage (internal linkage + C language linkage).

```cpp
extern "C" {
    static void helper() {  // Internal linkage, C language linkage
        // ...
    }
}
```

**AST structure**:
- FunctionDecl storage class: `SC_Static`
- FunctionDecl language linkage: `CLanguageLinkage`
- Linkage: `InternalLinkage`

**Transpiler handling**:
- Preserve `static` storage class
- Suppress name mangling (already no external linkage)
- Generate C static function

```cpp
bool CppToCVisitor::VisitFunctionDecl(clang::FunctionDecl *FD) {
    bool isStatic = (FD->getStorageClass() == SC_Static);
    bool isExternC = FD->isExternC();

    if (isStatic && isExternC) {
        // Static function with C linkage
        // Generate: static int helper(...) { ... }
    }

    return true;
}
```

---

#### Edge Case 5: Nested extern "C" and extern "C++" Blocks

Nested linkage specifications can restore C++ linkage inside extern "C" blocks.

```cpp
extern "C" {
    void c_func();  // C linkage

    extern "C++" {
        void cpp_func();  // C++ linkage (restored)
    }

    void c_func2();  // C linkage (restored)
}
```

**AST structure**:
- LinkageSpecDecl (lang_c)
  - FunctionDecl (c_func, C linkage)
  - LinkageSpecDecl (lang_cxx)
    - FunctionDecl (cpp_func, C++ linkage)
  - FunctionDecl (c_func2, C linkage)

**Transpiler handling**:
- Maintain linkage context stack
- Track current effective linkage

```cpp
class CppToCVisitor {
private:
    std::vector<LinkageSpecDecl::LanguageIDs> linkageStack;

public:
    bool VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS) {
        linkageStack.push_back(LS->getLanguage());
        return true;
    }

    LinkageSpecDecl::LanguageIDs getCurrentLinkage() const {
        if (linkageStack.empty()) {
            return LinkageSpecDecl::lang_cxx;  // Default C++
        }
        return linkageStack.back();
    }
};
```

---

### 4.2 Calling Convention Edge Cases

#### Edge Case 1: Calling Convention Conflicts (Function vs Function Pointer)

Function and function pointer must have matching calling conventions for compatibility.

```cpp
// C++ code:
void __stdcall func(int x);

typedef void (__cdecl *FuncPtr)(int);  // Different calling convention!

FuncPtr ptr = func;  // ERROR: incompatible types
```

**Compiler behavior**: Clang emits error: "cannot convert 'void (*)(int) __attribute__((stdcall))' to 'void (*)(int)' (different calling convention)"

**Transpiler handling**:
- Preserve calling conventions in both function and typedef
- Compiler will catch mismatches in generated C code
- No special validation needed in transpiler

---

#### Edge Case 2: Template Functions with Calling Conventions

Template functions can have explicit calling conventions, but specializations must match.

```cpp
template<typename T>
void __stdcall func(T x);  // Template with stdcall

template<>
void __stdcall func<int>(int x) {  // Specialization must match
    // ...
}
```

**Transpiler handling**:
- Manual template instantiation already required
- Preserve calling convention in instantiated function
- No special template handling needed

---

#### Edge Case 3: Virtual Functions with Calling Conventions

Virtual functions can have calling conventions, but all overrides must match.

```cpp
class Base {
public:
    virtual void __stdcall process(int x);
};

class Derived : public Base {
public:
    void __stdcall process(int x) override;  // Must match
};
```

**Compiler behavior**: Clang enforces matching calling conventions for virtual overrides

**Transpiler handling**:
- Virtual functions translated to function pointers in vtable
- Preserve calling convention in function pointer type
- Ensure all overrides have matching convention

```cpp
// Generated C code:
struct Base_vtable {
    void (__attribute__((stdcall)) *process)(struct Base* this, int x);
};
```

---

#### Edge Case 4: Platform Incompatibilities

Some calling conventions are x86-specific and invalid on other platforms.

```cpp
// Valid on x86, invalid on ARM:
void __stdcall func(int x);
```

**Compiler behavior**: Clang emits warning on non-x86 platforms: "'stdcall' calling convention is not supported on this target"

**Transpiler handling**:
- Detect target platform via Clang's target triple
- Emit warning for platform-incompatible conventions
- Strip unsupported convention and document in comment

```cpp
std::string CNodeBuilder::getCallingConvAttribute(CallingConv CC, const TargetInfo &Target) {
    // Check platform compatibility
    if (CC == CC_X86StdCall && !Target.getTriple().isX86()) {
        // Emit warning: stdcall not supported on this platform
        return "";  // Strip attribute
    }

    // ... map to attribute
}
```

---

#### Edge Case 5: Variadic Functions with Calling Conventions

Some calling conventions (e.g., stdcall, thiscall) are incompatible with variadic functions.

```cpp
// ILLEGAL:
void __stdcall printf_like(const char* fmt, ...);  // ERROR
```

**Compiler behavior**: Clang emits error: "variadic function cannot use 'stdcall' calling convention"

**Transpiler handling**:
- Clang rejects this during parsing
- No special handling needed (compilation fails before transpilation)

---

## 5. Testing Strategy

### 5.1 Test Case Outlines for extern "C"

#### Test 1: Simple extern "C" Function

**Input (C++):**
```cpp
extern "C" int add(int a, int b) {
    return a + b;
}
```

**Expected Output (C):**
```c
/* extern "C" */
int add(int a, int b) {
    return a + b;
}
```

**Assertions:**
- Function name is `add` (not mangled)
- Comment indicates original extern "C"
- No namespace prefix

---

#### Test 2: extern "C" Block with Multiple Functions

**Input (C++):**
```cpp
extern "C" {
    void init();
    void cleanup();
    int process(int x);
}
```

**Expected Output (C):**
```c
/* extern "C" block start */
void init();
void cleanup();
int process(int x);
/* extern "C" block end */
```

**Assertions:**
- All three functions have unmangled names
- Block comments indicate extern "C" scope

---

#### Test 3: extern "C" Forward Declaration + C++ Definition

**Input (C++):**
```cpp
extern "C" void foo(int x);  // Forward declaration

void foo(int x) {  // Definition (inherits C linkage)
    // ...
}
```

**Expected Output (C):**
```c
/* extern "C" */
void foo(int x);

/* extern "C" (inherited) */
void foo(int x) {
    // ...
}
```

**Assertions:**
- Both declaration and definition have unmangled name `foo`
- No duplicate mangling

---

#### Test 4: Mixed C/C++ Linkage in Same File

**Input (C++):**
```cpp
extern "C" {
    void c_func();
}

namespace NS {
    void cpp_func();
}
```

**Expected Output (C):**
```c
/* extern "C" */
void c_func();

/* namespace NS */
void NS_cpp_func();
```

**Assertions:**
- `c_func` is unmangled
- `cpp_func` is mangled as `NS_cpp_func`

---

#### Test 5: extern "C" with Namespaces

**Input (C++):**
```cpp
namespace MyNS {
    extern "C" void foo();
}
```

**Expected Output (C):**
```c
/* namespace MyNS */
/* extern "C" */
void foo();  // NOT MyNS_foo
```

**Assertions:**
- Function name is `foo` (namespace suppressed by extern "C")
- Comment indicates both namespace and extern "C"

---

#### Test 6: extern "C" Static Functions

**Input (C++):**
```cpp
extern "C" {
    static void helper() {
        // ...
    }
}
```

**Expected Output (C):**
```c
/* extern "C" */
static void helper() {
    // ...
}
```

**Assertions:**
- `static` storage class preserved
- Function name unmangled

---

### 5.2 Test Case Outlines for Calling Conventions

#### Test 1: Platform-Specific Calling Conventions (x86)

**Input (C++):**
```cpp
void __attribute__((cdecl)) func1(int x);
void __attribute__((stdcall)) func2(int x);
void __attribute__((fastcall)) func3(int x);
```

**Expected Output (C):**
```c
void __attribute__((cdecl)) func1(int x);
void __attribute__((stdcall)) func2(int x);
void __attribute__((fastcall)) func3(int x);
```

**Assertions:**
- All calling conventions preserved as attributes

---

#### Test 2: x86_64 ABI Conventions

**Input (C++):**
```cpp
void __attribute__((ms_abi)) win_func(int x);
void __attribute__((sysv_abi)) unix_func(int x);
```

**Expected Output (C):**
```c
void __attribute__((ms_abi)) win_func(int x);
void __attribute__((sysv_abi)) unix_func(int x);
```

**Assertions:**
- ABI attributes preserved for x86_64

---

#### Test 3: Function Pointers with Calling Conventions

**Input (C++):**
```cpp
typedef void (__stdcall *StdCallFuncPtr)(int);

void register_callback(StdCallFuncPtr callback);
```

**Expected Output (C):**
```c
typedef void (__attribute__((stdcall)) (*StdCallFuncPtr))(int);

void register_callback(StdCallFuncPtr callback);
```

**Assertions:**
- Function pointer type preserves calling convention
- Callback parameter type matches

---

#### Test 4: Member Functions with thiscall (Windows x86)

**Input (C++):**
```cpp
class Widget {
public:
    void process(int x);  // Implicit thiscall on Windows x86
};
```

**Expected Output (C):**
```c
struct Widget {
    // ...
};

/* thiscall (Windows x86) */
void Widget_process(struct Widget* this, int x);
```

**Assertions:**
- Comment indicates thiscall (converted to explicit `this` parameter in C)
- Platform-conditional test (Windows x86 only)

---

#### Test 5: ARM Calling Conventions

**Input (C++):**
```cpp
void __attribute__((pcs("aapcs"))) arm_func(int x);
void __attribute__((pcs("aapcs-vfp"))) arm_vfp_func(float x);
```

**Expected Output (C):**
```c
void __attribute__((pcs("aapcs"))) arm_func(int x);
void __attribute__((pcs("aapcs-vfp"))) arm_vfp_func(float x);
```

**Assertions:**
- ARM-specific conventions preserved
- Platform-conditional test (ARM only)

---

#### Test 6: Platform Incompatibility Warning

**Input (C++):**
```cpp
// Compiled for ARM target
void __attribute__((stdcall)) func(int x);  // Invalid on ARM
```

**Expected Behavior:**
- Emit warning: "stdcall not supported on ARM"
- Strip attribute from generated code
- Add comment documenting original convention

**Expected Output (C):**
```c
/* Original: __attribute__((stdcall)) - UNSUPPORTED ON THIS PLATFORM */
void func(int x);
```

---

### 5.3 Integration Tests

#### Integration Test 1: extern "C" + Calling Convention

**Input (C++):**
```cpp
extern "C" void __stdcall WindowProc(int msg, int wparam);
```

**Expected Output (C):**
```c
/* extern "C" */
void __attribute__((stdcall)) WindowProc(int msg, int wparam);
```

**Assertions:**
- Both extern "C" and calling convention handled correctly
- Name unmangled
- Calling convention preserved

---

#### Integration Test 2: Namespace + extern "C" + Calling Convention

**Input (C++):**
```cpp
namespace Win32 {
    extern "C" void __stdcall MessageBox(const char* text);
}
```

**Expected Output (C):**
```c
/* namespace Win32 */
/* extern "C" */
void __attribute__((stdcall)) MessageBox(const char* text);
```

**Assertions:**
- Namespace suppressed by extern "C"
- Calling convention preserved
- Name is `MessageBox` (not `Win32_MessageBox`)

---

## 6. Implementation Dependencies

### 6.1 Required Changes to CppToCVisitor

**Add VisitLinkageSpecDecl() Visitor:**

```cpp
// File: include/CppToCVisitor.h
class CppToCVisitor : public clang::RecursiveASTVisitor<CppToCVisitor> {
public:
    // ... existing methods ...

    /// Visit linkage specification (extern "C" { }) blocks
    /// @param LS The LinkageSpecDecl AST node
    /// @return true to continue visiting children
    bool VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS);

private:
    // Track linkage context stack for nested extern "C" blocks
    std::vector<clang::LinkageSpecDecl::LanguageIDs> linkageStack;
};
```

**Extend VisitFunctionDecl() to Query Linkage:**

```cpp
// File: src/CppToCVisitor.cpp
bool CppToCVisitor::VisitFunctionDecl(clang::FunctionDecl *FD) {
    // Skip forward declarations
    if (!FD->isThisDeclarationADefinition()) {
        return true;
    }

    // Query language linkage
    bool isExternC = FD->isExternC();
    LanguageLinkage linkage = FD->getLanguageLinkage();

    // Query calling convention
    const FunctionType *FT = FD->getType()->getAs<FunctionType>();
    CallingConv callConv = FT ? FT->getExtInfo().getCallConv() : CC_C;

    // Determine function name (mangled or unmangled)
    std::string funcName;
    if (isExternC) {
        funcName = FD->getName().str();  // Unmangled
    } else {
        funcName = Mangler.mangleFunctionName(FD);  // Mangled
    }

    // Generate C function declaration
    // ... pass callConv to Builder.funcDecl()

    return true;
}
```

---

### 6.2 Required Changes to CNodeBuilder

**Extend funcDecl() to Accept Calling Convention:**

```cpp
// File: include/CNodeBuilder.h
class CNodeBuilder {
public:
    /// Create C function declaration with calling convention
    /// @param name Function name
    /// @param retType Return type
    /// @param params Parameter list
    /// @param body Function body (optional)
    /// @param callConv Calling convention (default: CC_C)
    /// @return Created FunctionDecl
    FunctionDecl* funcDecl(
        llvm::StringRef name,
        QualType retType,
        llvm::ArrayRef<ParmVarDecl*> params,
        Stmt* body = nullptr,
        clang::CallingConv callConv = clang::CC_C
    );

    /// Map CallingConv enum to attribute string
    /// @param CC Calling convention enum value
    /// @return GCC/Clang attribute string (e.g., "__attribute__((stdcall))")
    std::string getCallingConvAttribute(clang::CallingConv CC) const;
};
```

**Implementation:**

```cpp
// File: src/CNodeBuilder.cpp (add to existing funcDecl implementation)
FunctionDecl* CNodeBuilder::funcDecl(
    llvm::StringRef name,
    QualType retType,
    llvm::ArrayRef<ParmVarDecl*> params,
    Stmt* body,
    clang::CallingConv callConv) {

    // Create function type with calling convention
    FunctionProtoType::ExtProtoInfo EPI;
    EPI.ExtInfo = EPI.ExtInfo.withCallingConv(callConv);

    llvm::SmallVector<QualType, 4> paramTypes;
    for (ParmVarDecl *P : params) {
        paramTypes.push_back(P->getType());
    }

    QualType funcType = Ctx.getFunctionType(retType, paramTypes, EPI);

    // Rest of implementation...
    IdentifierInfo &II = Ctx.Idents.get(name);
    DeclarationName DN(&II);

    FunctionDecl *FD = FunctionDecl::Create(
        Ctx,
        Ctx.getTranslationUnitDecl(),
        SourceLocation(),
        SourceLocation(),
        DN,
        funcType,
        Ctx.getTrivialTypeSourceInfo(funcType),
        SC_None
    );

    FD->setParams(params);
    if (body) {
        FD->setBody(body);
    }

    return FD;
}

std::string CNodeBuilder::getCallingConvAttribute(clang::CallingConv CC) const {
    switch (CC) {
        case CC_C:
            return "";  // Default, no attribute needed
        case CC_X86StdCall:
            return "__attribute__((stdcall))";
        case CC_X86FastCall:
            return "__attribute__((fastcall))";
        case CC_X86ThisCall:
            return "__attribute__((thiscall))";
        case CC_X86Pascal:
            return "__attribute__((pascal))";
        case CC_X86VectorCall:
            return "__attribute__((vectorcall))";
        case CC_X86RegCall:
            return "__attribute__((regcall))";
        case CC_X86_64Win64:
            return "__attribute__((ms_abi))";
        case CC_X86_64SysV:
            return "__attribute__((sysv_abi))";
        case CC_AAPCS:
            return "__attribute__((pcs(\"aapcs\")))";
        case CC_AAPCS_VFP:
            return "__attribute__((pcs(\"aapcs-vfp\")))";
        default:
            return "";  // Unknown convention
    }
}
```

---

### 6.3 Required Changes to NameMangler

**Suppress Mangling for extern "C" Functions:**

```cpp
// File: src/NameMangler.cpp
std::string NameMangler::mangleFunctionName(FunctionDecl *FD) {
    // Check for extern "C" linkage BEFORE any mangling
    if (FD->isExternC()) {
        return FD->getName().str();  // Return unmangled name
    }

    // Existing namespace-aware mangling for C++ functions
    std::vector<std::string> namespaces = extractNamespaceHierarchy(FD);
    std::string mangledName;
    for (const auto &ns : namespaces) {
        mangledName += ns + "_";
    }
    mangledName += FD->getName().str();

    return mangledName;
}

// Similar changes for mangleMethodName() and mangleClassName()
```

---

### 6.4 Test Files to Add

Create test suite for extern "C" and calling conventions:

**Test File Structure:**

```
tests/
├── ExternCBasicTest.cpp           # Simple extern "C" functions
├── ExternCBlockTest.cpp           # extern "C" { } blocks
├── ExternCNamespaceTest.cpp       # extern "C" with namespaces
├── ExternCStaticTest.cpp          # static extern "C" functions
├── CallingConvTest.cpp            # Calling conventions (x86, x64, ARM)
├── CallingConvFuncPtrTest.cpp     # Function pointers with calling conventions
├── ExternCCallConvTest.cpp        # Combined extern "C" + calling convention
└── PlatformCallingConvTest.cpp    # Platform-specific convention tests
```

**Test Harness Updates:**

Add new test categories to test runner:

```cpp
// File: tests/main.cpp
int main() {
    // ... existing tests ...

    // Linkage and calling convention tests
    RUN_TEST_SUITE(ExternCBasicTest);
    RUN_TEST_SUITE(ExternCBlockTest);
    RUN_TEST_SUITE(CallingConvTest);
    RUN_TEST_SUITE(PlatformCallingConvTest);

    return 0;
}
```

---

### 6.5 Documentation Updates

**Add to docs/FAQ.md:**

```markdown
### Q: How does the transpiler handle extern "C" functions?

A: Functions with `extern "C"` linkage are detected via `FunctionDecl::isExternC()`.
The transpiler:
1. Suppresses C++ name mangling (preserves original function name)
2. Strips the `extern "C"` declaration (redundant in pure C)
3. Optionally adds a `/* extern "C" */` comment for documentation

Example:
```cpp
// C++ input:
extern "C" int add(int a, int b);

// Generated C output:
/* extern "C" */
int add(int a, int b);
```

### Q: Are calling conventions preserved in the generated C code?

A: Yes. The transpiler detects calling conventions via `FunctionDecl::getCallConv()`
and preserves them using GCC/Clang `__attribute__` syntax.

Example:
```cpp
// C++ input:
void __stdcall WindowProc(int msg);

// Generated C output:
void __attribute__((stdcall)) WindowProc(int msg);
```

Supported calling conventions:
- x86: cdecl, stdcall, fastcall, thiscall, pascal, vectorcall, regcall
- x86_64: ms_abi (Windows), sysv_abi (Unix/Linux)
- ARM: pcs("aapcs"), pcs("aapcs-vfp")

Platform-incompatible conventions (e.g., stdcall on ARM) emit a warning
and are stripped from the generated code.
```

**Add to docs/SAFETY_CRITICAL_GUIDE.md:**

```markdown
### Calling Convention Preservation

**Critical for safety**: Calling conventions affect the Application Binary
Interface (ABI) and must be preserved exactly in generated C code.

**Why it matters**:
1. **Windows API**: `__stdcall` is mandatory for Win32 API functions
2. **Function pointers**: Calling convention must match for compatibility
3. **Interrupt handlers**: May require specific conventions (e.g., ARM interrupt)
4. **Third-party libraries**: Pre-compiled libraries expect specific conventions

**Transpiler guarantee**: All calling conventions are preserved using
`__attribute__` syntax supported by GCC/Clang.

**Verification**: Test suite includes platform-specific tests for x86, x64,
and ARM calling conventions.
```

---

## 7. Platform Considerations

### 7.1 x86 (32-bit) Calling Conventions

**Stack Management:**

| Convention | Argument Order | Stack Cleanup | Use Case |
|------------|---------------|---------------|----------|
| **cdecl** | Right-to-left | Caller | Default C, variadic functions |
| **stdcall** | Right-to-left | Callee | Win32 API |
| **fastcall** | First 2 in ECX/EDX, rest on stack | Callee | Performance-critical code |
| **thiscall** | `this` in ECX, rest on stack | Callee | C++ member functions (MSVC) |
| **pascal** | Left-to-right | Callee | Legacy Pascal compatibility |

**Key Differences:**

- **cdecl**: Caller cleans stack → supports variadic functions (e.g., `printf`)
- **stdcall**: Callee cleans stack → function name mangled with `@` + byte count (e.g., `_foo@8`)
- **fastcall**: First 2 args in registers (ECX, EDX) → faster calls, less stack usage
- **thiscall**: `this` pointer in ECX → Microsoft-specific for C++ member functions

**Compatibility:**

- **GCC/Clang** use cdecl for member functions (thiscall is MSVC-specific)
- **64-bit**: All conventions collapse to single x64 calling convention

**Transpiler Handling:**

```cpp
std::string getCallingConvAttribute_x86(CallingConv CC) {
    switch (CC) {
        case CC_C:           return "";  // Default
        case CC_X86StdCall:  return "__attribute__((stdcall))";
        case CC_X86FastCall: return "__attribute__((fastcall))";
        case CC_X86ThisCall: return "__attribute__((thiscall))";  // MSVC only
        case CC_X86Pascal:   return "__attribute__((pascal))";
        default:             return "";
    }
}
```

### 7.2 x86_64 (64-bit) Calling Conventions

**Two Primary ABIs:**

| ABI | Platform | Register Usage (Integer Args) | Register Usage (FP Args) | Used By |
|-----|----------|-------------------------------|-------------------------|---------|
| **System V AMD64 ABI** | Linux, macOS, Unix | RDI, RSI, RDX, RCX, R8, R9 | XMM0-XMM7 | GCC, Clang (Linux/Mac) |
| **Microsoft x64 ABI** | Windows | RCX, RDX, R8, R9 | XMM0-XMM3 | MSVC, Clang (Windows) |

**Key Differences:**

| Feature | System V ABI | Microsoft x64 ABI |
|---------|-------------|------------------|
| Integer arg regs | RDI, RSI, RDX, RCX, R8, R9 | RCX, RDX, R8, R9 |
| FP arg regs | XMM0-XMM7 | XMM0-XMM3 |
| Shadow space | No | Yes (32 bytes) |
| Callee-saved XMM | None | XMM6-XMM15 |
| Stack alignment | 16-byte (before call) | 16-byte (after call) |

**Calling Convention Attributes:**

- `__attribute__((ms_abi))` - Force Microsoft x64 ABI
- `__attribute__((sysv_abi))` - Force System V ABI

**Cross-Platform Compatibility:**

On 64-bit platforms, most x86 conventions (stdcall, fastcall) are **ignored** and collapsed to the default x64 convention.

```cpp
// On x86_64, these are equivalent:
void func(int x);                           // Uses x64 default
void __attribute__((stdcall)) func(int x);  // IGNORED, uses x64 default
```

**Transpiler Handling:**

```cpp
std::string getCallingConvAttribute_x64(CallingConv CC, const TargetInfo &Target) {
    // On x64, only ms_abi vs sysv_abi matter
    if (CC == CC_X86_64Win64) {
        return "__attribute__((ms_abi))";
    } else if (CC == CC_X86_64SysV) {
        return "__attribute__((sysv_abi))";
    } else if (CC == CC_X86StdCall || CC == CC_X86FastCall) {
        // Emit warning: ignored on x64
        return "";  // Strip attribute
    }
    return "";
}
```

### 7.3 ARM Calling Conventions

**ARM Procedure Call Standard (AAPCS):**

| Convention | Register Usage | Use Case |
|------------|---------------|----------|
| **AAPCS** | R0-R3 for args, R0-R1 for return | Standard ARM calls |
| **AAPCS-VFP** | S0-S15/D0-D7 for FP args | ARM with VFP (floating point) |
| **AArch64 Vector PCS** | V0-V7 for vector args | SIMD/NEON code |

**Attributes:**

- `__attribute__((pcs("aapcs")))`
- `__attribute__((pcs("aapcs-vfp")))`
- `__attribute__((aarch64_vector_pcs))`

**Transpiler Handling:**

```cpp
std::string getCallingConvAttribute_ARM(CallingConv CC) {
    switch (CC) {
        case CC_AAPCS:
            return "__attribute__((pcs(\"aapcs\")))";
        case CC_AAPCS_VFP:
            return "__attribute__((pcs(\"aapcs-vfp\")))";
        case CC_AArch64VectorCall:
            return "__attribute__((aarch64_vector_pcs))";
        default:
            return "";
    }
}
```

### 7.4 Cross-Platform Strategy

**Target Detection:**

```cpp
class CNodeBuilder {
private:
    const clang::TargetInfo &Target;

public:
    std::string getCallingConvAttribute(CallingConv CC) const {
        const llvm::Triple &T = Target.getTriple();

        if (T.isX86() && T.isArch32Bit()) {
            return getCallingConvAttribute_x86(CC);
        } else if (T.isX86() && T.isArch64Bit()) {
            return getCallingConvAttribute_x64(CC, Target);
        } else if (T.isARM() || T.isAArch64()) {
            return getCallingConvAttribute_ARM(CC);
        } else {
            // Unknown platform - emit warning
            return "";
        }
    }
};
```

**Fallback Handling:**

For unsupported calling conventions on a target platform:

1. **Emit warning**: "Calling convention 'stdcall' not supported on ARM"
2. **Strip attribute**: Remove from generated code
3. **Document**: Add comment `/* Original: __stdcall - UNSUPPORTED */`

**Platform-Specific Tests:**

```cpp
// tests/PlatformCallingConvTest.cpp
#ifdef __x86_64__
TEST(CallingConvTest, X64_StdcallIgnored) {
    // Verify stdcall is ignored on x64
}
#endif

#ifdef __arm__
TEST(CallingConvTest, ARM_AAPCS) {
    // Verify AAPCS attribute preserved
}
#endif
```

---

## Summary and Recommendations

### Key Recommendations

1. **extern "C" Handling**: **Strip and Note** approach
   - Remove `extern "C"` (redundant in pure C)
   - Suppress name mangling via `NameMangler`
   - Optionally add `/* extern "C" */` comment

2. **Calling Convention Handling**: **Preserve with Attributes**
   - Detect via `FunctionDecl::getCallConv()`
   - Preserve using `__attribute__` syntax
   - Emit warnings for platform-incompatible conventions

3. **Implementation Priority**:
   1. Add `VisitLinkageSpecDecl()` to `CppToCVisitor`
   2. Extend `VisitFunctionDecl()` to query linkage and calling convention
   3. Modify `NameMangler::mangleFunctionName()` to check `isExternC()`
   4. Extend `CNodeBuilder::funcDecl()` to accept calling convention parameter
   5. Add comprehensive test suite

4. **Testing Focus**:
   - Unit tests for linkage detection
   - Integration tests combining extern "C" + calling conventions
   - Platform-specific tests (x86, x64, ARM)
   - Edge case tests (namespaces, function pointers, virtual functions)

5. **Documentation**:
   - Update FAQ with extern "C" and calling convention handling
   - Add safety-critical guidance on ABI preservation
   - Document platform-specific behavior

### Next Steps

Proceed to **Stage 2: Planning** to design detailed implementation architecture, API signatures, and TDD test plan.

---

## References

### Clang Documentation

- [LinkageSpecDecl Class Reference](https://clang.llvm.org/doxygen/classclang_1_1LinkageSpecDecl.html)
- [FunctionDecl Class Reference](https://clang.llvm.org/doxygen/classclang_1_1FunctionDecl.html)
- [Linkage.h File Reference](https://clang.llvm.org/doxygen/include_2clang_2Basic_2Linkage_8h.html)
- [FunctionType::ExtInfo Class Reference](https://clang.llvm.org/doxygen/classclang_1_1FunctionType_1_1ExtInfo.html)
- [Introduction to the Clang AST](https://clang.llvm.org/docs/IntroductionToTheClangAST.html)

### LLVM Documentation

- [CallingConv Namespace Reference](https://llvm.org/doxygen/namespacellvm_1_1CallingConv.html)
- [CallingConv.h Source File](https://llvm.org/doxygen/CallingConv_8h_source.html)

### Calling Convention References

- [x86 calling conventions - Wikipedia](https://en.wikipedia.org/wiki/X86_calling_conventions)
- [x86 Disassembly/Calling Conventions - Wikibooks](https://en.wikibooks.org/wiki/X86_Disassembly/Calling_Conventions)
- [Calling Conventions in C/C++ - GeeksforGeeks](https://www.geeksforgeeks.org/cpp/calling-conventions-in-c-cpp/)
- [x64 ABI conventions - Microsoft Learn](https://learn.microsoft.com/en-us/cpp/build/x64-software-conventions?view=msvc-170)
- [x64 Calling Convention - Microsoft Learn](https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention?view=msvc-170)
- [Calling conventions for different C++ compilers (PDF)](https://www.agner.org/optimize/calling_conventions.pdf)

### C++ Language References

- [C++ extern C Linkage Explained - sqlpey](https://sqlpey.com/c++/cplusplus-extern-c-linkage/)
- [Deconstructing function pointers in C++ - Old New Thing](https://devblogs.microsoft.com/oldnewthing/20200717-00/?p=103989)

### Clang Test Files

- [clang/test/Sema/callingconv.c](https://github.com/llvm-mirror/clang/blob/master/test/Sema/callingconv.c)

---

**Document Status**: ✅ Complete
**Next Stage**: Stage 2 - Planning (Implementation Architecture Design)
**Author**: Claude Sonnet 4.5 (AI Research Assistant)
**Date**: 2025-12-18

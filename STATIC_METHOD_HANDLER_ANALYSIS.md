# Static Method Handler: Architecture Analysis and Design Recommendations

## Executive Summary

Based on analysis of existing dispatcher-pattern handlers (FunctionHandler, RecordHandler, NamespaceHandler), this document provides comprehensive guidance for implementing a StaticMethodHandler within the dispatcher architecture.

**Key Finding:** The existing MethodHandler (in `include/handlers/MethodHandler.h`) already supports static methods via `isStatic()` check, but it exists in the old handler framework. A new StaticMethodHandler is needed in the dispatcher pattern for consistency.

---

## 1. Existing Handler Pattern Analysis

### 1.1 Dispatcher Architecture Overview

The CppToCVisitorDispatcher implements **Chain of Responsibility** pattern:

```
Dispatcher.dispatch(D) → Handlers evaluated sequentially
                      → First handler.canHandle(D) == true handles D
                      → Handler.handle() processes D
                      → Optional recursive dispatch for children
```

**Key Components:**

```cpp
class CppToCVisitorDispatcher {
    // Handler registration (predicates + visitors)
    void addHandler(DeclPredicate, DeclVisitor);

    // Dispatch routing
    bool dispatch(cppCtx, cCtx, D);  // Routes to matching handler

    // Access to mappers (for handlers to retrieve/store mappings)
    PathMapper& getPathMapper();
    DeclMapper& getDeclMapper();
    TypeMapper& getTypeMapper();
};

// Handler registration pattern
void SomeHandler::registerWith(CppToCVisitorDispatcher& disp) {
    disp.addHandler(&SomeHandler::canHandle, &SomeHandler::handleXXX);
}
```

### 1.2 Handler Pattern: canHandle() Predicate

All handlers follow **exact type matching** using `D->getKind()`:

**FunctionHandler Pattern:**
```cpp
bool FunctionHandler::canHandle(const clang::Decl* D) {
    // Step 1: Exact type match
    if (D->getKind() != clang::Decl::Function) {
        return false;
    }
    // Step 2: Double-check to exclude derived types
    const auto* FD = llvm::cast<clang::FunctionDecl>(D);
    return !llvm::isa<clang::CXXMethodDecl>(FD);  // Exclude methods
}
```

**RecordHandler Pattern:**
```cpp
bool RecordHandler::canHandle(const clang::Decl* D) {
    // Accept two exact kinds
    return D->getKind() == clang::Decl::Record ||
           D->getKind() == clang::Decl::CXXRecord;
}
```

**NamespaceHandler Pattern:**
```cpp
bool NamespaceHandler::canHandle(const clang::Decl* D) {
    return D->getKind() == clang::Decl::Namespace;
}
```

**Critical Principle:**
- Use `D->getKind()` for exact type matching (NOT `isa<>`)
- isa<> matches derived types (CXXMethodDecl isa FunctionDecl)
- getKind() gives exact compile-time kind

### 1.3 Handler Pattern: handleXXX() Visitor

All handlers follow **consistent structure**:

```cpp
static void handleFunction(
    const CppToCVisitorDispatcher& disp,     // For recursive dispatch
    const clang::ASTContext& cppASTContext,  // Source (read-only)
    clang::ASTContext& cASTContext,          // Target (write)
    const clang::Decl* D                     // Node to handle
) {
    // 1. Assertions for safety
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::Function && "Must be FunctionDecl");

    // 2. Cast and check
    const auto* func = llvm::cast<clang::FunctionDecl>(D);
    if (llvm::isa<clang::CXXMethodDecl>(func)) {
        llvm::errs() << "Unexpected method - should be filtered\n";
        return;
    }

    // 3. Extract properties
    std::string name = func->getNameAsString();

    // 4. Check parent context (namespace, class, etc.)
    if (const auto* nsDecl = llvm::dyn_cast<clang::NamespaceDecl>(func->getDeclContext())) {
        std::string nsPrefix = NamespaceHandler::getNamespacePath(nsDecl);
        if (!nsPrefix.empty()) {
            name = nsPrefix + "_" + name;  // Single underscore for namespace
        }
    }

    // 5. Translate properties (return type, parameters)
    clang::QualType cReturnType = ...;  // TypeMapper
    std::vector<clang::ParmVarDecl*> cParams = ...;  // ParameterHandler

    // 6. Create C AST node
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(...);

    // 7. Get target path and C TranslationUnit
    std::string targetPath = disp.getTargetPath(cppASTContext, D);
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);

    // 8. Add to C TranslationUnit
    cFunc->setDeclContext(cTU);
    cTU->addDecl(cFunc);

    // 9. Register location
    pathMapper.setNodeLocation(cFunc, targetPath);

    // 10. Debug output
    llvm::outs() << "[FunctionHandler] Translated: " << name << " → " << targetPath << "\n";
}
```

---

## 2. Parent Context Analysis for Static Methods

### 2.1 Determining Parent Context

Every declaration has a `DeclContext`:
- Global scope → `TranslationUnitDecl`
- Namespace → `NamespaceDecl`
- Class/Struct → `RecordDecl` or `CXXRecordDecl`
- Function → `FunctionDecl`

**Pattern for checking parent:**
```cpp
const clang::DeclContext* DC = D->getDeclContext();

// Check if parent is namespace
if (const auto* nsDecl = llvm::dyn_cast<clang::NamespaceDecl>(DC)) {
    // Apply namespace prefix
}

// Check if parent is class
if (const auto* classDecl = llvm::dyn_cast<clang::CXXRecordDecl>(DC)) {
    // Apply class name prefix
}

// Check if parent is struct
if (const auto* recordDecl = llvm::dyn_cast<clang::RecordDecl>(DC)) {
    // Handle struct context (rare at top level)
}
```

### 2.2 Static Method Context

**CXXMethodDecl characteristics:**
```cpp
const auto* method = llvm::cast<clang::CXXMethodDecl>(D);

// Check if static
bool isStatic = method->isStatic();

// Get parent class
const auto* classDecl = method->getParent();  // Always CXXRecordDecl

// Check if class is in namespace
const clang::DeclContext* parentContext = classDecl->getDeclContext();
if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(parentContext)) {
    // Class is in namespace
}
```

**Key Insight:** Static methods always have:
- Parent = CXXRecordDecl (the class)
- No 'this' parameter in C translation
- Class name prefix in C function name

---

## 3. Name Mangling Strategy

### 3.1 Separator Convention Analysis

Existing handlers use **different separators** for different purposes:

| Context | Separator | Pattern | Example |
|---------|-----------|---------|---------|
| Namespace + Function | `_` (single) | `Namespace_funcName` | `myns_getValue()` |
| Namespace + Class | `__` (double) | `Namespace__ClassName` | `myns__Counter` |
| Nested Struct | `__` (double) | `Outer__Inner` | `Outer__Inner` |
| Method | `_` (single) | `ClassName__methodName` | `Counter__increment()` |

**Rationale:**
- `_` (single): Separates function/method name from class/namespace
- `__` (double): Separates scope levels (namespace → class)

### 3.2 Static Method Naming

**Pattern for static methods:**
```
ClassName_staticMethodName

Example:
- Class: GameState, Method: getInstance
- Result: GameState_getInstance()
```

**Pattern with namespace:**
```
Namespace__ClassName_staticMethodName

Example:
- Namespace: engine, Class: Renderer, Method: initialize
- Result: engine__Renderer_initialize()
```

**Implementation:**
```cpp
std::string StaticMethodHandler::mangleStaticMethodName(
    const clang::CXXMethodDecl* method,
    const clang::CXXRecordDecl* classDecl
) {
    // Step 1: Get class name
    std::string className = classDecl->getNameAsString();

    // Step 2: Check if class is in namespace
    std::string prefix;
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(classDecl->getDeclContext())) {
        prefix = NamespaceHandler::getNamespacePath(ns);
        if (!prefix.empty()) {
            className = prefix + "__" + className;
        }
    }

    // Step 3: Get method name
    std::string methodName = method->getNameAsString();

    // Step 4: Combine: ClassName__methodName
    return className + "_" + methodName;
}
```

### 3.3 Avoiding Collisions

**Potential collision:** If both these exist:
```cpp
namespace foo {
    class bar_baz { static void qux(); };  // → foo__bar_baz_qux
    class bar { static void baz_qux(); };  // → foo__bar_baz_qux (COLLISION!)
}
```

**Mitigation:**
- Use consistent naming conventions (linters)
- Document the rule in code comments
- This is acceptable as it mirrors C++'s namespace isolation

---

## 4. Registration Order and Dependencies

### 4.1 Handler Registration Sequence

**Critical ordering principle:**
Handlers that depend on previous handlers must register AFTER them.

**Recommended sequence:**
```cpp
// Phase: Type System (prerequisites)
TypeHandler::registerWith(dispatcher);              // Phase 1: Core types
NamespaceHandler::registerWith(dispatcher);         // Phase 2: Scope tracking

// Phase: Declaration Translation (depends on types)
ParameterHandler::registerWith(dispatcher);         // Phase 3: Parameter types
FunctionHandler::registerWith(dispatcher);          // Phase 4: Free functions
RecordHandler::registerWith(dispatcher);            // Phase 5: Struct/class + fields
MethodHandler::registerWith(dispatcher);            // Phase 6: Instance methods
StaticMethodHandler::registerWith(dispatcher);      // Phase 7: Static methods
```

**Why this order?**
1. **TypeHandler first**: All other handlers need type translation
2. **NamespaceHandler second**: FunctionHandler/RecordHandler need namespace paths
3. **ParameterHandler**: FunctionHandler needs it for parameter translation
4. **FunctionHandler before RecordHandler**: Potential forward references
5. **MethodHandler/StaticMethodHandler at end**: Depend on class definitions

### 4.2 StaticMethodHandler Registration

**Place StaticMethodHandler AFTER or WITH MethodHandler:**

Option A (Same registration):
```cpp
// In CppToCVisitor or main initialization
MethodHandler::registerWith(dispatcher);           // Handles instance methods
StaticMethodHandler::registerWith(dispatcher);     // Handles static methods
```

Option B (Merged into MethodHandler):
```cpp
// Modify MethodHandler::canHandle to accept both static and instance
// Dispatch to different internal paths based on isStatic()
```

**Recommendation: Option A (Separate handlers)**
- Follows Single Responsibility Principle
- Each handler has clear focus
- Easier to understand and test
- Easier to modify one without affecting the other

---

## 5. Predicate Design for StaticMethodHandler

### 5.1 canHandle() Implementation

```cpp
bool StaticMethodHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Step 1: Check exact type - ONLY CXXMethodDecl
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    // Step 2: Ensure it's not a constructor or destructor
    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // Step 3: Check if static
    return method->isStatic();
}
```

**Key Points:**
- Use `getKind() == clang::Decl::CXXMethod` (not isa<>)
- Exclude constructors/destructors (have separate handlers)
- Use `isStatic()` to distinguish from instance methods

### 5.2 Interaction with MethodHandler

**MethodHandler filter:**
```cpp
bool MethodHandler::canHandle(const clang::Decl* D) {
    const auto* method = llvm::dyn_cast<clang::CXXMethodDecl>(D);
    if (!method) return false;

    // Exclude constructors and destructors
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // CRITICAL: Exclude static methods!
    return !method->isStatic();  // Instance methods only
}
```

**Result:**
- MethodHandler: Instance methods only
- StaticMethodHandler: Static methods only
- No overlap, no conflicts

---

## 6. Complete StaticMethodHandler Structure

### 6.1 Header File Pattern

```cpp
/**
 * @file StaticMethodHandler.h
 * @brief Handler for translating C++ static methods to C functions
 *
 * Registers with CppToCVisitorDispatcher to handle static method declarations.
 * Translates C++ static methods to regular C functions WITHOUT 'this' parameter.
 *
 * Static Method Translation:
 * C++: class Counter { static int getVersion() { return 1; } };
 * C:   int Counter__getVersion(void) { return 1; }
 *
 * With Namespace:
 * C++: namespace engine { class Renderer { static void init(); } }
 * C:   void engine__Renderer_init(void);
 *
 * Scope:
 * - CXXMethodDecl with isStatic() == true
 * - No 'this' parameter (unlike instance methods)
 * - Name mangling: Namespace__ClassName__methodName
 * - Parameter translation (like regular methods)
 * - Return type translation
 *
 * Future:
 * - Body translation (currently placeholder)
 * - Operator overloading
 * - Complex overload resolution
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/DeclCXX.h"
#include <string>
#include <vector>

namespace cpptoc {

class StaticMethodHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is static CXXMethodDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is CXXMethodDecl with isStatic() == true
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ static method to C function
     * @param disp Dispatcher for accessing PathMapper, DeclMapper, TypeMapper
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D CXXMethodDecl to process (must be static)
     *
     * Algorithm:
     * 1. Extract class name and method name
     * 2. Check if class is in namespace, apply namespace prefix
     * 3. Mangle static method name (ClassName__methodName or Namespace__ClassName__methodName)
     * 4. Translate return type (via TypeMapper)
     * 5. Translate parameters (via ParameterHandler)
     * 6. Create C FunctionDecl WITHOUT 'this' parameter
     * 7. Translate method body (placeholder in Phase 1)
     * 8. Get target path and C TranslationUnit
     * 9. Add C function to C TranslationUnit
     * 10. Register location in PathMapper
     */
    static void handleStaticMethod(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Mangle static method name with namespace and class name
     * @param classDecl Class containing the method
     * @param methodName Method name
     * @param disp Dispatcher for namespace path lookup
     * @param cppASTContext C++ ASTContext
     * @return Mangled name (ClassName__methodName or Namespace__ClassName__methodName)
     */
    static std::string mangleStaticMethodName(
        const clang::CXXRecordDecl* classDecl,
        const std::string& methodName,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext
    );

    /**
     * @brief Get the class name for a static method
     * @param method C++ static method declaration
     * @return Class name as string
     */
    static std::string getClassName(const clang::CXXMethodDecl* method);

    /**
     * @brief Translate static method parameters to C parameters
     * @param method C++ static method declaration
     * @param disp Dispatcher for parameter translation
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @return Vector of C parameter declarations
     */
    static std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::CXXMethodDecl* method,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
```

### 6.2 Implementation File Pattern

```cpp
/**
 * @file StaticMethodHandler.cpp
 * @brief Implementation of StaticMethodHandler
 *
 * Translates C++ static methods to C functions (no 'this' parameter).
 * Handles namespace prefixes and class name mangling.
 */

#include "dispatch/StaticMethodHandler.h"
#include "dispatch/NamespaceHandler.h"
#include "dispatch/ParameterHandler.h"
#include "CNodeBuilder.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/StmtMapper.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void StaticMethodHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &StaticMethodHandler::canHandle,
        &StaticMethodHandler::handleStaticMethod
    );
}

bool StaticMethodHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // CRITICAL: Use getKind() for exact type matching
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);

    // Exclude constructors and destructors
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // CRITICAL: Check for static methods ONLY
    return method->isStatic();
}

void StaticMethodHandler::handleStaticMethod(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::CXXMethod && "Must be CXXMethodDecl");

    const auto* cppMethod = llvm::cast<clang::CXXMethodDecl>(D);
    assert(cppMethod->isStatic() && "StaticMethodHandler requires static method");

    // Step 1: Extract class and method name
    std::string className = getClassName(cppMethod);
    std::string methodName = cppMethod->getNameAsString();

    // Step 2: Check if class is in namespace
    const clang::CXXRecordDecl* classDecl = cppMethod->getParent();
    if (const auto* nsDecl = llvm::dyn_cast<clang::NamespaceDecl>(classDecl->getDeclContext())) {
        std::string nsPrefix = NamespaceHandler::getNamespacePath(nsDecl);
        if (!nsPrefix.empty()) {
            className = nsPrefix + "__" + className;
            llvm::outs() << "[StaticMethodHandler] Applied namespace prefix: "
                         << cppMethod->getParent()->getNameAsString()
                         << " → " << className << "\n";
        }
    }

    // Step 3: Mangle method name
    std::string mangledName = className + "_" + methodName;

    // Step 4: Translate return type
    clang::QualType cppReturnType = cppMethod->getReturnType();
    const clang::Type* cppReturnTypePtr = cppReturnType.getTypePtr();
    bool typeHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Type*>(cppReturnTypePtr));

    cpptoc::TypeMapper& typeMapper = disp.getTypeMapper();
    clang::QualType cReturnType = typeMapper.getCreated(cppReturnTypePtr);
    if (cReturnType.isNull()) {
        cReturnType = cppReturnType;  // Pass-through if no special handling
    }

    // Step 5: Translate parameters (NO 'this' parameter for static methods)
    std::vector<clang::ParmVarDecl*> cParams = translateParameters(
        cppMethod, disp, cppASTContext, cASTContext
    );

    // Step 6: Translate body (placeholder in Phase 1)
    clang::CompoundStmt* cBody = nullptr;
    if (cppMethod->hasBody()) {
        const clang::Stmt* cppBody = cppMethod->getBody();
        if (cppBody) {
            bool bodyHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));
            if (bodyHandled) {
                cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
                clang::Stmt* cStmt = stmtMapper.getCreated(cppBody);
                if (cStmt) {
                    cBody = llvm::dyn_cast<clang::CompoundStmt>(cStmt);
                }
            }
        }
    }

    // Step 7: Create C function declaration
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(
        mangledName,
        cReturnType,
        cParams,
        cBody
    );

    assert(cFunc && "Failed to create C FunctionDecl for static method");

    // Step 8: Get target path and C TranslationUnit
    std::string targetPath = disp.getTargetPath(cppASTContext, D);
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);
    assert(cTU && "Failed to get/create C TranslationUnit");

    // Step 9: Add C function to C TranslationUnit
    cFunc->setDeclContext(cTU);
    cTU->addDecl(cFunc);

    // Step 10: Register location in PathMapper
    pathMapper.setNodeLocation(cFunc, targetPath);

    // Debug output
    llvm::outs() << "[StaticMethodHandler] Translated static method: " << methodName
                 << " → " << mangledName << " → " << targetPath << "\n";
}

std::string StaticMethodHandler::mangleStaticMethodName(
    const clang::CXXRecordDecl* classDecl,
    const std::string& methodName,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext
) {
    std::string className = classDecl->getNameAsString();

    // Check if class is in namespace
    if (const auto* nsDecl = llvm::dyn_cast<clang::NamespaceDecl>(classDecl->getDeclContext())) {
        std::string nsPrefix = NamespaceHandler::getNamespacePath(nsDecl);
        if (!nsPrefix.empty()) {
            className = nsPrefix + "__" + className;
        }
    }

    return className + "_" + methodName;
}

std::string StaticMethodHandler::getClassName(const clang::CXXMethodDecl* method) {
    const clang::CXXRecordDecl* classDecl = method->getParent();
    return classDecl->getNameAsString();
}

std::vector<clang::ParmVarDecl*> StaticMethodHandler::translateParameters(
    const clang::CXXMethodDecl* method,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    std::vector<clang::ParmVarDecl*> cParams;

    for (const auto* cppParam : method->parameters()) {
        clang::ParmVarDecl* cppParamNonConst = const_cast<clang::ParmVarDecl*>(cppParam);

        // Dispatch parameter to ParameterHandler
        bool handled = disp.dispatch(cppASTContext, cASTContext, cppParamNonConst);

        if (!handled) {
            llvm::errs() << "[StaticMethodHandler] Error: No handler for parameter: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        // Retrieve created C parameter from DeclMapper
        cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
        clang::Decl* cDecl = declMapper.getCreated(cppParam);

        if (!cDecl) {
            llvm::errs() << "[StaticMethodHandler] Error: ParameterHandler did not create C parameter for: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        clang::ParmVarDecl* cParam = llvm::cast<clang::ParmVarDecl>(cDecl);
        cParams.push_back(cParam);
    }

    return cParams;
}

} // namespace cpptoc
```

---

## 7. Edge Cases and Considerations

### 7.1 Edge Cases to Handle

| Edge Case | Handling Strategy |
|-----------|------------------|
| Static method in namespace | Apply namespace prefix: `ns__ClassName__methodName` |
| Static method in namespace in namespace | Nested namespaces: `ns1__ns2__ClassName__methodName` |
| Static method with no parameters | Create empty parameter list (not void, but truly empty) |
| Static method returning reference | TypeHandler converts to pointer |
| Static method with const parameters | Preserve const in translated types |
| Static method with default parameters | Not supported in Phase 1, document limitation |
| Static method with same name as free function | Mangling prevents collision (different prefix) |
| Static method in template class | Not supported in Phase 1, skip or forward-declare |

### 7.2 Distinction from MethodHandler

**MethodHandler (Instance Methods):**
```cpp
// CRITICAL: Must exclude static methods
if (!method->isStatic()) {  // Instance methods ONLY
    // Has 'this' parameter
    // Name: ClassName__methodName (single underscore)
}
```

**StaticMethodHandler (Static Methods):**
```cpp
// CRITICAL: Must match static methods ONLY
if (method->isStatic()) {
    // NO 'this' parameter
    // Name: ClassName__methodName (single underscore, same as instance)
    // Difference: No 'this' in signature
}
```

**Complementary filters ensure no overlap:**
```
CXXMethodDecl
├─ Instance Method (isStatic() == false) → MethodHandler
│  └─ Parameters: [this, p1, p2, ...]
│  └─ Name: ClassName__methodName
│
└─ Static Method (isStatic() == true) → StaticMethodHandler
   └─ Parameters: [p1, p2, ...] (NO 'this')
   └─ Name: ClassName__methodName
```

---

## 8. Testing Strategy

### 8.1 Unit Test Cases

```cpp
// Test 1: Simple static method
TEST_F(StaticMethodHandlerTest, TranslatesSimpleStaticMethod) {
    // C++: class Counter { static int getValue() { return 42; } };
    // Expected C: int Counter__getValue(void) { return 42; }
}

// Test 2: Static method with parameters
TEST_F(StaticMethodHandlerTest, TranslatesStaticMethodWithParameters) {
    // C++: class Math { static int add(int a, int b) { return a + b; } };
    // Expected C: int Math__add(int a, int b) { return a + b; }
}

// Test 3: Static method in namespace
TEST_F(StaticMethodHandlerTest, TranslatesStaticMethodInNamespace) {
    // C++: namespace engine { class Renderer { static void init() {} } }
    // Expected C: void engine__Renderer_init(void)
}

// Test 4: canHandle filters correctly
TEST_F(StaticMethodHandlerTest, CanHandleMatchesStaticMethods) {
    // Matches static methods
    // Rejects instance methods
    // Rejects constructors
    // Rejects destructors
}

// Test 5: Parameter translation
TEST_F(StaticMethodHandlerTest, TranslatesParametersCorrectly) {
    // C++: class Math { static void func(int x, const int& y) {} }
    // Expected C: void Math__func(int x, const int* y)
}

// Test 6: Return type translation
TEST_F(StaticMethodHandlerTest, TranslatesReturnTypeCorrectly) {
    // C++: class Ref { static int& getValue() {} }
    // Expected C: int* Ref_getValue(void)
}

// Test 7: Interaction with MethodHandler
TEST_F(StaticMethodHandlerTest, NoOverlapWithMethodHandler) {
    // MethodHandler handles instance methods
    // StaticMethodHandler handles static methods
    // Both present same class → each handles appropriate methods
}
```

### 8.2 Integration Test Cases

```cpp
// Test: Complete class with both static and instance methods
TEST_F(StaticMethodIntegrationTest, TranslatesCompleteClass) {
    // C++:
    // class Counter {
    // public:
    //     int count;
    //     void increment() { count++; }
    //     static int getVersion() { return 1; }
    // };

    // Expected C:
    // struct Counter {
    //     int count;
    // };
    // void Counter__increment(struct Counter* this);
    // int Counter__getVersion(void);
}

// Test: Static and instance methods in namespace
TEST_F(StaticMethodIntegrationTest, NamespacedClassWithStaticAndInstanceMethods) {
    // C++:
    // namespace game {
    //     class Entity {
    //     public:
    //         void update() {}
    //         static int getMaxEntities() { return 100; }
    //     };
    // }

    // Expected C:
    // struct game__Entity { };
    // void game__Entity__update(struct game__Entity* this);
    // int game__Entity__getMaxEntities(void);
}
```

---

## 9. Summary of Recommendations

### 9.1 Implementation Approach

1. **Create new files:**
   - `include/dispatch/StaticMethodHandler.h`
   - `src/dispatch/StaticMethodHandler.cpp`

2. **Implement pattern:**
   - Follow FunctionHandler/RecordHandler structure
   - Use exact type matching: `getKind() == clang::Decl::CXXMethod`
   - Check `method->isStatic()` in canHandle()
   - Implement complementary filters with MethodHandler

3. **Name mangling:**
   - Single underscore between class name and method name: `ClassName__methodName`
   - Double underscore for namespace prefix: `Namespace__ClassName__methodName`
   - Consistent with existing patterns

4. **Parameter handling:**
   - NO 'this' parameter (key difference from instance methods)
   - Delegate parameter translation to ParameterHandler
   - Delegate type translation to TypeMapper

5. **Registration:**
   - Register AFTER or alongside MethodHandler
   - Order: TypeHandler → NamespaceHandler → ... → MethodHandler → StaticMethodHandler

### 9.2 Key Design Points

| Aspect | Design Choice | Rationale |
|--------|---------------|-----------|
| Type checking | `getKind() == CXXMethod` | Exact matching, exclude derived types |
| Static filter | `method->isStatic()` | Clear and unambiguous |
| Separator | `_` (class) + `__` (namespace) | Consistent with existing pattern |
| This parameter | NONE | C static functions don't need object context |
| Parameter dispatch | ParameterHandler | Reuse existing translation logic |
| Type dispatch | TypeMapper | Reuse existing type system |
| Body handling | StmtMapper dispatch | Consistent with FunctionHandler |
| Registration | After MethodHandler | Clearer flow, simpler filters |

---

## 10. Related Files

**Key files to understand:**
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/dispatch/CppToCVisitorDispatcher.h` - Dispatcher architecture
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/dispatch/FunctionHandler.h` - Free function pattern
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/dispatch/RecordHandler.h` - Struct/class pattern
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/dispatch/NamespaceHandler.h` - Namespace path calculation
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/handlers/MethodHandler.h` - Instance methods (for comparison)
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/*.cpp` - Implementation patterns

---

## Appendix A: Quick Reference - Dispatcher Pattern

```cpp
// Registration
void SomeHandler::registerWith(CppToCVisitorDispatcher& disp) {
    disp.addHandler(&SomeHandler::canHandle, &SomeHandler::handleXXX);
}

// Predicate (filtering)
bool SomeHandler::canHandle(const clang::Decl* D) {
    assert(D);
    if (D->getKind() != clang::Decl::SomeKind) return false;
    // Additional checks
    return true;
}

// Visitor (processing)
void SomeHandler::handleXXX(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppCtx,
    clang::ASTContext& cCtx,
    const clang::Decl* D
) {
    assert(D && D->getKind() == clang::Decl::SomeKind);

    const auto* node = llvm::cast<clang::SomeDecl>(D);

    // Process: extract, translate, create C nodes
    // Dispatch children if needed
    // Register in PathMapper/DeclMapper/TypeMapper
    // Add to C TranslationUnit
}
```

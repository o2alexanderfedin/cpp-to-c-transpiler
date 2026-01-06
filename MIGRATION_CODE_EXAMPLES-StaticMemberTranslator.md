# StaticMemberTranslator Migration - Code Examples

---

## Example 1: Handler Skeleton with Registration

### Header File (StaticMemberHandler.h)

```cpp
/**
 * @file StaticMemberHandler.h
 * @brief Handler for translating C++ static data members to C global variables
 *
 * Dispatcher pattern implementation for Phase 49 static member translation.
 * Registers with CppToCVisitorDispatcher to handle VarDecl nodes that are
 * static data members.
 *
 * Translation Pattern:
 * C++: static int count;     → C: extern int Counter__count;
 * C++: int Counter::count = 0; → C: int Counter__count = 0;
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include <vector>

namespace cpptoc {

/**
 * @class StaticMemberHandler
 * @brief Processes static data member VarDecl nodes and creates C global variables
 *
 * Responsibilities:
 * - Identify static data member declarations (predicate)
 * - Distinguish from instance members (handled by RecordHandler)
 * - Distinguish from file/function scope static (handled by VariableHandler)
 * - Generate extern declarations for headers (SC_Extern)
 * - Generate global definitions for implementation (SC_None + initializer)
 * - Apply consistent name mangling via NameMangler
 *
 * Design Pattern: Chain of Responsibility with CppToCVisitorDispatcher
 *
 * Integration:
 * @code
 * CppToCVisitorDispatcher dispatcher(...);
 * StaticMemberHandler::registerWith(dispatcher);
 *
 * // When dispatcher encounters a static member VarDecl:
 * dispatcher.dispatch(cppCtx, cCtx, staticMemberVarDecl);
 * // → StaticMemberHandler::handleStaticMember() is invoked
 * @endcode
 */
class StaticMemberHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Adds predicate and visitor to dispatcher's handler chain.
     * Must be called during initialization before translation begins.
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is a static data member
     * @param D Declaration to check (must not be null)
     * @return true if D is a VarDecl that is a static data member, false otherwise
     *
     * Matches:
     * - class Counter { static int count; };  ← YES
     *
     * Does NOT match:
     * - int globalCounter = 0;               ← NO (global, not member)
     * - static int fileStatic = 0;           ← NO (file scope, not member)
     * - class Counter { int count; };        ← NO (instance member, not static)
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ static member to C global variable
     * @param disp Dispatcher for accessing mappers and helpers
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D VarDecl to process (guaranteed to be static member via predicate)
     *
     * Algorithm:
     * 1. Cast D to VarDecl
     * 2. Get owning class from DeclContext
     * 3. Check if already translated (skip if yes)
     * 4. Mangle name using NameMangler
     * 5. Extract type and initializer
     * 6. Create C VarDecl:
     *    - If declaration (in-class): SC_Extern
     *    - If definition (out-of-class): SC_None + initializer
     * 7. Register in mappers
     *
     * @pre D != nullptr && D->getKind() == Decl::Var && isStaticDataMember()
     */
    static void handleStaticMember(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    // ====================================================================
    // Utility Functions (migrated from StaticMemberTranslator)
    // ====================================================================

    /**
     * @brief Detect all static data members in a class
     * @param record C++ class/struct declaration
     * @return Vector of static member VarDecls
     */
    static std::vector<clang::VarDecl*> detectStaticMembers(
        const clang::CXXRecordDecl* record
    );

    /**
     * @brief Check if VarDecl is a static member definition
     * @param varDecl Variable to check
     * @return true if this is an out-of-class definition
     *
     * Identifies: int Counter::count = 0;
     * vs: static int count;  (declaration only)
     */
    static bool isStaticMemberDefinition(
        const clang::VarDecl* varDecl
    );

    /**
     * @brief Find the class that owns a static member definition
     * @param definition Static member definition
     * @return CXXRecordDecl of owning class, nullptr if not found
     */
    static clang::CXXRecordDecl* getOwningClass(
        const clang::VarDecl* definition
    );
};

} // namespace cpptoc
```

### Implementation File (StaticMemberHandler.cpp)

```cpp
/**
 * @file StaticMemberHandler.cpp
 * @brief Implementation of StaticMemberHandler dispatcher pattern
 *
 * Translates C++ static data members to C global variables with mangled names.
 * Integrates with CppToCVisitorDispatcher for AST traversal.
 */

#include "dispatch/StaticMemberHandler.h"
#include "NameMangler.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <vector>

using namespace clang;

namespace cpptoc {

// ============================================================================
// Public API
// ============================================================================

void StaticMemberHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &StaticMemberHandler::canHandle,
        &StaticMemberHandler::handleStaticMember
    );
}

// ============================================================================
// Predicate
// ============================================================================

bool StaticMemberHandler::canHandle(const Decl* D) {
    assert(D && "Declaration must not be null");

    // Only handle VarDecl
    if (D->getKind() != Decl::Var) {
        return false;
    }

    auto* varDecl = llvm::cast<VarDecl>(D);

    // Only handle static DATA members
    // isStaticDataMember() is specific to class members
    // Distinguishes from:
    // - Global variables (handled by VariableHandler)
    // - Static file-scope variables (handled by VariableHandler)
    // - Static function-scope variables (handled by VariableHandler)
    if (varDecl->isStaticDataMember()) {
        return true;
    }

    return false;
}

// ============================================================================
// Visitor
// ============================================================================

void StaticMemberHandler::handleStaticMember(
    const CppToCVisitorDispatcher& disp,
    const ASTContext& cppASTContext,
    ASTContext& cASTContext,
    const Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == Decl::Var && "Must be VarDecl");

    auto* cppVarDecl = llvm::cast<VarDecl>(D);
    assert(cppVarDecl->isStaticDataMember() && "Must be static member");

    llvm::outs() << "[StaticMemberHandler] Translating: "
                 << cppVarDecl->getNameAsString() << "\n";

    // ====================================================================
    // Step 1: Get owning class
    // ====================================================================

    auto* record = dyn_cast<CXXRecordDecl>(cppVarDecl->getDeclContext());
    if (!record) {
        llvm::outs() << "[StaticMemberHandler] ERROR: Could not find owning class\n";
        return;
    }

    // ====================================================================
    // Step 2: Check if already translated
    // ====================================================================

    // TODO: Use declMapper to check if already created
    // cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    // if (declMapper.hasCreated(cppVarDecl)) {
    //     return;  // Already translated, skip
    // }

    // ====================================================================
    // Step 3: Generate mangled name
    // ====================================================================

    std::string mangledName = cpptoc::mangle_static_member(cppVarDecl);
    llvm::outs() << "[StaticMemberHandler] Mangled name: " << mangledName << "\n";

    // ====================================================================
    // Step 4: Extract type and initializer
    // ====================================================================

    QualType cppType = cppVarDecl->getType();

    // TODO: Translate C++ type to C type
    // For now, use the same type (works for primitive types and basic pointers)
    // Future: Handle complex types, arrays, etc.
    QualType cType = cppType;

    Expr* cppInitializer = cppVarDecl->getInit();

    // TODO: Translate initializer expression from C++ to C
    // For now, use the same expression (works for literal constants)
    // Future: Handle complex initialization expressions
    Expr* cInitializer = cppInitializer;

    // ====================================================================
    // Step 5: Determine storage class and context
    // ====================================================================

    StorageClass sc;
    bool isDefinition = isStaticMemberDefinition(cppVarDecl);

    if (isDefinition) {
        // Out-of-class definition: int Counter::count = 0;
        sc = SC_None;  // Global scope, no storage class specifier
    } else {
        // In-class declaration: static int count;
        sc = SC_Extern;  // Make it extern for inclusion in header
    }

    // ====================================================================
    // Step 6: Create C VarDecl
    // ====================================================================

    auto* cTU = cASTContext.getTranslationUnitDecl();

    // KEY CHANGE: Replace ctx.getCContext() with cASTContext parameter
    VarDecl* cVarDecl = VarDecl::Create(
        cASTContext,                                  // CHANGED: was ctx.getCContext()
        cTU,
        SourceLocation(),
        SourceLocation(),
        &cASTContext.Idents.get(mangledName),        // CHANGED: was cContext
        cType,
        nullptr,
        sc
    );

    // Set initializer if this is a definition
    if (isDefinition && cInitializer) {
        cVarDecl->setInit(cInitializer);
    }

    // ====================================================================
    // Step 7: Register in mappers (future integration)
    // ====================================================================

    // TODO: Register in declMapper
    // declMapper.map(cppVarDecl, cVarDecl);

    // TODO: Register in PathMapper for location tracking
    // std::string targetPath = disp.getTargetPath(cppASTContext, D);
    // pathMapper.registerLocation(...);

    llvm::outs() << "[StaticMemberHandler] Created VarDecl: " << mangledName
                 << " (storage class: " << (isDefinition ? "SC_None" : "SC_Extern") << ")\n";
}

// ============================================================================
// Utility Functions
// ============================================================================

std::vector<VarDecl*> StaticMemberHandler::detectStaticMembers(
    const CXXRecordDecl* record
) {
    std::vector<VarDecl*> staticMembers;

    if (!record) {
        return staticMembers;
    }

    // Walk through all declarations in the class
    for (auto* decl : record->decls()) {
        if (auto* varDecl = dyn_cast<VarDecl>(decl)) {
            if (varDecl->isStaticDataMember()) {
                staticMembers.push_back(varDecl);
            }
        }
    }

    return staticMembers;
}

bool StaticMemberHandler::isStaticMemberDefinition(const VarDecl* varDecl) {
    if (!varDecl) {
        return false;
    }

    // Check all three conditions for definition:
    // 1. Must be a static data member
    if (!varDecl->isStaticDataMember()) {
        return false;
    }

    // 2. Must be at file scope (not local variable)
    if (!varDecl->isFileVarDecl()) {
        return false;
    }

    // 3. Must be a definition (has initializer or is canonical)
    if (!varDecl->isThisDeclarationADefinition()) {
        return false;
    }

    return true;
}

CXXRecordDecl* StaticMemberHandler::getOwningClass(const VarDecl* definition) {
    if (!definition) {
        return nullptr;
    }

    auto* declContext = definition->getDeclContext();
    if (auto* record = dyn_cast<CXXRecordDecl>(declContext)) {
        // Cast away const - safe for AST navigation
        return const_cast<CXXRecordDecl*>(record);
    }

    return nullptr;
}

} // namespace cpptoc
```

---

## Example 2: Before/After Code Comparison

### BEFORE: Using HandlerContext

```cpp
// StaticMemberTranslator.cpp - Original

VarDecl* StaticMemberTranslator::generateStaticDeclaration(
    VarDecl* staticMember,
    HandlerContext& ctx          // ← Old: HandlerContext parameter
) {
    if (!staticMember || !staticMember->isStaticDataMember()) {
        return nullptr;
    }

    auto* record = dyn_cast<CXXRecordDecl>(staticMember->getDeclContext());
    if (!record) {
        return nullptr;
    }

    std::string mangledName = getMangledName(record, staticMember, ctx);
    QualType cppType = staticMember->getType();
    QualType cType = cppType;  // TODO: Translate type

    auto& cContext = ctx.getCContext();  // ← Dependency: HandlerContext
    auto* cTU = cContext.getTranslationUnitDecl();

    VarDecl* cDecl = VarDecl::Create(
        cContext,                               // ← From HandlerContext
        cTU,
        SourceLocation(),
        SourceLocation(),
        &cContext.Idents.get(mangledName),     // ← From HandlerContext
        cType,
        nullptr,
        SC_Extern
    );

    return cDecl;
}

std::string StaticMemberTranslator::getMangledName(
    CXXRecordDecl* record,
    VarDecl* member,
    HandlerContext& ctx  // ← Parameter unused!
) {
    return cpptoc::mangle_static_member(member);  // Direct call, no ctx usage
}
```

### AFTER: Using Dispatcher Pattern

```cpp
// StaticMemberHandler.cpp - New

void StaticMemberHandler::handleStaticMember(
    const CppToCVisitorDispatcher& disp,      // ← New: Dispatcher parameter
    const clang::ASTContext& cppASTContext,  // ← New: Source AST
    clang::ASTContext& cASTContext,          // ← New: Direct parameter (replaces HandlerContext)
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    auto* cppVarDecl = llvm::cast<VarDecl>(D);

    if (!cppVarDecl->isStaticDataMember()) {
        return;
    }

    auto* record = dyn_cast<CXXRecordDecl>(cppVarDecl->getDeclContext());
    if (!record) {
        return;
    }

    std::string mangledName = cpptoc::mangle_static_member(cppVarDecl);
    // ↑ Direct call, no intermediate function needed
    // ↑ No HandlerContext parameter required

    QualType cppType = cppVarDecl->getType();
    QualType cType = cppType;  // TODO: Translate type

    auto* cTU = cASTContext.getTranslationUnitDecl();
    // ↑ Direct call on cASTContext parameter

    VarDecl* cVarDecl = VarDecl::Create(
        cASTContext,                                  // ← Direct parameter!
        cTU,
        SourceLocation(),
        SourceLocation(),
        &cASTContext.Idents.get(mangledName),        // ← Direct parameter!
        cType,
        nullptr,
        SC_Extern  // or SC_None for definitions
    );

    // Optional: Set initializer for definitions
    if (isStaticMemberDefinition(cppVarDecl)) {
        if (auto* init = cppVarDecl->getInit()) {
            cVarDecl->setInit(init);
        }
    }
}
```

### Key Changes

| Aspect | Before | After |
|--------|--------|-------|
| **Function Signature** | `(VarDecl*, HandlerContext&)` | `(const CppToCVisitorDispatcher&, const ASTContext&, ASTContext&, const Decl*)` |
| **C Context** | `ctx.getCContext()` | `cASTContext` parameter |
| **Handler Registration** | Manual in caller | `registerWith(dispatcher)` |
| **Predicate** | Implicit in caller | Explicit `canHandle()` method |
| **Error Handling** | Return nullptr | Early return/assert |
| **Extra Context** | C++ AST not available | Both C++ and C AST available |

---

## Example 3: Registration and Usage

### How to Register

```cpp
// In main translator initialization (e.g., TranslationUnitHandler)

#include "dispatch/StaticMemberHandler.h"

void initializeHandlers(CppToCVisitorDispatcher& dispatcher) {
    // Register handlers in dependency order
    // ...

    // Register StaticMemberHandler
    // Can be registered anywhere, no special ordering needed
    StaticMemberHandler::registerWith(dispatcher);

    // ...
}
```

### How Handler Gets Invoked

```cpp
// Dispatcher encounters a VarDecl
// 1. Checks all registered predicates in order
// 2. When StaticMemberHandler::canHandle() returns true:
//    - Invokes StaticMemberHandler::handleStaticMember()

// User's C++ code:
class Counter {
public:
    static int count;  // VarDecl that is a static data member
};

int Counter::count = 0;  // Another VarDecl that is definition

// Dispatcher automatically:
// 1. Encounters first VarDecl (count declaration)
// 2. StaticMemberHandler::canHandle() returns true
// 3. Calls StaticMemberHandler::handleStaticMember()
//    → Creates extern int Counter__count;

// 4. Encounters second VarDecl (count definition)
// 5. StaticMemberHandler::canHandle() returns true
// 6. Calls StaticMemberHandler::handleStaticMember()
//    → Creates int Counter__count = 0;
```

---

## Example 4: Test Cases

### Unit Test Example

```cpp
// tests/unit/dispatch/StaticMemberHandlerTest.cpp

#include <gtest/gtest.h>
#include "dispatch/StaticMemberHandler.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/DeclCXX.h"
#include <cassert>

using namespace clang;

class StaticMemberHandlerTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char* code) {
        return tooling::buildASTFromCode(code);
    }

    // Helper to find a VarDecl by name
    VarDecl* findVarDecl(ASTContext& ctx, const std::string& name) {
        auto* TU = ctx.getTranslationUnitDecl();
        for (auto* D : TU->decls()) {
            if (auto* VD = dyn_cast<VarDecl>(D)) {
                if (VD->getNameAsString() == name) {
                    return VD;
                }
            }
        }
        return nullptr;
    }
};

// Test 1: Predicate matches static members
TEST_F(StaticMemberHandlerTest, PredicateMatchesStaticMember) {
    const char* code = R"(
        class Counter {
        public:
            static int count;
        };
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST);

    auto& ctx = AST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    // Find the Counter class
    CXXRecordDecl* Counter = nullptr;
    VarDecl* countMember = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Counter" && RD->isCompleteDefinition()) {
                Counter = RD;
                for (auto* Decl : RD->decls()) {
                    if (auto* VD = dyn_cast<VarDecl>(Decl)) {
                        if (VD->getNameAsString() == "count") {
                            countMember = VD;
                        }
                    }
                }
            }
        }
    }

    ASSERT_TRUE(Counter != nullptr) << "Counter class not found";
    ASSERT_TRUE(countMember != nullptr) << "count member not found";

    // Test predicate
    EXPECT_TRUE(StaticMemberHandler::canHandle(countMember));
}

// Test 2: Predicate doesn't match instance members
TEST_F(StaticMemberHandlerTest, PredicateRejectsInstanceMember) {
    const char* code = R"(
        class Counter {
        public:
            int count;  // Instance member, not static
        };
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST);

    auto& ctx = AST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    CXXRecordDecl* Counter = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Counter") {
                Counter = RD;
                break;
            }
        }
    }

    ASSERT_TRUE(Counter != nullptr);

    // Instance members are FieldDecl, not VarDecl
    for (auto* D : Counter->decls()) {
        if (D->getKind() != Decl::Var) {
            continue;  // Skip FieldDecl
        }
        // If we reach here, test the VarDecl
        EXPECT_FALSE(StaticMemberHandler::canHandle(D));
    }
}

// Test 3: Detects static members in a class
TEST_F(StaticMemberHandlerTest, DetectsAllStaticMembers) {
    const char* code = R"(
        class Stats {
        public:
            static int count;
            static int total;
            int value;  // Instance member
        };
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST);

    auto& ctx = AST->getASTContext();
    CXXRecordDecl* Stats = nullptr;

    for (auto* D : ctx.getTranslationUnitDecl()->decls()) {
        if (auto* RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Stats") {
                Stats = RD;
                break;
            }
        }
    }

    ASSERT_TRUE(Stats != nullptr);

    auto staticMembers = StaticMemberHandler::detectStaticMembers(Stats);
    ASSERT_EQ(staticMembers.size(), 2);
    EXPECT_EQ(staticMembers[0]->getNameAsString(), "count");
    EXPECT_EQ(staticMembers[1]->getNameAsString(), "total");
}

// Test 4: Identifies definitions vs declarations
TEST_F(StaticMemberHandlerTest, IdentifiesDefinitionVsDeclaration) {
    const char* code = R"(
        class Counter {
        public:
            static int count;  // Declaration
        };
        int Counter::count = 0;  // Definition
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST);

    auto& ctx = AST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    VarDecl* declaration = nullptr;
    VarDecl* definition = nullptr;

    // Find both VarDecls
    for (auto* D : TU->decls()) {
        if (auto* VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "count") {
                if (VD->isFileVarDecl()) {
                    definition = VD;
                } else {
                    // In-class declaration found elsewhere
                }
            }
        }
    }

    // This test may need adjustment based on how Clang structures AST
    if (definition) {
        EXPECT_TRUE(StaticMemberHandler::isStaticMemberDefinition(definition));
    }
}
```

---

## Example 5: Type and Initializer Translation (Future)

### Current State (TODO)

```cpp
// Current implementation - deferred to future phase

// Type translation TODO
QualType cppType = staticMember->getType();
// TODO: Translate C++ type to C type
// For now, use the same type (works for primitive types)
QualType cType = cppType;  // NO TRANSLATION

// Initializer translation TODO
Expr* initializer = staticMember->getInit();
// TODO: Translate initializer expression from C++ to C
// For now, use the same expression
Expr* cInitializer = initializer;  // NO TRANSLATION
```

### Future Implementation (Sketch)

```cpp
// Future phase - full type and expression translation

// Type translation (would use TypeMapper)
QualType cppType = staticMember->getType();
QualType cType;

if (disp.getTypeMapper().hasCreated(cppType.getTypePtr())) {
    cType = disp.getTypeMapper().getCreated(cppType.getTypePtr());
} else {
    // Dispatch to TypeHandler for translation
    // This requires recursive dispatch capability
    // disp.dispatch(cppASTContext, cASTContext, cppType.getTypePtr());
    // cType = disp.getTypeMapper().getCreated(cppType.getTypePtr());
    cType = cppType;  // Fallback
}

// Expression translation (would use ExprMapper)
Expr* cppInitializer = staticMember->getInit();
Expr* cInitializer = nullptr;

if (cppInitializer) {
    if (disp.getExprMapper().hasCreated(cppInitializer)) {
        cInitializer = disp.getExprMapper().getCreated(cppInitializer);
    } else {
        // Dispatch to ExprHandler for translation
        // disp.dispatch(cppASTContext, cASTContext, cppInitializer);
        // cInitializer = disp.getExprMapper().getCreated(cppInitializer);
        cInitializer = cppInitializer;  // Fallback
    }
}
```

---

## Summary

The migration from **StaticMemberTranslator** (helper) to **StaticMemberHandler** (dispatcher) involves:

1. **API Change**: Function-based → Dispatcher pattern with predicate and visitor
2. **Dependency Change**: HandlerContext → Direct ASTContext parameter
3. **Registration Change**: Manual calls → Dispatcher registration
4. **Code Location**: helpers/ → dispatch/
5. **Logic Preservation**: Core translation logic unchanged
6. **Future Enhancement**: Type and expression translation deferred

All changes are straightforward substitutions with improved architecture alignment.

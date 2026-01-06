# StaticMemberTranslator Migration - Quick Reference

**Status**: Ready for Implementation
**Complexity**: LOW
**Estimated Time**: 2-3 hours

---

## 1. Methods to Migrate

### Static Utility Methods (Keep As-Is)
```cpp
// Can be moved to StaticMemberHandler as static utilities
static std::vector<clang::VarDecl*> detectStaticMembers(
    const clang::CXXRecordDecl* record
);

static bool isStaticMemberDefinition(const clang::VarDecl* varDecl);

static clang::CXXRecordDecl* getOwningClass(
    const clang::VarDecl* definition
);
```

### Translation Methods (Migrate to Visitor)
```cpp
// MIGRATE to StaticMemberHandler::handleStaticMember()
static clang::VarDecl* generateStaticDeclaration(
    clang::VarDecl* staticMember,
    HandlerContext& ctx           // BECOMES: clang::ASTContext& cASTContext
);

static clang::VarDecl* generateStaticDefinition(
    clang::VarDecl* staticMember,
    HandlerContext& ctx           // BECOMES: clang::ASTContext& cASTContext
);

// MIGRATE to StaticMemberHandler (private)
static std::string getMangledName(
    clang::CXXRecordDecl* record,
    clang::VarDecl* member,
    HandlerContext& ctx           // BECOMES: (removed, not used)
);
```

---

## 2. HandlerContext Replacements

### What Gets Removed
```cpp
// OLD: Using HandlerContext
HandlerContext& ctx;
auto& cContext = ctx.getCContext();
```

### What Replaces It
```cpp
// NEW: Direct parameter in visitor
clang::ASTContext& cASTContext;  // Passed to handleStaticMember()
```

### API Equivalence
| Old | New | Status |
|-----|-----|--------|
| `ctx.getCContext()` | `cASTContext` | Direct replacement |
| `cContext.getTranslationUnitDecl()` | `cASTContext.getTranslationUnitDecl()` | Same call |
| `cContext.Idents.get(name)` | `cASTContext.Idents.get(name)` | Same call |

---

## 3. Handler Skeleton

```cpp
// StaticMemberHandler.h
#pragma once
#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Decl.h"

namespace cpptoc {

class StaticMemberHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Decl* D);

    static void handleStaticMember(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    // Utilities from StaticMemberTranslator
    static std::vector<clang::VarDecl*> detectStaticMembers(
        const clang::CXXRecordDecl* record
    );

    static bool isStaticMemberDefinition(
        const clang::VarDecl* varDecl
    );

    static clang::CXXRecordDecl* getOwningClass(
        const clang::VarDecl* definition
    );
};

} // namespace cpptoc
```

---

## 4. Implementation Pattern

### Registration
```cpp
// StaticMemberHandler.cpp

void StaticMemberHandler::registerWith(
    CppToCVisitorDispatcher& dispatcher
) {
    dispatcher.addHandler(
        &StaticMemberHandler::canHandle,
        &StaticMemberHandler::handleStaticMember
    );
}
```

### Predicate
```cpp
bool StaticMemberHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Only handle static data members
    if (D->getKind() != clang::Decl::Var) {
        return false;
    }

    auto* varDecl = llvm::cast<clang::VarDecl>(D);
    return varDecl->isStaticDataMember();
}
```

### Visitor (Simplified)
```cpp
void StaticMemberHandler::handleStaticMember(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,  // REPLACES ctx.getCContext()
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    auto* staticMember = llvm::cast<clang::VarDecl>(D);

    // Get owning class
    auto* record = dyn_cast<clang::CXXRecordDecl>(
        staticMember->getDeclContext()
    );
    if (!record) return;

    // Check if already translated (skip if yes)
    // TODO: Check against declMapper

    // Get mangled name
    std::string mangledName = cpptoc::mangle_static_member(staticMember);

    // Get type (no translation for Phase 1)
    clang::QualType cType = staticMember->getType();

    // Create C VarDecl
    auto* cTU = cASTContext.getTranslationUnitDecl();
    clang::VarDecl* cDecl = clang::VarDecl::Create(
        cASTContext,                              // Changed from ctx.getCContext()
        cTU,
        clang::SourceLocation(),
        clang::SourceLocation(),
        &cASTContext.Idents.get(mangledName),   // Changed from cContext
        cType,
        nullptr,
        clang::SC_Extern  // Or SC_None for definition
    );

    // Handle initializer if definition
    if (isStaticMemberDefinition(staticMember)) {
        if (auto* init = staticMember->getInit()) {
            cDecl->setInit(init);  // TODO: Translate initializer
        }
    }

    // Store in mapper
    // TODO: declMapper.map(staticMember, cDecl);
}
```

---

## 5. Key Code Snippets from Current Implementation

### VarDecl Creation (Declaration - Extern)
```cpp
// Lines 80-89 of StaticMemberTranslator.cpp
VarDecl* cDecl = VarDecl::Create(
    cContext,                               // BECOMES: cASTContext
    cTU,                                    // BECOMES: cASTContext.getTranslationUnitDecl()
    SourceLocation(),
    SourceLocation(),
    &cContext.Idents.get(mangledName),     // BECOMES: &cASTContext.Idents.get()
    cType,
    nullptr,
    SC_Extern                               // Storage class for declaration
);
```

### VarDecl Creation (Definition - Global)
```cpp
// Lines 137-146 of StaticMemberTranslator.cpp
VarDecl* cDecl = VarDecl::Create(
    cContext,                               // BECOMES: cASTContext
    cTU,                                    // BECOMES: cASTContext.getTranslationUnitDecl()
    SourceLocation(),
    SourceLocation(),
    &cContext.Idents.get(mangledName),     // BECOMES: &cASTContext.Idents.get()
    cType,
    nullptr,
    SC_None                                 // Storage class for definition
);

// Set initializer if present
if (cInitializer) {
    cDecl->setInit(cInitializer);
}
```

### Name Mangling
```cpp
// Line 209 - Direct call, no changes needed
return cpptoc::mangle_static_member(member);
```

---

## 6. Integration Points

### Where Handler Gets Registered
**TBD**: Search codebase to find where other handlers are registered

Likely locations:
- `TranslationUnitHandler::handleTranslationUnit()`
- Main translation pipeline setup
- `CppToCConsumer::HandleTranslationUnit()`

### Order Matters
- Must register AFTER type handlers
- May need to register BEFORE or AFTER VariableHandler (depends on predicate specificity)
- Should register near RecordHandler (related to classes)

---

## 7. Test Structure

### Unit Test Skeleton
```cpp
// tests/unit/dispatch/StaticMemberHandlerTest.cpp
#include <gtest/gtest.h>
#include "dispatch/StaticMemberHandler.h"
#include "mapping/DeclMapper.h"
#include "clang/Tooling/Tooling.h"

class StaticMemberHandlerTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> buildAST(const char* code) {
        return clang::tooling::buildASTFromCode(code);
    }
};

// Test predicate
TEST_F(StaticMemberHandlerTest, CanHandleStaticMember) {
    const char* code = R"(
        class Counter {
        public:
            static int count;
        };
    )";

    auto AST = buildAST(code);
    // Find static member and verify canHandle returns true
}

// Test declaration generation
TEST_F(StaticMemberHandlerTest, GeneratesExternDeclaration) {
    // Verify SC_Extern
    // Verify mangled name
    // Verify type preserved
}

// Test definition generation
TEST_F(StaticMemberHandlerTest, GeneratesGlobalDefinition) {
    // Verify SC_None
    // Verify initializer set
    // Verify mangled name matches declaration
}
```

---

## 8. Includes Needed

### For Handler Header
```cpp
#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
```

### For Handler Implementation
```cpp
#include "dispatch/StaticMemberHandler.h"
#include "NameMangler.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"
#include <vector>
#include <cassert>
```

---

## 9. Checklist for Migration

### Planning
- [ ] Search for all StaticMemberTranslator usages
- [ ] Identify where handler should be registered
- [ ] Verify no other handlers conflict (predicate)
- [ ] Document handler registration order

### Implementation
- [ ] Create StaticMemberHandler.h
- [ ] Create StaticMemberHandler.cpp
- [ ] Implement registerWith()
- [ ] Implement canHandle()
- [ ] Implement handleStaticMember()
- [ ] Copy utility functions (detectStaticMembers, etc.)
- [ ] Replace HandlerContext with cASTContext
- [ ] Update all TODO comments

### Testing
- [ ] Create StaticMemberHandlerTest.cpp
- [ ] Write predicate tests
- [ ] Write declaration generation tests
- [ ] Write definition generation tests
- [ ] Test error cases
- [ ] Run unit tests
- [ ] Run integration tests
- [ ] Verify no regressions

### Integration
- [ ] Register handler in appropriate location
- [ ] Test in full translation pipeline
- [ ] Verify static members are properly translated
- [ ] Check generated C code

### Cleanup
- [ ] Decide: Keep or remove original StaticMemberTranslator
- [ ] Update CMakeLists.txt
- [ ] Add git commit
- [ ] Update CLAUDE.md

---

## 10. Common Mistakes to Avoid

1. **Don't forget null checks**
   ```cpp
   if (!record) return;  // GetOwningClass can return nullptr
   ```

2. **Don't confuse storage classes**
   ```cpp
   SC_Extern  // For extern declaration (header)
   SC_None    // For global definition (implementation)
   ```

3. **Don't forget to preserve const**
   - Automatically preserved in QualType
   - No special handling needed

4. **Don't skip initializer for definitions**
   ```cpp
   if (cInitializer) {
       cDecl->setInit(cInitializer);  // Must set for definitions
   }
   ```

5. **Don't use HandlerContext methods**
   - Replace ctx.getCContext() with cASTContext parameter
   - No mapper needed for basic static members

---

## 11. Files to Reference

### Source Files (Current)
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/helpers/StaticMemberTranslator.h`
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/helpers/StaticMemberTranslator.cpp`

### Test Files (Current)
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/unit/helpers/NameManglerStaticMemberTest.cpp`

### Reference Implementations
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/dispatch/VariableHandler.h`
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/VariableHandler.cpp`
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/dispatch/RecordHandler.h`
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/RecordHandler.cpp`

### NameMangler Reference
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/NameMangler.h` (line 235)

---

## 12. Expected Output

After migration, translation should produce:

**Input (C++)**:
```cpp
class Counter {
public:
    static int count;
    static const int MAX = 100;
};

int Counter::count = 0;
const int Counter::MAX = 100;
```

**Output (C Header)**:
```c
extern int Counter__count;
extern const int Counter__MAX;
```

**Output (C Implementation)**:
```c
int Counter__count = 0;
const int Counter__MAX = 100;
```

---

## Summary

| Aspect | Value |
|--------|-------|
| **Complexity** | LOW |
| **Risk** | LOW |
| **Effort** | 2-3 hours |
| **Files to Create** | 3 |
| **Methods to Migrate** | 5 |
| **HandlerContext Methods Used** | 1 (getCContext) |
| **Breaking Changes** | None |
| **Test Coverage** | Excellent (existing tests) |

**Ready to start implementation!**

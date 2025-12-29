# InstanceMethodHandler Implementation Prompt

## Objective

Implement InstanceMethodHandler following the dispatcher Chain of Responsibility pattern to translate C++ non-static, non-virtual instance methods to C free functions with explicit `this` parameter and class/namespace prefixing.

**Why this matters:**
- Instance methods need explicit `this` parameter (C has no implicit `this`)
- Must apply class name prefix and namespace prefix (if applicable)
- Must integrate with existing dispatcher infrastructure
- Must use `__` separator consistently for all C++ scope resolution
- Complements StaticMethodHandler (which has NO `this` parameter)

## Context

### Existing Implementation

**OLD FRAMEWORK:** `src/handlers/MethodHandler.cpp` exists but:
- Uses old handler framework (not dispatcher)
- Uses single underscore `_` separator (incorrect)
- Will be migrated to dispatcher framework with `__` separator

**NEW FRAMEWORK:** Need to create InstanceMethodHandler in `dispatch/` following:
- StaticMethodHandler pattern (just implemented)
- FunctionHandler pattern (free function)
- RecordHandler pattern (class context)

### Referenced Files

Read these files to understand the established patterns:

**@include/dispatch/StaticMethodHandler.h** - Static methods (NO `this` parameter) - COPY THIS STRUCTURE
**@src/dispatch/StaticMethodHandler.cpp** - Static method implementation (difference: add `this`)
**@include/dispatch/FunctionHandler.h** - Free function handler pattern
**@src/dispatch/FunctionHandler.cpp** - Free function implementation
**@include/dispatch/NamespaceHandler.h** - Namespace path computation
**@include/dispatch/CppToCVisitorDispatcher.h** - Dispatcher interface

**@src/handlers/MethodHandler.cpp** - OLD framework (reference for logic, NOT pattern)

## Requirements

### 1. Create InstanceMethodHandler Class

**File:** `include/dispatch/InstanceMethodHandler.h`

**Structure:**
```cpp
namespace cpptoc {

class InstanceMethodHandler {
public:
    // Registration
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    // Public helpers (for testing)
    static std::string getMangledName(
        const clang::CXXMethodDecl* method,
        const clang::CXXRecordDecl* classDecl
    );

private:
    // Predicate: Match instance methods ONLY (non-static, non-virtual, non-ctor, non-dtor)
    static bool canHandle(const clang::Decl* D);

    // Visitor: Translate instance method to C function with "this" parameter
    static void handleInstanceMethod(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    // Helper: Translate parameters (delegate to ParameterHandler)
    static std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::CXXMethodDecl* method,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );

    // Helper: Create "this" parameter (struct ClassName* this)
    static clang::ParmVarDecl* createThisParameter(
        const clang::CXXRecordDecl* classDecl,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
```

**Documentation requirements:**
- Class-level Doxygen comment explaining responsibility
- Method-level Doxygen for all public methods
- Translation examples in header (C++ → C)
- Algorithm descriptions for canHandle and handleInstanceMethod
- Explain difference from StaticMethodHandler (has `this` parameter)

### 2. Implement canHandle() Predicate

**Critical requirements:**
```cpp
static bool canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // EXACT type matching (NOT isa<> which matches derived types)
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);

    // Exclude constructors and destructors (dedicated handlers)
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // Exclude static methods (handled by StaticMethodHandler)
    if (method->isStatic()) {
        return false;
    }

    // Exclude virtual methods (handled by VirtualMethodHandler - future phase)
    if (method->isVirtual()) {
        return false;
    }

    // Match non-static, non-virtual instance methods ONLY
    return true;
}
```

**Why these checks:**
- `getKind() == CXXMethod` ensures exact type (not derived types)
- Exclude ctors/dtors (dedicated handlers)
- `!isStatic()` filter creates complementary partition with StaticMethodHandler
- `!isVirtual()` excludes virtual methods (future VirtualMethodHandler)

### 3. Implement Name Mangling

**Name format:** `Namespace__ClassName__methodName`

**Separator rules:**
- `__` (double underscore) for ALL C++ scope resolution `::`
- **SAME AS StaticMethodHandler** - only difference is `this` parameter

**Algorithm:**
```cpp
static std::string getMangledName(
    const clang::CXXMethodDecl* method,
    const clang::CXXRecordDecl* classDecl
) {
    std::string methodName = method->getNameAsString();
    std::string className = classDecl->getNameAsString();

    // Check if class is in namespace
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
            classDecl->getDeclContext())) {
        std::string nsPath = NamespaceHandler::getNamespacePath(ns);
        if (!nsPath.empty()) {
            className = nsPath + "__" + className;
        }
    }

    // Apply class prefix to method
    return className + "__" + methodName;
}
```

**Examples:**
- `Counter::increment()` → `Counter__increment`
- `game::Entity::update()` → `game__Entity__update`
- `ns1::ns2::Math::compute()` → `ns1__ns2__Math__compute`

### 4. Implement createThisParameter()

**Critical difference from StaticMethodHandler:**

```cpp
static clang::ParmVarDecl* createThisParameter(
    const clang::CXXRecordDecl* classDecl,
    clang::ASTContext& cASTContext
) {
    // Get class name (with namespace prefix if applicable)
    std::string className = classDecl->getNameAsString();

    // Apply namespace prefix if class is in namespace
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
            classDecl->getDeclContext())) {
        std::string nsPath = NamespaceHandler::getNamespacePath(ns);
        if (!nsPath.empty()) {
            className = nsPath + "__" + className;
        }
    }

    // Create struct type: "struct ClassName"
    clang::IdentifierInfo& structII = cASTContext.Idents.get(className);
    clang::RecordDecl* structDecl = clang::RecordDecl::Create(
        cASTContext,
        clang::TagTypeKind::Struct,
        cASTContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &structII
    );

    // Create pointer type: "struct ClassName*"
    clang::QualType structType = cASTContext.getRecordType(structDecl);
    clang::QualType pointerType = cASTContext.getPointerType(structType);

    // Create parameter: "this"
    clang::IdentifierInfo& thisII = cASTContext.Idents.get("this");
    clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
        cASTContext,
        nullptr,  // Parent (will be set later)
        clang::SourceLocation(),
        clang::SourceLocation(),
        &thisII,
        pointerType,
        cASTContext.getTrivialTypeSourceInfo(pointerType),
        clang::SC_None,
        nullptr  // Default arg
    );

    return thisParam;
}
```

**Why this approach:**
- Creates `struct ClassName* this` parameter
- First parameter in function signature
- Allows accessing class members via `this->field`

### 5. Implement handleInstanceMethod()

**Algorithm (follow StaticMethodHandler + add `this`):**

1. **Assert preconditions**
2. **Cast to CXXMethodDecl**
3. **Get class context:** `method->getParent()`
4. **Compute mangled name:** Use getMangledName()
5. **Create `this` parameter:** Use createThisParameter()
6. **Translate return type:** Dispatch to TypeHandler
7. **Translate method parameters:** Delegate to ParameterHandler (via translateParameters helper)
8. **Combine parameters:** `[this] + methodParams`
9. **Translate body:** Dispatch to CompoundStmtHandler, retrieve from StmtMapper
10. **Create C function:** Use CNodeBuilder::funcDecl() with `this` as first parameter
11. **Add to C TranslationUnit:** Via PathMapper::getOrCreateTU()
12. **Register location:** PathMapper::setNodeLocation()
13. **Debug output:** Log translation for verification

**Key difference from StaticMethodHandler:**
- Create `this` parameter first
- Add `this` as first parameter in parameter list
- Name mangling is same
- Everything else follows same pattern

**Implementation pattern:**
```cpp
// Get class context
const auto* classDecl = method->getParent();

// Compute mangled name
std::string name = getMangledName(method, classDecl);

// Create "this" parameter (FIRST)
clang::ParmVarDecl* thisParam = createThisParameter(classDecl, cASTContext);

// Translate method parameters
std::vector<clang::ParmVarDecl*> methodParams = translateParameters(...);

// Combine: this + method params
std::vector<clang::ParmVarDecl*> allParams;
allParams.push_back(thisParam);
allParams.insert(allParams.end(), methodParams.begin(), methodParams.end());

// Create C function with all parameters
clang::FunctionDecl* cFunc = builder.funcDecl(name, returnType, allParams, body);
```

### 6. Update CMakeLists.txt

**Add source to cpptoc_core:**
```cmake
# Around line 200
set(CPPTOC_CORE_SOURCES
    # ... existing sources ...
    src/dispatch/InstanceMethodHandler.cpp
)
```

**Add test target:**
```cmake
# After StaticMethodHandlerDispatcherTest
add_executable(InstanceMethodHandlerDispatcherTest
    tests/unit/dispatch/InstanceMethodHandlerDispatcherTest.cpp
)

target_include_directories(InstanceMethodHandlerDispatcherTest PRIVATE
    ${PROJECT_SOURCE_DIR}/include
    ${PROJECT_SOURCE_DIR}/tests/helpers
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(InstanceMethodHandlerDispatcherTest PRIVATE
    cpptoc_core
    gtest
    gtest_main
    ${CLANG_LIBS}
    ${LLVM_LIBS}
)

gtest_discover_tests(InstanceMethodHandlerDispatcherTest
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
    PROPERTIES LABELS "unit;dispatcher;instance-method"
)
```

### 7. Write Comprehensive Tests

**File:** `tests/unit/dispatch/InstanceMethodHandlerDispatcherTest.cpp`

**Required test cases:**

```cpp
// Test 1: Handler registration
TEST(InstanceMethodHandlerDispatcherTest, Registration) {
    // Verify handler registers and processes instance method
}

// Test 2: Simple instance method
TEST(InstanceMethodHandlerDispatcherTest, SimpleInstanceMethod) {
    const char* cpp = R"(
        class Counter {
            void increment() {}
        };
    )";
    // Expected: void Counter__increment(struct Counter* this) {}
}

// Test 3: Instance method with parameters
TEST(InstanceMethodHandlerDispatcherTest, InstanceMethodWithParameters) {
    const char* cpp = R"(
        class Math {
            int add(int a, int b) { return a + b; }
        };
    )";
    // Expected: int Math__add(struct Math* this, int a, int b) { return a + b; }
}

// Test 4: Instance method in namespace
TEST(InstanceMethodHandlerDispatcherTest, InstanceMethodInNamespace) {
    const char* cpp = R"(
        namespace game {
            class Entity {
                void update() {}
            };
        }
    )";
    // Expected: void game__Entity__update(struct game__Entity* this) {}
}

// Test 5: Nested namespace
TEST(InstanceMethodHandlerDispatcherTest, NestedNamespaceInstanceMethod) {
    const char* cpp = R"(
        namespace ns1 {
            namespace ns2 {
                class Calculator {
                    int multiply(int a, int b) { return a * b; }
                };
            }
        }
    )";
    // Expected: int ns1__ns2__Calculator__multiply(struct ns1__ns2__Calculator* this, int a, int b)
}

// Test 6: Reference parameter conversion
TEST(InstanceMethodHandlerDispatcherTest, ReferenceParameterConversion) {
    const char* cpp = R"(
        class Formatter {
            void format(const std::string& s);
        };
    )";
    // Expected: const pointer conversion (reference → pointer)
}

// Test 7: Return type conversion
TEST(InstanceMethodHandlerDispatcherTest, ReferenceReturnTypeConversion) {
    const char* cpp = R"(
        class Container {
            int& get() { return value; }
            int value;
        };
    )";
    // Expected: int* Container__get(struct Container* this) (reference → pointer)
}

// Test 8: Exclude static methods
TEST(InstanceMethodHandlerDispatcherTest, IgnoresStaticMethods) {
    const char* cpp = R"(
        class Counter {
            static int getValue() { return 42; }
        };
    )";
    // Verify: InstanceMethodHandler does NOT handle this
}

// Test 9: Exclude virtual methods
TEST(InstanceMethodHandlerDispatcherTest, IgnoresVirtualMethods) {
    const char* cpp = R"(
        class Base {
            virtual void foo() {}
        };
    )";
    // Verify: InstanceMethodHandler does NOT handle this (VirtualMethodHandler)
}

// Test 10: Exclude constructors
TEST(InstanceMethodHandlerDispatcherTest, IgnoresConstructors) {
    const char* cpp = R"(
        class Counter {
            Counter() {}
        };
    )";
    // Verify: InstanceMethodHandler does NOT handle this
}

// Test 11: Mixed static and instance methods
TEST(InstanceMethodHandlerDispatcherTest, MixedStaticAndInstanceMethods) {
    const char* cpp = R"(
        namespace game {
            class Entity {
                void update() {}  // Instance
                static int getMaxEntities() { return 100; }  // Static
            };
        }
    )";
    // Verify: Only instance method handled by InstanceMethodHandler
}

// Test 12: Name mangling helper
TEST(InstanceMethodHandlerDispatcherTest, NameManglingHelper) {
    // Test getMangledName() directly
    // Verify: Correct name format for various scenarios
}

// Test 13: This parameter creation
TEST(InstanceMethodHandlerDispatcherTest, ThisParameterCreation) {
    // Test createThisParameter() directly
    // Verify: "struct ClassName* this" type and name
}
```

### 8. Migrate Old MethodHandler

**After InstanceMethodHandler is complete:**

**Option 1: Update old MethodHandler to use dispatcher (recommended)**
- Change `src/handlers/MethodHandler.cpp` to delegate to InstanceMethodHandler
- Update separator from `_` to `__`
- Keep same interface for backward compatibility
- Phase out old handler framework gradually

**Option 2: Document migration path**
- Keep old MethodHandler as-is (deprecated)
- Document in SUMMARY.md that new code should use InstanceMethodHandler
- Plan full migration in future phase

### 9. Update Registration Order

**Dispatcher registration order matters:**

```cpp
// In integration test or main transpiler
NamespaceHandler::registerWith(dispatcher);      // 1. Namespace paths first
TypeHandler::registerWith(dispatcher);            // 2. Type translation
RecordHandler::registerWith(dispatcher);          // 3. Struct/class definitions
FunctionHandler::registerWith(dispatcher);        // 4. Free functions
StaticMethodHandler::registerWith(dispatcher);    // 5. Static methods (no this)
InstanceMethodHandler::registerWith(dispatcher);  // 6. Instance methods (with this)
```

**Why this order:**
- NamespaceHandler must be first (provides namespace paths)
- RecordHandler creates struct definitions needed by method handlers
- StaticMethodHandler before InstanceMethodHandler (both need class context)

## Output Specification

### Files to Create

1. **include/dispatch/InstanceMethodHandler.h** (280-320 lines)
   - Class declaration
   - Complete Doxygen documentation
   - Translation examples
   - Helper method declarations (getMangledName, createThisParameter)

2. **src/dispatch/InstanceMethodHandler.cpp** (250-300 lines)
   - Implementation following StaticMethodHandler pattern + `this` parameter
   - Name mangling algorithm (same as static)
   - This parameter creation
   - Parameter translation delegation
   - Debug logging

3. **tests/unit/dispatch/InstanceMethodHandlerDispatcherTest.cpp** (800-900 lines)
   - 13 comprehensive test cases
   - Helper functions for AST building
   - Assertion macros for verification
   - This parameter verification

### Files to Modify

1. **CMakeLists.txt**
   - Add src/dispatch/InstanceMethodHandler.cpp to cpptoc_core
   - Add InstanceMethodHandlerDispatcherTest target

2. **src/handlers/MethodHandler.cpp** (optional - already updated with `!isStatic()`)
   - Already has complementary filter
   - Document migration path in comments

### Metadata Requirements

Create **SUMMARY.md** with:

```markdown
# InstanceMethodHandler Implementation Summary

## One-Liner
Implemented InstanceMethodHandler following Chain of Responsibility pattern to translate C++ instance methods to C free functions with explicit `this` parameter and `__` separator for scope resolution.

## Version
Version: Phase 1 (Complete Implementation)
Date: [DATE]
Author: Claude Sonnet 4.5

## Key Findings
- Instance methods translated as C free functions WITH `this` parameter
- Name mangling: `Namespace__ClassName__methodName` (same as static)
- First parameter: `struct ClassName* this`
- Complementary filter with StaticMethodHandler and VirtualMethodHandler
- All tests passing (13/13)

## Files Created
- include/dispatch/InstanceMethodHandler.h ([X] lines)
- src/dispatch/InstanceMethodHandler.cpp ([X] lines)
- tests/unit/dispatch/InstanceMethodHandlerDispatcherTest.cpp ([X] lines)

## Files Modified
- CMakeLists.txt (added source + test target)

## Decisions Made
1. **Separator:** Use `__` for all C++ scope resolution (matches project convention)
2. **This parameter:** Always first parameter, type `struct ClassName* this`
3. **Name mangling:** Identical to StaticMethodHandler (only difference is `this` param)
4. **Registration order:** After StaticMethodHandler (both need class context)
5. **Virtual methods:** Excluded (future VirtualMethodHandler)
6. **Parameter translation:** Delegate to ParameterHandler (follows Chain of Responsibility)
7. **Body translation:** Delegate to CompoundStmtHandler (follows FunctionHandler pattern)

## Blockers
None

## Next Steps
- VirtualMethodHandler for virtual methods (with vtable dispatch)
- Migration of old MethodHandler to use InstanceMethodHandler
- Real-world validation testing
```

## Success Criteria

### Completion Checklist

- [ ] InstanceMethodHandler.h created with complete documentation
- [ ] InstanceMethodHandler.cpp implements all required methods
- [ ] canHandle() uses exact type matching (`getKind()`)
- [ ] canHandle() filters out constructors, destructors, static, virtual
- [ ] canHandle() matches instance methods ONLY
- [ ] getMangledName() uses `__` separator consistently
- [ ] getMangledName() applies namespace prefix if present
- [ ] createThisParameter() creates `struct ClassName* this`
- [ ] handleInstanceMethod() follows StaticMethodHandler pattern + `this`
- [ ] This parameter is FIRST in parameter list
- [ ] Parameter translation delegates to ParameterHandler
- [ ] Body translation delegates to CompoundStmtHandler
- [ ] CMakeLists.txt updated with source and test target
- [ ] All 13 test cases written and passing
- [ ] Integration test verifies mixed static/instance methods
- [ ] No compiler warnings
- [ ] SUMMARY.md created with all required sections
- [ ] Build succeeds: `cmake --build build`
- [ ] Tests pass: `ctest -R InstanceMethodHandlerDispatcherTest`
- [ ] Code follows existing conventions (naming, formatting, comments)

### Test Verification

**Build:**
```bash
cd build
cmake --build . --target InstanceMethodHandlerDispatcherTest
```

**Run:**
```bash
ctest -R InstanceMethodHandlerDispatcherTest --output-on-failure
```

**Expected:** 100% tests passed, 0 tests failed out of 13

### Code Quality

- No TODOs or placeholders
- All edge cases handled
- Clear error messages with context
- Debug logging for verification
- Assertions for preconditions
- Comments explain "why" not "what"

## Implementation Notes

### Pattern Consistency

**FOLLOW StaticMethodHandler pattern EXACTLY + add `this`:**
1. File structure (header + implementation)
2. Method signatures (registerWith, canHandle, handle)
3. Documentation style (Doxygen comments)
4. Error handling (assertions + logging)
5. Mapper usage (DeclMapper, TypeMapper, StmtMapper, PathMapper)
6. **ONLY DIFFERENCE:** Add `this` parameter creation and insertion

### Key Difference from StaticMethodHandler

| Aspect | StaticMethodHandler | InstanceMethodHandler |
|--------|---------------------|------------------------|
| First parameter | NONE | `struct ClassName* this` |
| Filter | `isStatic() == true` | `isStatic() == false && !isVirtual()` |
| Name mangling | `ClassName__method` | `ClassName__method` (SAME) |
| Use case | Class-scoped functions | Object methods |

### Common Pitfalls (AVOID)

1. **Forgetting `this` parameter** - Instance methods MUST have `this`
   - ✓ Create: `createThisParameter()`
   - ✓ Add as first parameter

2. **Wrong `this` type** - Must be pointer to struct
   - ✓ Use: `struct ClassName*` NOT `ClassName*`

3. **Wrong parameter order** - `this` must be first
   - ✓ Use: `[this] + methodParams`

4. **Different name mangling** - Should be same as static
   - ✓ Use: Same `getMangledName()` as StaticMethodHandler

5. **Not excluding virtual methods** - Virtual needs different handling
   - ✓ Add: `if (method->isVirtual()) return false;`

### Debug Verification

**Check handler registration:**
```bash
# Should show InstanceMethodHandler processing
grep "InstanceMethodHandler" build/test_output.log
```

**Verify this parameter:**
```bash
# Search for "struct ClassName* this" pattern
grep "struct.*\* this" transpiled/output.h
```

**Verify name mangling:**
```bash
# Search for double underscore pattern
grep "__" transpiled/output.h
```

---

## References

- StaticMethodHandler: Pattern reference (add `this` parameter)
- FunctionHandler: Free function pattern
- RecordHandler: Class context and namespace handling
- NamespaceHandler: Namespace path computation
- CppToCVisitorDispatcher: Dispatcher architecture

---

**Ready to implement? Execute this prompt with the Task tool to create InstanceMethodHandler.**

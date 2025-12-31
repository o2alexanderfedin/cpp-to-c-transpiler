# StaticMethodHandler Implementation Prompt

## Objective

Implement StaticMethodHandler following the dispatcher Chain of Responsibility pattern to translate C++ static methods to C free functions with class name prefixing.

**Why this matters:**
- Static methods are class-scoped functions with NO `this` parameter
- Must apply class name prefix and namespace prefix (if applicable)
- Must integrate with existing dispatcher infrastructure
- Must use `__` separator consistently for all C++ scope resolution

## Context

### Referenced Files

Read these files to understand the established patterns:

**@include/dispatch/FunctionHandler.h** - Free function handler (COPY THIS STRUCTURE)
**@src/dispatch/FunctionHandler.cpp** - Free function implementation pattern
**@include/dispatch/RecordHandler.h** - Struct/class handler for context
**@src/dispatch/NamespaceHandler.cpp** - Namespace path computation
**@include/dispatch/CppToCVisitorDispatcher.h** - Dispatcher interface

### Dynamic Context

**!STATIC_METHOD_HANDLER_ANALYSIS.md** - Complete technical design and rationale
**!STATIC_METHOD_HANDLER_QUICK_REFERENCE.md** - Implementation checklist and common pitfalls
**!STATIC_METHOD_CODE_EXAMPLES.md** - 10 detailed translation examples

## Requirements

### 1. Create StaticMethodHandler Class

**File:** `include/dispatch/StaticMethodHandler.h`

**Structure:**
```cpp
namespace cpptoc {

class StaticMethodHandler {
public:
    // Registration
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    // Public helpers (for testing)
    static std::string getMangledName(
        const clang::CXXMethodDecl* method,
        const clang::CXXRecordDecl* classDecl
    );

private:
    // Predicate: Match static methods ONLY
    static bool canHandle(const clang::Decl* D);

    // Visitor: Translate static method to C function
    static void handleStaticMethod(
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
};

} // namespace cpptoc
```

**Documentation requirements:**
- Class-level Doxygen comment explaining responsibility
- Method-level Doxygen for all public methods
- Translation examples in header (C++ → C)
- Algorithm descriptions for canHandle and handleStaticMethod

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

    // Exclude constructors and destructors
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // Match static methods ONLY
    return method->isStatic();
}
```

**Why these checks:**
- `getKind() == CXXMethod` ensures exact type (not derived types)
- Exclude ctors/dtors (handled by dedicated handlers)
- `isStatic()` filter creates complementary partition with MethodHandler

### 3. Implement Name Mangling

**Name format:** `Namespace__ClassName__methodName`

**Separator rules:**
- `__` (double underscore) for ALL C++ scope resolution `::`
- Matches project convention:
  - NamespaceHandler: `A::B` → `A__B`
  - RecordHandler: `namespace A { struct S; }` → `A__S`
  - Nested structs: `Outer::Inner` → `Outer__Inner`

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
- `Counter::getValue()` → `Counter__getValue`
- `game::Entity::update()` → `game__Entity__update`
- `ns1::ns2::Math::add()` → `ns1__ns2__Math__add`

### 4. Implement handleStaticMethod()

**Algorithm (follow FunctionHandler pattern exactly):**

1. **Assert preconditions**
2. **Cast to CXXMethodDecl**
3. **Get class context:** `method->getParent()`
4. **Compute mangled name:** Use getMangledName()
5. **Translate return type:** Dispatch to TypeHandler
6. **Translate parameters:** Delegate to ParameterHandler (via translateParameters helper)
7. **Translate body:** Dispatch to CompoundStmtHandler, retrieve from StmtMapper
8. **Create C function:** Use CNodeBuilder::funcDecl()
9. **Add to C TranslationUnit:** Via PathMapper::getOrCreateTU()
10. **Register location:** PathMapper::setNodeLocation()
11. **Debug output:** Log translation for verification

**Key difference from FunctionHandler:**
- Get class context: `method->getParent()` instead of direct `getDeclContext()`
- Apply class name prefix in addition to namespace prefix
- NO `this` parameter (static methods are class-scoped free functions)

### 5. Parameter Translation

**Delegate to ParameterHandler:**
```cpp
static std::vector<clang::ParmVarDecl*> translateParameters(
    const clang::CXXMethodDecl* method,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    std::vector<clang::ParmVarDecl*> cParams;

    for (const auto* cppParam : method->parameters()) {
        // Dispatch to ParameterHandler
        bool handled = disp.dispatch(cppASTContext, cASTContext,
                                     const_cast<clang::ParmVarDecl*>(cppParam));

        if (!handled) {
            llvm::errs() << "[StaticMethodHandler] Error: No handler for parameter\n";
            continue;
        }

        // Retrieve from DeclMapper
        cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
        clang::Decl* cDecl = declMapper.getCreated(cppParam);

        if (!cDecl) {
            llvm::errs() << "[StaticMethodHandler] Error: Parameter not created\n";
            continue;
        }

        cParams.push_back(llvm::cast<clang::ParmVarDecl>(cDecl));
    }

    return cParams;
}
```

### 6. Update CMakeLists.txt

**Add source to cpptoc_core:**
```cmake
# Around line 200
set(CPPTOC_CORE_SOURCES
    # ... existing sources ...
    src/dispatch/StaticMethodHandler.cpp
)
```

**Add test target:**
```cmake
# After NamespaceHandlerDispatcherTest
add_executable(StaticMethodHandlerDispatcherTest
    tests/unit/dispatch/StaticMethodHandlerDispatcherTest.cpp
)

target_include_directories(StaticMethodHandlerDispatcherTest PRIVATE
    ${PROJECT_SOURCE_DIR}/include
    ${PROJECT_SOURCE_DIR}/tests/helpers
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(StaticMethodHandlerDispatcherTest PRIVATE
    cpptoc_core
    gtest
    gtest_main
    ${CLANG_LIBS}
    ${LLVM_LIBS}
)

gtest_discover_tests(StaticMethodHandlerDispatcherTest
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
    PROPERTIES LABELS "unit;dispatcher;static-method"
)
```

### 7. Write Comprehensive Tests

**File:** `tests/unit/dispatch/StaticMethodHandlerDispatcherTest.cpp`

**Required test cases:**

```cpp
// Test 1: Handler registration
TEST(StaticMethodHandlerDispatcherTest, Registration) {
    // Verify handler registers and processes static method
}

// Test 2: Simple static method
TEST(StaticMethodHandlerDispatcherTest, SimpleStaticMethod) {
    const char* cpp = R"(
        class Counter {
            static int getValue() { return 42; }
        };
    )";
    // Expected: int Counter__getValue(void) { return 42; }
}

// Test 3: Static method with parameters
TEST(StaticMethodHandlerDispatcherTest, StaticMethodWithParameters) {
    const char* cpp = R"(
        class Math {
            static int add(int a, int b) { return a + b; }
        };
    )";
    // Expected: int Math__add(int a, int b) { return a + b; }
}

// Test 4: Static method in namespace
TEST(StaticMethodHandlerDispatcherTest, StaticMethodInNamespace) {
    const char* cpp = R"(
        namespace game {
            class Entity {
                static int getMaxEntities() { return 100; }
            };
        }
    )";
    // Expected: int game__Entity__getMaxEntities(void) { return 100; }
}

// Test 5: Nested namespace
TEST(StaticMethodHandlerDispatcherTest, NestedNamespaceStaticMethod) {
    const char* cpp = R"(
        namespace ns1 {
            namespace ns2 {
                class Math {
                    static int multiply(int a, int b) { return a * b; }
                };
            }
        }
    )";
    // Expected: int ns1__ns2__Math__multiply(int a, int b) { return a * b; }
}

// Test 6: Reference parameter conversion
TEST(StaticMethodHandlerDispatcherTest, ReferenceParameterConversion) {
    const char* cpp = R"(
        class Formatter {
            static void format(const std::string& s);
        };
    )";
    // Expected: const pointer conversion (reference → pointer)
}

// Test 7: Exclude instance methods
TEST(StaticMethodHandlerDispatcherTest, IgnoresInstanceMethods) {
    const char* cpp = R"(
        class Counter {
            void increment() {}  // NOT static
        };
    )";
    // Verify: StaticMethodHandler does NOT handle this
}

// Test 8: Exclude constructors
TEST(StaticMethodHandlerDispatcherTest, IgnoresConstructors) {
    const char* cpp = R"(
        class Counter {
            Counter() {}
        };
    )";
    // Verify: StaticMethodHandler does NOT handle this
}

// Test 9: Both static and instance methods
TEST(StaticMethodHandlerDispatcherTest, MixedStaticAndInstanceMethods) {
    const char* cpp = R"(
        namespace game {
            class Entity {
                void update() {}  // Instance
                static int getMaxEntities() { return 100; }  // Static
            };
        }
    )";
    // Verify: Only static method handled by StaticMethodHandler
}

// Test 10: Name mangling helper
TEST(StaticMethodHandlerDispatcherTest, NameManglingHelper) {
    // Test getMangledName() directly
    // Verify: Correct name format for various scenarios
}
```

### 8. Integration Testing

**Update existing integration test:**
- Add static method test case to existing integration test suite
- Verify static methods work alongside instance methods
- Ensure no interference with MethodHandler

### 9. Update MethodHandler Filter

**File:** `src/handlers/MethodHandler.cpp`

**Add complementary filter to canHandle():**
```cpp
bool MethodHandler::canHandle(const clang::Decl* D) {
    // ... existing checks ...

    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);

    // CRITICAL: Exclude static methods (handled by StaticMethodHandler)
    if (method->isStatic()) {
        return false;
    }

    // ... rest of predicate ...
}
```

**Why:** Creates complementary partition - each method handled by exactly one handler.

## Output Specification

### Files to Create

1. **include/dispatch/StaticMethodHandler.h** (250-300 lines)
   - Class declaration
   - Complete Doxygen documentation
   - Translation examples
   - Helper method declarations

2. **src/dispatch/StaticMethodHandler.cpp** (180-220 lines)
   - Implementation following FunctionHandler pattern
   - Name mangling algorithm
   - Parameter translation delegation
   - Debug logging

3. **tests/unit/dispatch/StaticMethodHandlerDispatcherTest.cpp** (600-700 lines)
   - 10 comprehensive test cases
   - Helper functions for AST building
   - Assertion macros for verification

### Files to Modify

1. **CMakeLists.txt**
   - Add src/dispatch/StaticMethodHandler.cpp to cpptoc_core
   - Add StaticMethodHandlerDispatcherTest target

2. **src/handlers/MethodHandler.cpp**
   - Add `!method->isStatic()` filter to canHandle()

### Metadata Requirements

Create **SUMMARY.md** with:

```markdown
# StaticMethodHandler Implementation Summary

## One-Liner
Implemented StaticMethodHandler following Chain of Responsibility pattern to translate C++ static methods to C free functions with class and namespace prefixing using `__` separator.

## Version
Version: Phase 1 (Complete Implementation)
Date: [DATE]
Author: Claude Sonnet 4.5

## Key Findings
- Static methods translated as C free functions (NO `this` parameter)
- Name mangling: `Namespace__ClassName__methodName`
- Complementary filter with MethodHandler prevents collisions
- All tests passing (10/10)

## Files Created
- include/dispatch/StaticMethodHandler.h ([X] lines)
- src/dispatch/StaticMethodHandler.cpp ([X] lines)
- tests/unit/dispatch/StaticMethodHandlerDispatcherTest.cpp ([X] lines)

## Files Modified
- CMakeLists.txt (added source + test target)
- src/handlers/MethodHandler.cpp (added !isStatic() filter)

## Decisions Made
1. **Separator:** Use `__` for all C++ scope resolution (matches project convention)
2. **Registration order:** After NamespaceHandler, RecordHandler (needs namespace paths and class definitions)
3. **Parameter translation:** Delegate to ParameterHandler (follows Chain of Responsibility)
4. **Body translation:** Delegate to CompoundStmtHandler (follows FunctionHandler pattern)

## Blockers
None

## Next Steps
- Integration with MethodHandler for mixed static/instance methods
- Real-world validation testing
- Performance benchmarking
```

## Success Criteria

### Completion Checklist

- [ ] StaticMethodHandler.h created with complete documentation
- [ ] StaticMethodHandler.cpp implements all required methods
- [ ] canHandle() uses exact type matching (`getKind()`)
- [ ] canHandle() filters out constructors and destructors
- [ ] canHandle() matches `method->isStatic()` ONLY
- [ ] getMangledName() uses `__` separator consistently
- [ ] getMangledName() applies namespace prefix if present
- [ ] handleStaticMethod() follows FunctionHandler pattern exactly
- [ ] Parameter translation delegates to ParameterHandler
- [ ] Body translation delegates to CompoundStmtHandler
- [ ] CMakeLists.txt updated with source and test target
- [ ] MethodHandler updated with `!isStatic()` filter
- [ ] All 10 test cases written and passing
- [ ] Integration test verifies mixed static/instance methods
- [ ] No compiler warnings
- [ ] SUMMARY.md created with all required sections
- [ ] Build succeeds: `cmake --build build`
- [ ] Tests pass: `ctest -R StaticMethodHandlerDispatcherTest`
- [ ] Code follows existing conventions (naming, formatting, comments)

### Test Verification

**Build:**
```bash
cd build
cmake --build . --target StaticMethodHandlerDispatcherTest
```

**Run:**
```bash
ctest -R StaticMethodHandlerDispatcherTest --output-on-failure
```

**Expected:** 100% tests passed, 0 tests failed out of 10

### Code Quality

- No TODOs or placeholders
- All edge cases handled
- Clear error messages with context
- Debug logging for verification
- Assertions for preconditions
- Comments explain "why" not "what"

## Implementation Notes

### Pattern Consistency

**FOLLOW FunctionHandler pattern:**
1. File structure (header + implementation)
2. Method signatures (registerWith, canHandle, handle)
3. Documentation style (Doxygen comments)
4. Error handling (assertions + logging)
5. Mapper usage (DeclMapper, TypeMapper, StmtMapper, PathMapper)

### Common Pitfalls (AVOID)

1. **Using `isa<CXXMethodDecl>`** - Matches all derived types (ctors, dtors)
   - ✓ Use: `D->getKind() == Decl::CXXMethod`

2. **Forgetting to exclude ctors/dtors** - Leads to collisions
   - ✓ Add: `if (isa<CXXConstructorDecl>(m) || isa<CXXDestructorDecl>(m)) return false;`

3. **Wrong separator** - Using `_` instead of `__`
   - ✓ Use: `className + "__" + methodName`

4. **Adding `this` parameter** - Static methods don't have `this`
   - ✓ Only translate method parameters, no implicit `this`

5. **Direct C AST creation** - Bypassing mappers
   - ✓ Use: Dispatch to TypeHandler, ParameterHandler, CompoundStmtHandler

### Debug Verification

**Check handler registration:**
```bash
# Should show StaticMethodHandler processing
grep "StaticMethodHandler" build/test_output.log
```

**Verify name mangling:**
```bash
# Search for double underscore pattern
grep "__" transpiled/output.h
```

**Confirm no collisions:**
```bash
# No duplicate function definitions
grep "duplicate" build/compiler_errors.log
```

---

## References

- FunctionHandler: Pattern reference for free functions
- RecordHandler: Class context and namespace handling
- NamespaceHandler: Namespace path computation
- MethodHandler: Instance methods (complementary handler)
- CppToCVisitorDispatcher: Dispatcher architecture

---

**Ready to implement? Execute this prompt with the Task tool to create StaticMethodHandler.**

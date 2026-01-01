# NameMangler Refactoring Analysis

## Executive Summary

This document analyzes the current `NameMangler` implementation to understand what needs to be refactored to align with the handler chain pattern and SOLID principles. The current implementation is a monolithic class with 10 public methods handling name mangling for all C++ constructs. The target architecture follows the range-v3 pattern of composable, single-responsibility handlers.

---

## Current Implementation Analysis

### File Structure

**Header**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/NameMangler.h` (241 lines)
**Implementation**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/NameMangler.cpp` (618 lines)
**Tests**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/NameManglerTest.cpp` (842 lines, comprehensive)

### Class Structure

```cpp
class NameMangler {
private:
    clang::ASTContext &Ctx;                    // C++ AST context
    cpptoc::OverloadRegistry& registry_;       // Global overload tracking

public:
    // Constructor
    explicit NameMangler(clang::ASTContext &Ctx, cpptoc::OverloadRegistry& registry);

    // Public API (10 methods)
    std::string mangleName(clang::CXXMethodDecl *MD);
    std::string mangleConstructor(clang::CXXConstructorDecl *CD);
    std::string mangleDestructor(clang::CXXDestructorDecl *DD);
    std::string mangleConversionOperator(clang::CXXConversionDecl *CD);
    std::string mangleClassName(clang::CXXRecordDecl *RD);
    std::string mangleMethodName(clang::CXXMethodDecl *MD);
    std::string mangleFunctionName(clang::FunctionDecl *FD);
    std::string mangleStandaloneFunction(clang::FunctionDecl *FD);
    std::string mangleStaticMember(clang::CXXRecordDecl *RD, clang::VarDecl *VD);

private:
    // Helper methods (4)
    std::vector<std::string> extractNamespaceHierarchy(clang::Decl *D);
    std::string getAnonymousNamespaceID(clang::NamespaceDecl *ND);
    std::string getSimpleTypeName(clang::QualType T);
    std::string sanitizeOperatorName(clang::OverloadedOperatorKind Op);
};
```

### Key Responsibilities (Violations of SRP)

The `NameMangler` class currently handles:

1. **Class name mangling** - `mangleClassName()`
2. **Instance method mangling** - `mangleName()`, `mangleMethodName()`
3. **Constructor mangling** - `mangleConstructor()`
4. **Destructor mangling** - `mangleDestructor()`
5. **Conversion operator mangling** - `mangleConversionOperator()`
6. **Standalone function mangling** - `mangleFunctionName()`, `mangleStandaloneFunction()`
7. **Static member mangling** - `mangleStaticMember()`
8. **Namespace hierarchy extraction** - `extractNamespaceHierarchy()`
9. **Anonymous namespace ID generation** - `getAnonymousNamespaceID()`
10. **Type name simplification** - `getSimpleTypeName()`
11. **Operator name sanitization** - `sanitizeOperatorName()`
12. **Overload resolution** - via `OverloadRegistry` integration

**VIOLATION**: This is a "magic servlet" anti-pattern with 12 distinct responsibilities.

### Current Mangling Algorithm

#### Pattern Structure

```
Namespace_Class__NestedClass_methodName_paramType1_paramType2[_prefix|_postfix]
│         │     ││           │          │                      │
│         │     ││           │          │                      └─ Inc/Dec suffix
│         │     ││           │          └─ Parameter types (overloading)
│         │     ││           └─ Method name (or operator_xxx)
│         │     │└─ Double underscore (nested class separator)
│         │     └─ Nested class name
│         └─ Single underscore (namespace/class separator)
└─ Namespace prefix
```

#### Special Cases

1. **Namespaces**: Single underscore `_` separator
   - `ns1::ns2::func` → `ns1_ns2_func`

2. **Nested Classes**: Double underscore `__` separator
   - `Outer::Inner` → `Outer__Inner`
   - `ns::Outer::Inner::method` → `ns_Outer__Inner_method`

3. **Anonymous Namespaces**: `_anon_<basename>_<line>` pattern
   - `namespace { func; }` → `_anon_file_cpp_42_func`

4. **Constructors**: `__ctor` suffix with param count
   - `Point()` → `Point__ctor`
   - `Point(int, int)` → `Point__ctor_2`

5. **Destructors**: `__dtor` suffix (never overloaded)
   - `~Point()` → `Point__dtor`

6. **Static Members**: Double underscore `__` separator
   - `Counter::count` → `Counter__count`

7. **Operators**: Sanitized names
   - `operator[]` → `operator_indexer`
   - `operator++` (prefix) → `operator_increment_prefix`
   - `operator++` (postfix) → `operator_increment_postfix`

8. **Conversion Operators**: `operator_to_<targetType>[_const]`
   - `operator int()` → `MyClass_operator_to_int`
   - `operator bool() const` → `MyClass_operator_to_bool_const`

9. **extern "C"**: No mangling
   - `extern "C" void func()` → `func` (preserved)

10. **main()**: Never mangled
    - `int main()` → `main`

#### Type Encoding Algorithm

```cpp
std::string getSimpleTypeName(QualType T) {
    // Handles references FIRST (before const checking)
    if (T->isLValueReferenceType()) {
        T = T.getNonReferenceType();
        // Append _ref suffix
    }

    // Then check const qualification
    if (T.isConstQualified()) {
        result += "const_";
    }

    // Type mapping
    if (T->isIntegerType()) return "int";
    if (T->isFloatingType()) return "float";
    if (T->isPointerType()) {
        // RECURSIVE encoding (like Itanium ABI)
        return getSimpleTypeName(pointee) + "_ptr";
    }
    if (T->isRecordType()) return RD->getName().str();

    // References get suffix
    if (isReference) result += "_ref";
    if (isRValueRef) result += "_rref";

    return result;
}
```

**Examples**:
- `int` → `int`
- `const int&` → `const_int_ref`
- `int*` → `int_ptr`
- `char*` → `char_ptr` (NOT just "ptr" - fixes overload resolution)

### Dependencies

#### External Dependencies

1. **Clang AST Types**:
   - `clang::ASTContext` - Type queries, source location
   - `clang::CXXMethodDecl` - Method declarations
   - `clang::CXXRecordDecl` - Class declarations
   - `clang::CXXConstructorDecl` - Constructor declarations
   - `clang::CXXDestructorDecl` - Destructor declarations
   - `clang::CXXConversionDecl` - Conversion operators
   - `clang::FunctionDecl` - Standalone functions
   - `clang::VarDecl` - Static data members
   - `clang::NamespaceDecl` - Namespace declarations
   - `clang::QualType` - Type encoding

2. **Transpiler Components**:
   - `cpptoc::OverloadRegistry` - Cross-file overload tracking
   - `clang::SourceManager` - File location for anonymous namespaces
   - `llvm::Support/Path.h` - Filename extraction

#### Internal Dependencies

1. **extractNamespaceHierarchy()** - Used by all methods
2. **getSimpleTypeName()** - Used by overload-aware methods
3. **sanitizeOperatorName()** - Used by operator methods
4. **getAnonymousNamespaceID()** - Used by namespace extraction

#### Usage in Codebase

**Direct Usages** (20+ files):
- `src/dispatch/RecordHandler.cpp` - Class name mangling
- `src/dispatch/InstanceMethodHandler.cpp` - Method name mangling
- `src/dispatch/StaticMethodHandler.cpp` - Static method mangling
- `src/dispatch/VirtualMethodHandler.cpp` - Virtual method mangling
- `src/helpers/StaticMemberTranslator.cpp` - Static member mangling
- `src/SpecialOperatorTranslator.cpp` - Operator mangling
- `src/ComparisonOperatorTranslator.cpp` - Comparison operator mangling
- `src/ArithmeticOperatorTranslator.cpp` - Arithmetic operator mangling
- `src/TemplateMonomorphizer.cpp` - Template instantiation naming

**Test Files** (15+ files):
- `tests/NameManglerTest.cpp` - Comprehensive unit tests (842 lines)
- `tests/unit/helpers/NameManglerStaticMemberTest.cpp`
- Various integration tests

### Test Coverage

**Comprehensive Test Suite** (NameManglerTest.cpp):
- ✅ Simple class name: `MyClass` → `MyClass`
- ✅ Class method: `MyClass::method` → `MyClass_method`
- ✅ Namespace function: `ns::func` → `ns_func`
- ✅ Nested namespaces: `ns1::ns2::func` → `ns1_ns2_func`
- ✅ Namespace class method: `ns::MyClass::method` → `ns_MyClass_method`
- ✅ Anonymous namespace: `namespace { helper; }` → `_anon_<id>_helper`
- ✅ Anonymous namespace class: `namespace { InternalClass; }` → `_anon_<id>_InternalClass`
- ✅ Nested anonymous: `outer::namespace { helper; }` → `outer__anon_<id>_helper`
- ✅ Anonymous namespace method: `namespace { Helper::process; }` → `_anon_<id>_Helper_process`
- ✅ extern "C" in namespace: `namespace wrapper { extern "C" func; }` → `func` (unmangled)
- ✅ Deep nesting: `a::b::c::d::func` → `a_b_c_d_func`
- ✅ Static method: `utils::Helper::staticMethod` → `utils_Helper_staticMethod`
- ✅ Nested class: `ns::Outer::Inner` → contains `Inner`
- ✅ Constructors: `data::Buffer()` and `data::Buffer(int)` → distinct names
- ✅ Overloaded functions: `math::process(int)` vs `math::process(double)` → different
- ✅ Multiple namespaces: `ns1::func` vs `ns2::func` → `ns1_func` vs `ns2_func`
- ✅ C++17 nested syntax: `a::b::c::func` → `a_b_c_func`

**Total Test Count**: 17 comprehensive tests covering all major features

---

## Problems with Current Architecture

### 1. Violates Single Responsibility Principle (SRP)

**Problem**: One class handles 12 different responsibilities
- Class name mangling (with namespace support)
- Method name mangling (with overload resolution)
- Constructor/destructor mangling
- Function name mangling
- Static member mangling
- Operator name sanitization
- Type name encoding
- Namespace hierarchy extraction
- Anonymous namespace ID generation
- Overload registry integration
- extern "C" detection
- main() detection

**Impact**:
- Hard to understand which method to call for a given use case
- Changes to one mangling algorithm can affect others
- Testing requires understanding entire class
- New mangling patterns require modifying existing class

### 2. Violates Open/Closed Principle (OCP)

**Problem**: Adding new mangling patterns requires modifying `NameMangler` class

**Example**: To add C++20 modules support:
```cpp
// Would need to modify NameMangler.h
std::string mangleModuleName(clang::ModuleDecl *MD);  // NEW method

// Would need to modify NameMangler.cpp
std::string NameMangler::mangleModuleName(clang::ModuleDecl *MD) {
    // NEW implementation
}
```

**Impact**: Every new C++ feature requires changing core class

### 3. Method Name Confusion

**Problem**: Multiple methods do similar things with subtle differences:
- `mangleName()` - Instance methods with overload support
- `mangleMethodName()` - Methods with full namespace qualification
- `mangleFunctionName()` - Standalone functions (no overload handling)
- `mangleStandaloneFunction()` - Standalone functions WITH overload handling

**Which to use?**
- For method in namespaced class? `mangleMethodName()`
- For overloaded method? `mangleName()`
- For standalone function? `mangleFunctionName()` or `mangleStandaloneFunction()`?

**Impact**: Users need to study implementation to understand which method to call

### 4. Tight Coupling with OverloadRegistry

**Problem**: Every method directly accesses `registry_` member
```cpp
registry_.registerOverload(baseName, MD, mangledName);  // Scattered throughout
registry_.getMangledName(baseName, FD);
registry_.hasMultipleOverloads(baseName);
```

**Impact**:
- Can't use `NameMangler` without `OverloadRegistry`
- Harder to test individual mangling algorithms
- Cross-cutting concern mixed with domain logic

### 5. Mixed Abstraction Levels

**Problem**: Public methods mix high-level and low-level operations:
- High-level: `mangleClassName()`, `mangleMethodName()`
- Low-level: `getSimpleTypeName()`, `sanitizeOperatorName()`
- Mid-level: `extractNamespaceHierarchy()`

**Impact**: Unclear API surface - what's the public contract?

### 6. Duplicate Logic

**Problem**: Similar patterns repeated across methods:

**Namespace extraction** (appears in 5+ methods):
```cpp
std::vector<std::string> hierarchy = extractNamespaceHierarchy(D);
for (const auto &item : hierarchy) {
    if (item.substr(0, 3) == "ns:") {
        mangledName += item.substr(3) + "_";
    }
    // ...
}
```

**Type encoding for overloads** (appears in 3+ methods):
```cpp
for (ParmVarDecl *Param : MD->parameters()) {
    std::string paramType = getSimpleTypeName(Param->getType());
    mangledName += "_" + paramType;
}
```

**Impact**: Violates DRY principle, maintenance burden

---

## Target Architecture: Range-v3 Pattern

### Conceptual Model

The range-v3 library uses a **composable pipeline** pattern:

```cpp
// range-v3 example
auto result = data
    | views::filter(predicate)
    | views::transform(mapper)
    | views::take(10);
```

Each stage:
1. Has ONE responsibility (SRP)
2. Is independently testable
3. Can be composed with others
4. Has clear input/output contract

### Applying to NameMangler

**Current (Monolithic)**:
```cpp
NameMangler mangler(ctx, registry);
std::string name = mangler.mangleMethodName(MD);  // Does everything
```

**Target (Composable)**:
```cpp
// Each component has ONE responsibility
NamespaceExtractor nsExtractor;
TypeEncoder typeEncoder;
OverloadResolver overloadResolver;
NameBuilder nameBuilder;

// Compose them into pipeline
auto namePipeline =
    nsExtractor
    | typeEncoder
    | overloadResolver
    | nameBuilder;

std::string name = namePipeline(MD);
```

### Handler Chain Pattern

From `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/docs/architecture/02-handler-chain-pattern.md`:

```cpp
/**
 * @class ASTHandler
 * @brief Abstract base class for all C++ AST to C AST translation handlers
 *
 * Design Principles:
 * - Single Responsibility: Each handler translates ONE C++ construct
 * - Open/Closed: New handlers can be added without modifying existing ones
 * - Liskov Substitution: All handlers can be used interchangeably
 * - Interface Segregation: Only implement methods relevant to handler type
 * - Dependency Inversion: Depend on HandlerContext abstraction
 */
class ASTHandler {
public:
    virtual bool canHandle(const clang::Decl* D) const { return false; }
    virtual clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) {
        return nullptr;
    }
};
```

### Proposed NameMangler Handlers

```cpp
/**
 * @namespace cpptoc::mangling
 * @brief Name mangling components following Chain of Responsibility pattern
 */
namespace cpptoc::mangling {

// ============================================================================
// Base Interface
// ============================================================================

/**
 * @class ManglingHandler
 * @brief Base class for name mangling handlers
 *
 * Each handler is responsible for ONE aspect of name mangling.
 * Handlers can be composed to build complete mangled names.
 */
class ManglingHandler {
public:
    virtual ~ManglingHandler() = default;

    /**
     * @brief Check if this handler can mangle the given declaration
     * @param D Declaration to check
     * @return true if handler can process this declaration
     */
    virtual bool canHandle(const clang::Decl* D) const = 0;

    /**
     * @brief Generate mangled name component
     * @param D Declaration to mangle
     * @param ctx Mangling context (namespace info, type cache, etc.)
     * @return Mangled name component
     */
    virtual std::string mangle(const clang::Decl* D, ManglingContext& ctx) const = 0;
};

// ============================================================================
// Specialized Handlers (Each with ONE responsibility)
// ============================================================================

/**
 * @class NamespaceMangler
 * @brief Extracts and mangles namespace hierarchy
 *
 * Responsibility: Convert namespace hierarchy to prefix
 * Example: ns1::ns2::Class → "ns1_ns2"
 */
class NamespaceMangler : public ManglingHandler {
public:
    bool canHandle(const clang::Decl* D) const override;
    std::string mangle(const clang::Decl* D, ManglingContext& ctx) const override;
};

/**
 * @class ClassNameMangler
 * @brief Mangles class/struct names
 *
 * Responsibility: Handle class name component
 * Example: Point → "Point", Outer::Inner → "Outer__Inner"
 */
class ClassNameMangler : public ManglingHandler {
public:
    bool canHandle(const clang::Decl* D) const override;
    std::string mangle(const clang::Decl* D, ManglingContext& ctx) const override;
};

/**
 * @class MethodNameMangler
 * @brief Mangles instance method names
 *
 * Responsibility: Handle method name component (no overload resolution)
 * Example: getX → "getX", operator[] → "operator_indexer"
 */
class MethodNameMangler : public ManglingHandler {
public:
    bool canHandle(const clang::Decl* D) const override;
    std::string mangle(const clang::Decl* D, ManglingContext& ctx) const override;
};

/**
 * @class ConstructorMangler
 * @brief Mangles constructor names
 *
 * Responsibility: Generate constructor suffix
 * Example: Point() → "__ctor", Point(int, int) → "__ctor_2"
 */
class ConstructorMangler : public ManglingHandler {
public:
    bool canHandle(const clang::Decl* D) const override;
    std::string mangle(const clang::Decl* D, ManglingContext& ctx) const override;
};

/**
 * @class DestructorMangler
 * @brief Mangles destructor names
 *
 * Responsibility: Generate destructor suffix
 * Example: ~Point() → "__dtor"
 */
class DestructorMangler : public ManglingHandler {
public:
    bool canHandle(const clang::Decl* D) const override;
    std::string mangle(const clang::Decl* D, ManglingContext& ctx) const override;
};

/**
 * @class OverloadResolver
 * @brief Resolves overloaded names by appending parameter types
 *
 * Responsibility: Distinguish overloads via type encoding
 * Example: dot(Vector3D&) → "dot_const_Vector3D_ref"
 */
class OverloadResolver : public ManglingHandler {
private:
    TypeEncoder typeEncoder_;  // Delegate to TypeEncoder

public:
    bool canHandle(const clang::Decl* D) const override;
    std::string mangle(const clang::Decl* D, ManglingContext& ctx) const override;
};

/**
 * @class TypeEncoder
 * @brief Encodes C++ types to mangled form
 *
 * Responsibility: Convert QualType to string encoding
 * Example: const int& → "const_int_ref", char* → "char_ptr"
 */
class TypeEncoder {
public:
    std::string encode(clang::QualType T, clang::ASTContext& ctx) const;
};

/**
 * @class OperatorNameSanitizer
 * @brief Sanitizes operator names for C identifiers
 *
 * Responsibility: Convert operator symbols to valid C names
 * Example: operator[] → "operator_indexer", operator++ → "operator_increment"
 */
class OperatorNameSanitizer {
public:
    std::string sanitize(clang::OverloadedOperatorKind op, bool isPrefix = false) const;
};

/**
 * @class StaticMemberMangler
 * @brief Mangles static data member names
 *
 * Responsibility: Generate static member global variable name
 * Example: Counter::count → "Counter__count"
 */
class StaticMemberMangler : public ManglingHandler {
public:
    bool canHandle(const clang::Decl* D) const override;
    std::string mangle(const clang::Decl* D, ManglingContext& ctx) const override;
};

/**
 * @class AnonymousNamespaceMangler
 * @brief Generates unique IDs for anonymous namespaces
 *
 * Responsibility: Create deterministic unique names for anonymous namespaces
 * Example: namespace { func; } → "_anon_file_cpp_42"
 */
class AnonymousNamespaceMangler {
public:
    std::string generateID(const clang::NamespaceDecl* ND, clang::ASTContext& ctx) const;
};

// ============================================================================
// Composite Handler (Orchestration)
// ============================================================================

/**
 * @class CompositeManglingHandler
 * @brief Composes multiple mangling handlers into a pipeline
 *
 * Orchestrates handler chain to build complete mangled names.
 * Delegates to specialized handlers based on declaration type.
 */
class CompositeManglingHandler {
private:
    std::vector<std::unique_ptr<ManglingHandler>> handlers_;
    cpptoc::OverloadRegistry& registry_;  // For cross-file consistency

public:
    explicit CompositeManglingHandler(cpptoc::OverloadRegistry& registry);

    /**
     * @brief Add handler to chain
     */
    void addHandler(std::unique_ptr<ManglingHandler> handler);

    /**
     * @brief Generate mangled name for declaration
     * @param D Declaration to mangle
     * @param ctx AST context
     * @return Complete mangled name
     */
    std::string mangle(const clang::Decl* D, clang::ASTContext& ctx);
};

// ============================================================================
// Context for Sharing State
// ============================================================================

/**
 * @class ManglingContext
 * @brief Shared context passed between mangling handlers
 *
 * Provides:
 * - Namespace hierarchy cache
 * - Type encoding cache
 * - Anonymous namespace ID cache
 * - Overload registry access
 */
class ManglingContext {
private:
    clang::ASTContext& astCtx_;
    cpptoc::OverloadRegistry& registry_;

    // Caches
    std::map<const clang::Decl*, std::vector<std::string>> nsHierarchyCache_;
    std::map<clang::QualType, std::string> typeEncodeCache_;
    std::map<const clang::NamespaceDecl*, std::string> anonNsIDCache_;

public:
    ManglingContext(clang::ASTContext& ctx, cpptoc::OverloadRegistry& reg)
        : astCtx_(ctx), registry_(reg) {}

    clang::ASTContext& getASTContext() { return astCtx_; }
    cpptoc::OverloadRegistry& getRegistry() { return registry_; }

    // Cache access
    const std::vector<std::string>& getNamespaceHierarchy(const clang::Decl* D);
    std::string getTypeEncoding(clang::QualType T);
    std::string getAnonymousNamespaceID(const clang::NamespaceDecl* ND);
};

} // namespace cpptoc::mangling
```

---

## Refactoring Strategy

### Phase 1: Extract Core Components (Week 1)

**Goal**: Extract stateless helpers that don't depend on `OverloadRegistry`

1. **TypeEncoder** (from `getSimpleTypeName()`)
   - Input: `clang::QualType`, `clang::ASTContext`
   - Output: `std::string` (encoded type)
   - Dependencies: None (pure function)
   - Test: 15+ test cases for all type categories

2. **OperatorNameSanitizer** (from `sanitizeOperatorName()`)
   - Input: `clang::OverloadedOperatorKind`, `bool isPrefix`
   - Output: `std::string` (sanitized name)
   - Dependencies: None (pure function)
   - Test: 30+ test cases for all operators

3. **AnonymousNamespaceMangler** (from `getAnonymousNamespaceID()`)
   - Input: `clang::NamespaceDecl*`, `clang::ASTContext`
   - Output: `std::string` (unique ID)
   - Dependencies: `clang::SourceManager`, `llvm::Support/Path.h`
   - Test: 5+ test cases for various file locations

**Success Criteria**:
- 3 new classes created
- 50+ unit tests passing
- Original `NameMangler` tests still pass (using extracted components internally)

### Phase 2: Extract Namespace Processing (Week 2)

**Goal**: Extract namespace hierarchy logic

1. **NamespaceExtractor** (from `extractNamespaceHierarchy()`)
   - Input: `clang::Decl*`
   - Output: `std::vector<std::string>` (hierarchy with "ns:" and "rec:" prefixes)
   - Dependencies: `AnonymousNamespaceMangler`
   - Test: 10+ test cases for nested namespaces, anonymous namespaces, nested classes

**Success Criteria**:
- NamespaceExtractor class created
- 10+ unit tests passing
- Original `NameMangler` tests still pass

### Phase 3: Create ManglingHandler Interface (Week 3)

**Goal**: Define base interface and context

1. **ManglingHandler** (abstract base class)
   - `canHandle(const clang::Decl*)` - Predicate
   - `mangle(const clang::Decl*, ManglingContext&)` - Generate component

2. **ManglingContext** (shared state)
   - AST context access
   - Overload registry access
   - Caching for namespace hierarchy, type encoding, etc.

**Success Criteria**:
- Base interface defined
- Context class created
- Mock handler tests passing

### Phase 4: Extract Specialized Handlers (Week 4-5)

**Goal**: Convert each mangling method to a handler

1. **ClassNameMangler** (from `mangleClassName()`)
   - Dependencies: `NamespaceExtractor`
   - Test: 8+ test cases

2. **MethodNameMangler** (from `mangleName()`, `mangleMethodName()`)
   - Dependencies: `NamespaceExtractor`, `OperatorNameSanitizer`
   - Test: 12+ test cases

3. **ConstructorMangler** (from `mangleConstructor()`)
   - Dependencies: `NamespaceExtractor`
   - Test: 5+ test cases

4. **DestructorMangler** (from `mangleDestructor()`)
   - Dependencies: `NamespaceExtractor`
   - Test: 3+ test cases

5. **OverloadResolver** (from overload-aware methods)
   - Dependencies: `TypeEncoder`
   - Test: 10+ test cases

6. **StaticMemberMangler** (from `mangleStaticMember()`)
   - Dependencies: `NamespaceExtractor`
   - Test: 6+ test cases

**Success Criteria**:
- 6 new handler classes created
- 44+ unit tests passing
- Original `NameMangler` tests still pass

### Phase 5: Create Composite Handler (Week 6)

**Goal**: Orchestrate handlers into a unified API

1. **CompositeManglingHandler**
   - Maintains handler chain
   - Dispatches to appropriate handler
   - Integrates with `OverloadRegistry`

2. **Backward Compatibility Wrapper**
   - Keep `NameMangler` class as thin wrapper
   - Delegate to `CompositeManglingHandler`
   - Maintain existing API for gradual migration

**Success Criteria**:
- Composite handler created
- All 842 original tests pass
- Performance benchmarks show no regression

### Phase 6: Migrate Callers (Week 7-8)

**Goal**: Update codebase to use new handlers

1. **Update Handlers** (20+ files):
   - `RecordHandler.cpp`
   - `InstanceMethodHandler.cpp`
   - `StaticMethodHandler.cpp`
   - etc.

2. **Migration Strategy**:
   - Use `CompositeManglingHandler` directly
   - Remove dependency on old `NameMangler` API
   - One handler file per commit

**Success Criteria**:
- All 20+ handler files updated
- All integration tests pass
- No regressions in validation tests

### Phase 7: Deprecate Old API (Week 9)

**Goal**: Remove monolithic `NameMangler` class

1. **Remove old methods** from `NameMangler.h/cpp`
2. **Update documentation** to reference new handlers
3. **Final integration tests**

**Success Criteria**:
- Old `NameMangler` class removed
- All tests pass (100%)
- Documentation updated
- Git commit with clean diff

---

## Benefits of Refactoring

### 1. Single Responsibility (SRP) ✅

**Before**:
```cpp
NameMangler mangler(ctx, registry);  // Does 12 things
```

**After**:
```cpp
ClassNameMangler classMangler;      // Does 1 thing
MethodNameMangler methodMangler;    // Does 1 thing
OverloadResolver overloadResolver;  // Does 1 thing
```

### 2. Open/Closed (OCP) ✅

**Before**: Add C++20 modules support = modify `NameMangler`

**After**: Add new handler without touching existing code
```cpp
class ModuleNameMangler : public ManglingHandler {
    // New handler, zero changes to existing handlers
};
composite.addHandler(std::make_unique<ModuleNameMangler>());
```

### 3. Liskov Substitution (LSP) ✅

All handlers can be used interchangeably:
```cpp
void testHandler(ManglingHandler& handler, const clang::Decl* D) {
    if (handler.canHandle(D)) {
        std::string name = handler.mangle(D, ctx);  // Works with ANY handler
    }
}
```

### 4. Interface Segregation (ISP) ✅

Handlers only implement what they need:
```cpp
// TypeEncoder doesn't inherit from ManglingHandler (different concern)
class TypeEncoder {
    std::string encode(clang::QualType T);  // Just type encoding
};

// OperatorNameSanitizer doesn't need AST context
class OperatorNameSanitizer {
    std::string sanitize(OverloadedOperatorKind op);  // Just sanitization
};
```

### 5. Dependency Inversion (DIP) ✅

Handlers depend on abstractions:
```cpp
class MethodNameMangler : public ManglingHandler {
    std::string mangle(const clang::Decl* D, ManglingContext& ctx) {
        // Depend on ManglingContext interface, not concrete OverloadRegistry
        auto& registry = ctx.getRegistry();
    }
};
```

### 6. Testability ✅

Each component can be unit tested independently:
```cpp
TEST(TypeEncoderTest, EncodeConstReference) {
    TypeEncoder encoder;
    QualType T = /* const int& */;
    EXPECT_EQ(encoder.encode(T), "const_int_ref");
}

TEST(OperatorNameSanitizerTest, SanitizeSubscript) {
    OperatorNameSanitizer sanitizer;
    EXPECT_EQ(sanitizer.sanitize(OO_Subscript), "operator_indexer");
}
```

### 7. Composability ✅

Build complex mangling from simple components:
```cpp
// For namespaced overloaded method
auto name =
    namespaceMangler.mangle(D, ctx) + "_" +
    classMangler.mangle(D, ctx) + "_" +
    methodMangler.mangle(D, ctx) +
    overloadResolver.mangle(D, ctx);
```

### 8. Clarity ✅

**Before**: "Which method do I call for a namespaced overloaded method?"
- `mangleName()`?
- `mangleMethodName()`?

**After**: "I need namespace + class + method + overload components"
```cpp
composite.mangle(methodDecl, ctx);  // Automatically dispatches to correct handlers
```

---

## File Structure After Refactoring

### New Files to Create

```
include/mangling/
├── ManglingHandler.h               // Base interface
├── ManglingContext.h               // Shared context
├── CompositeManglingHandler.h      // Orchestrator
├── NamespaceMangler.h              // Namespace extraction
├── ClassNameMangler.h              // Class name component
├── MethodNameMangler.h             // Method name component
├── ConstructorMangler.h            // Constructor suffix
├── DestructorMangler.h             // Destructor suffix
├── OverloadResolver.h              // Overload resolution
├── StaticMemberMangler.h           // Static member names
├── TypeEncoder.h                   // Type encoding
├── OperatorNameSanitizer.h         // Operator sanitization
└── AnonymousNamespaceMangler.h     // Anonymous namespace IDs

src/mangling/
├── ManglingContext.cpp
├── CompositeManglingHandler.cpp
├── NamespaceMangler.cpp
├── ClassNameMangler.cpp
├── MethodNameMangler.cpp
├── ConstructorMangler.cpp
├── DestructorMangler.cpp
├── OverloadResolver.cpp
├── StaticMemberMangler.cpp
├── TypeEncoder.cpp
├── OperatorNameSanitizer.cpp
└── AnonymousNamespaceMangler.cpp

tests/unit/mangling/
├── TypeEncoderTest.cpp
├── OperatorNameSanitizerTest.cpp
├── AnonymousNamespaceManglerTest.cpp
├── NamespaceManglerTest.cpp
├── ClassNameManglerTest.cpp
├── MethodNameManglerTest.cpp
├── ConstructorManglerTest.cpp
├── DestructorManglerTest.cpp
├── OverloadResolverTest.cpp
├── StaticMemberManglerTest.cpp
└── CompositeManglingHandlerTest.cpp
```

### Files to Update

```
include/NameMangler.h               // Keep as backward-compatible wrapper
src/NameMangler.cpp                 // Delegate to CompositeManglingHandler

tests/NameManglerTest.cpp           // Keep for regression testing

// Update all callers (20+ files)
src/dispatch/RecordHandler.cpp
src/dispatch/InstanceMethodHandler.cpp
src/dispatch/StaticMethodHandler.cpp
src/dispatch/VirtualMethodHandler.cpp
src/helpers/StaticMemberTranslator.cpp
src/SpecialOperatorTranslator.cpp
src/ComparisonOperatorTranslator.cpp
src/ArithmeticOperatorTranslator.cpp
src/TemplateMonomorphizer.cpp
// ... (15+ more files)
```

---

## Migration Path for Callers

### Before (Current Usage)

```cpp
// In RecordHandler.cpp
cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
NameMangler mangler(const_cast<clang::ASTContext&>(cppASTContext), registry);

if (const auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(cppRecord)) {
    mangledName = mangler.mangleClassName(const_cast<clang::CXXRecordDecl*>(cxxRecord));
}
```

### After (New Handler Usage)

```cpp
// In RecordHandler.cpp
#include "mangling/CompositeManglingHandler.h"

cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
cpptoc::mangling::CompositeManglingHandler mangler(registry);

if (const auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(cppRecord)) {
    mangledName = mangler.mangle(cxxRecord, const_cast<clang::ASTContext&>(cppASTContext));
}
```

### Incremental Migration

**Option 1**: Keep `NameMangler` as wrapper (backward compatible)
```cpp
// NameMangler.h
class NameMangler {
private:
    CompositeManglingHandler composite_;

public:
    // Keep old API, delegate to composite
    std::string mangleClassName(clang::CXXRecordDecl *RD) {
        return composite_.mangle(RD, Ctx);
    }
};
```

**Option 2**: Deprecate old API, migrate incrementally
```cpp
// NameMangler.h
class NameMangler {
public:
    [[deprecated("Use CompositeManglingHandler::mangle() instead")]]
    std::string mangleClassName(clang::CXXRecordDecl *RD);
};
```

---

## Testing Strategy

### Unit Tests (Per Component)

Each new component gets comprehensive unit tests:

1. **TypeEncoder** (15+ tests):
   - Integer types: `int` → `"int"`
   - Floating types: `float` → `"float"`
   - Pointers: `int*` → `"int_ptr"`, `char*` → `"char_ptr"`
   - References: `const int&` → `"const_int_ref"`
   - R-value refs: `int&&` → `"int_rref"`
   - Const qualification: `const int` → `"const_int"`
   - Record types: `Point` → `"Point"`
   - Nested pointers: `int**` → `"int_ptr_ptr"`

2. **OperatorNameSanitizer** (30+ tests):
   - All arithmetic operators
   - All comparison operators
   - All bitwise operators
   - All assignment operators
   - Special operators (subscript, call, arrow, etc.)
   - Prefix vs postfix increment/decrement

3. **NamespaceMangler** (10+ tests):
   - Simple namespace: `ns::func`
   - Nested namespaces: `ns1::ns2::func`
   - Anonymous namespaces
   - C++17 nested syntax: `a::b::c::func`
   - Nested classes vs namespaces

### Integration Tests

Keep existing 842-line test suite as regression tests:
- All 17 comprehensive tests must pass
- Performance must not degrade
- Output must match exactly

### Test-Driven Development (TDD)

For each new component:
1. Write failing test
2. Implement minimal code to pass
3. Refactor while keeping tests green

---

## Key Differences from Current Implementation

### 1. Separation of Concerns

**Current**: Everything in one class
**Target**: Each concern is a separate class

### 2. Dependency Injection

**Current**: `NameMangler` owns `OverloadRegistry` reference
**Target**: `ManglingContext` provides registry access

### 3. Composability

**Current**: Fixed algorithm per method
**Target**: Compose handlers to build custom mangling strategies

### 4. Testability

**Current**: Must test through `NameMangler` API
**Target**: Test each component independently

### 5. Extensibility

**Current**: Modify `NameMangler` for new patterns
**Target**: Add new handler, register with composite

### 6. API Clarity

**Current**: 10 public methods with overlapping responsibilities
**Target**: 1 unified API (`composite.mangle()`) with clear dispatch

---

## Risk Assessment

### High Risk

1. **Breaking Changes to Callers** (20+ files)
   - Mitigation: Keep `NameMangler` as backward-compatible wrapper
   - Mitigation: Migrate one caller per commit with tests

2. **Performance Regression**
   - Current: Direct method calls
   - Target: Handler chain dispatch (virtual function calls)
   - Mitigation: Benchmark before/after
   - Mitigation: Cache heavily used paths

3. **Regression in Mangling Output**
   - Critical: Must produce identical output for existing code
   - Mitigation: Keep all 842 tests passing
   - Mitigation: Add integration tests for each handler

### Medium Risk

1. **Increased Complexity** (more files, more abstractions)
   - Mitigation: Comprehensive documentation
   - Mitigation: Clear examples for each handler

2. **Context Management**
   - `ManglingContext` becomes another global state holder
   - Mitigation: Clear ownership rules
   - Mitigation: Immutable caching where possible

### Low Risk

1. **Test Coverage** - Already excellent (842 lines)
2. **Understanding Current Behavior** - Well documented
3. **SOLID Principles** - Clear target architecture

---

## Success Criteria

### Must Have (Week 9)

1. ✅ All handlers extracted into separate classes
2. ✅ All 842 original tests pass
3. ✅ Performance benchmarks show <5% regression
4. ✅ All 20+ callers migrated
5. ✅ Documentation updated

### Should Have (Week 10)

1. ✅ 100+ new unit tests for individual components
2. ✅ Comprehensive handler documentation
3. ✅ Migration guide for future callers
4. ✅ Integration tests for handler composition

### Nice to Have (Future)

1. ⭕ Pluggable mangling strategies (e.g., Itanium ABI compatibility mode)
2. ⭕ Performance optimization via caching
3. ⭕ Handler registry for dynamic dispatch
4. ⭕ Metrics on handler usage

---

## Conclusion

The current `NameMangler` implementation is a classic "magic servlet" anti-pattern with 12 distinct responsibilities violating SRP. The refactoring to a handler chain pattern will:

1. **Improve Maintainability**: Each handler has ONE clear purpose
2. **Enable Extensibility**: Add new handlers without modifying existing code
3. **Enhance Testability**: Unit test individual components
4. **Increase Clarity**: Clear API with predictable behavior
5. **Follow SOLID**: All 5 principles satisfied

**Estimated Timeline**: 9 weeks
**Estimated Effort**: ~80 hours
**Risk Level**: Medium (mitigated by comprehensive tests)

**Recommendation**: Proceed with refactoring in 7 phases as outlined above.

---

## Appendix A: Current Method Signatures

```cpp
// From include/NameMangler.h

class NameMangler {
public:
    explicit NameMangler(clang::ASTContext &Ctx, cpptoc::OverloadRegistry& registry);

    // Instance methods (10 public methods)
    std::string mangleName(clang::CXXMethodDecl *MD);
    std::string mangleConstructor(clang::CXXConstructorDecl *CD);
    std::string mangleDestructor(clang::CXXDestructorDecl *DD);
    std::string mangleConversionOperator(clang::CXXConversionDecl *CD);
    std::string mangleClassName(clang::CXXRecordDecl *RD);
    std::string mangleMethodName(clang::CXXMethodDecl *MD);
    std::string mangleFunctionName(clang::FunctionDecl *FD);
    std::string mangleStandaloneFunction(clang::FunctionDecl *FD);
    std::string mangleStaticMember(clang::CXXRecordDecl *RD, clang::VarDecl *VD);

private:
    // Helper methods (4 private methods)
    std::vector<std::string> extractNamespaceHierarchy(clang::Decl *D);
    std::string getAnonymousNamespaceID(clang::NamespaceDecl *ND);
    std::string getSimpleTypeName(clang::QualType T);
    std::string sanitizeOperatorName(clang::OverloadedOperatorKind Op);
};
```

---

## Appendix B: Proposed Handler Interfaces

```cpp
// From proposed architecture

namespace cpptoc::mangling {

// Base interface
class ManglingHandler {
public:
    virtual ~ManglingHandler() = default;
    virtual bool canHandle(const clang::Decl* D) const = 0;
    virtual std::string mangle(const clang::Decl* D, ManglingContext& ctx) const = 0;
};

// Context
class ManglingContext {
public:
    ManglingContext(clang::ASTContext& ctx, cpptoc::OverloadRegistry& reg);
    clang::ASTContext& getASTContext();
    cpptoc::OverloadRegistry& getRegistry();
    const std::vector<std::string>& getNamespaceHierarchy(const clang::Decl* D);
    std::string getTypeEncoding(clang::QualType T);
    std::string getAnonymousNamespaceID(const clang::NamespaceDecl* ND);
};

// Specialized handlers (9 classes)
class NamespaceMangler : public ManglingHandler { /* ... */ };
class ClassNameMangler : public ManglingHandler { /* ... */ };
class MethodNameMangler : public ManglingHandler { /* ... */ };
class ConstructorMangler : public ManglingHandler { /* ... */ };
class DestructorMangler : public ManglingHandler { /* ... */ };
class OverloadResolver : public ManglingHandler { /* ... */ };
class StaticMemberMangler : public ManglingHandler { /* ... */ };

// Utility classes (3 classes)
class TypeEncoder { /* ... */ };
class OperatorNameSanitizer { /* ... */ };
class AnonymousNamespaceMangler { /* ... */ };

// Orchestrator
class CompositeManglingHandler {
public:
    explicit CompositeManglingHandler(cpptoc::OverloadRegistry& registry);
    void addHandler(std::unique_ptr<ManglingHandler> handler);
    std::string mangle(const clang::Decl* D, clang::ASTContext& ctx);
};

} // namespace cpptoc::mangling
```

---

## Appendix C: Example Usage Comparison

### Current (Monolithic)

```cpp
#include "NameMangler.h"

void translateMethod(clang::CXXMethodDecl* MD, clang::ASTContext& ctx) {
    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    NameMangler mangler(ctx, registry);

    // Which method to call? Need to study implementation
    // mangleName() vs mangleMethodName() vs ...?
    std::string name = mangler.mangleMethodName(MD);

    // Use name...
}
```

### Target (Composable)

```cpp
#include "mangling/CompositeManglingHandler.h"

void translateMethod(clang::CXXMethodDecl* MD, clang::ASTContext& ctx) {
    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    cpptoc::mangling::CompositeManglingHandler mangler(registry);

    // Clear API: one method, automatic dispatch
    std::string name = mangler.mangle(MD, ctx);

    // Use name...
}
```

---

**Document Version**: 1.0
**Author**: Analysis of current NameMangler implementation
**Date**: 2025-12-30
**Status**: Ready for Review

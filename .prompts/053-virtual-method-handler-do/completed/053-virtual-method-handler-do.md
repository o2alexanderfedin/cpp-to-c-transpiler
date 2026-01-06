# Prompt: Implement VirtualMethodHandler for Dispatcher Framework

## Objective

Implement a **VirtualMethodHandler** for the new dispatcher Chain of Responsibility framework that handles virtual methods (non-static, non-constructor, non-destructor) with COM-style vtable generation using strongly typed function pointers.

**Key Requirements:**
- Use NEW dispatcher framework (NOT old VtableGenerator)
- Follow COM/DCOM vtable design patterns
- Strongly typed function pointers (NO void* or generic casts)
- Compile-time type safety with static declarations
- Double underscore `__` separator for all naming
- 100% test coverage with TDD approach
- NO modifications to existing InstanceMethodHandler or StaticMethodHandler

## Context

### Existing Architecture

The codebase has:
1. **VtableGenerator.h/cpp** - OLD framework implementation (Phase 31)
2. **docs/VTABLE_IMPLEMENTATION.md** - Complete COM-style vtable documentation
3. **StaticMethodHandler** - Handles static methods (recently implemented, commit 505f372)
4. **InstanceMethodHandler** - Handles instance methods (recently implemented, commit b950845)

### Dispatcher Pattern

All new handlers follow this Chain of Responsibility pattern:

```cpp
class HandlerName {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);
private:
    static bool canHandle(const clang::Decl* D);
    static void handleXXX(...);
    // Helper methods
};
```

### COM-Style Vtable Pattern

From docs/VTABLE_IMPLEMENTATION.md (already implemented in old VtableGenerator):

```c
// Static declarations (compile-time type safety)
static void Shape__dtor(struct Shape *this);
static int Shape_getArea(struct Shape *this);

// Vtable structure (strongly typed function pointers)
struct Shape_vtable {
    const struct __class_type_info *type_info;  // RTTI
    void (*destructor)(struct Shape *this);
    int (*getArea)(struct Shape *this);
};

// Vtable instance initialization
static struct Shape_vtable Shape__vtable = {
    .type_info = &Shape__type_info,
    .destructor = Shape__dtor,
    .getArea = Shape_getArea
};

// Struct with vptr
struct Shape {
    const struct Shape_vtable *__vptr;  // Virtual pointer
};
```

## Requirements

### 1. Handler Registration and Predicates

**File:** `include/dispatch/VirtualMethodHandler.h`

```cpp
namespace cpptoc {

class VirtualMethodHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Decl* D);
    static void handleVirtualMethod(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );
    // Helper methods...
};

} // namespace cpptoc
```

**Predicate Logic (CRITICAL):**

```cpp
static bool canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Must be CXXMethodDecl (exact match, NOT derived types)
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);

    // Exclude constructors and destructors
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // Exclude static methods (handled by StaticMethodHandler)
    if (method->isStatic()) {
        return false;
    }

    // ONLY virtual methods (this is the key filter)
    return method->isVirtual();
}
```

**Complementary Filtering:**
- **StaticMethodHandler**: `isStatic() == true` (NO this, NO vtable)
- **InstanceMethodHandler**: `!isStatic() && !isVirtual()` (WITH this, NO vtable)
- **VirtualMethodHandler**: `!isStatic() && isVirtual()` (WITH this, WITH vtable)

### 2. Vtable Structure Generation

**Requirements:**
- Generate vtable struct for polymorphic classes
- Strongly typed function pointers (NOT void*)
- RTTI type_info pointer as first field
- Destructor always first in method list (Itanium ABI)
- Virtual methods in declaration order
- Handle inheritance correctly (override resolution)

**Expected Output:**

```c
// For: class Shape { virtual int getArea() = 0; virtual ~Shape() {} };

// Static declarations
static void Shape__dtor(struct Shape *this);
static int Shape_getArea(struct Shape *this);

// Vtable structure
struct Shape__vtable {
    const struct __class_type_info *type_info;
    void (*destructor)(struct Shape *this);
    int (*getArea)(struct Shape *this);
};
```

### 3. Vtable Instance Generation

**Requirements:**
- Generate static vtable instance with initializer
- Use designated initializers for clarity
- Compile-time type checking (static declarations ensure this)
- Correct override resolution for inheritance

**Expected Output:**

```c
// Vtable instance
static struct Shape__vtable Shape__vtable_instance = {
    .type_info = &Shape__type_info,
    .destructor = Shape__dtor,
    .getArea = Shape_getArea
};
```

### 4. Struct Member Addition

**Requirements:**
- Add `__vptr` member to struct for polymorphic classes
- Type: `const struct ClassName__vtable *__vptr`
- Always first member (before any fields)

**Expected Output:**

```c
struct Shape {
    const struct Shape__vtable *__vptr;
    // ... fields follow
};
```

### 5. Constructor Vtable Initialization

**Requirements:**
- In constructor body, initialize `this->__vptr = &ClassName__vtable_instance`
- Must happen BEFORE any other initialization
- Handle inheritance (set derived class vtable, not base)

**Expected Output:**

```c
void Circle__init(struct Circle *this, int radius) {
    this->__vptr = &Circle__vtable_instance;  // FIRST
    this->radius = radius;
}
```

### 6. Virtual Method Call Translation

**Requirements:**
- Translate `obj->method()` to `obj->__vptr->method(obj, ...)`
- Explicit this pointer as first argument
- Preserve argument types
- Handle multiple inheritance (thunk generation deferred)

**Expected Output:**

```c
// C++: shape->getArea()
// C:
int area = shape->__vptr->getArea(shape);
```

### 7. Name Mangling Convention

**CRITICAL:** All C++ scope resolution `::` uses `__` (double underscore):

```
Patterns:
- Namespace + class: namespace__ClassName
- Namespace + class + method: namespace__ClassName__methodName
- Nested namespace: ns1__ns2__ClassName
- Vtable struct: ClassName__vtable
- Vtable instance: ClassName__vtable_instance
- Virtual pointer: __vptr (fixed name)
- Destructor: ClassName__dtor
```

Examples:
```
game::Entity::update() → game__Entity__update
Shape::getArea() → Shape__getArea
Shape vtable → Shape__vtable
Shape vptr → __vptr (always this name)
```

### 8. Integration with Dispatcher

**Registration Order (CRITICAL):**

```cpp
// In dispatcher initialization
TypeHandler::registerWith(dispatcher);          // 1. Types first
NamespaceHandler::registerWith(dispatcher);     // 2. Scopes
ParameterHandler::registerWith(dispatcher);     // 3. Parameters
FunctionHandler::registerWith(dispatcher);      // 4. Free functions
RecordHandler::registerWith(dispatcher);        // 5. Structs/classes
StaticMethodHandler::registerWith(dispatcher);  // 6. Static methods
InstanceMethodHandler::registerWith(dispatcher); // 7. Instance methods
VirtualMethodHandler::registerWith(dispatcher); // 8. Virtual methods (NEW)
```

**Coordination:**
- VirtualMethodHandler runs AFTER RecordHandler creates struct
- VirtualMethodHandler adds `__vptr` field to existing struct
- VirtualMethodHandler delegates to TypeHandler for return types
- VirtualMethodHandler delegates to ParameterHandler for parameters
- VirtualMethodHandler uses NamespaceHandler for namespace prefixes

## Implementation Strategy

### Phase 1: Handler Infrastructure (TDD)

**Test:** `tests/unit/dispatch/VirtualMethodHandlerDispatcherTest.cpp`

1. **Test Registration:**
   - Verify handler registers with dispatcher
   - Verify canHandle() predicate logic
   - Verify exclusion of constructors, destructors, static methods, non-virtual methods

2. **Test Simple Virtual Method:**
   - C++ input: `class Shape { virtual int getArea() = 0; };`
   - Verify static declaration generated
   - Verify vtable struct generated
   - Verify vtable instance generated
   - Verify struct has `__vptr` field

3. **Test Virtual Method with Parameters:**
   - C++ input: `virtual void setPosition(int x, int y);`
   - Verify parameter translation
   - Verify function pointer signature correct
   - Verify static declaration matches

4. **Test Virtual Method in Namespace:**
   - C++ input: `namespace game { class Entity { virtual void update(); }; }`
   - Verify name mangling: `game__Entity__update`
   - Verify vtable name: `game__Entity__vtable`
   - Verify `__` separator everywhere

5. **Test Inheritance with Override:**
   - C++ input: `class Circle : public Shape { int getArea() override; };`
   - Verify Circle vtable has correct override
   - Verify correct method resolution
   - Verify type safety (matching signatures)

6. **Test Virtual Destructor:**
   - C++ input: `virtual ~Shape() {}`
   - Verify destructor is FIRST in vtable
   - Verify name mangling: `Shape__dtor`
   - Verify function pointer type: `void (*destructor)(struct Shape *this)`

7. **Test Pure Virtual Methods:**
   - C++ input: `virtual int getArea() = 0;`
   - Verify static declaration generated (even for pure virtual)
   - Verify vtable entry created
   - Note: Implementation can be placeholder (abstract class)

8. **Test Type Conversions:**
   - References → pointers: `virtual void setData(const int& value);` → `void (*setData)(struct Shape *this, const int* value)`
   - Verify all parameters converted correctly

9. **Test Exclusions:**
   - Non-virtual methods → handled by InstanceMethodHandler
   - Static methods → handled by StaticMethodHandler
   - Constructors → handled by ConstructorHandler
   - Destructors (non-virtual) → handled by DestructorHandler

10. **Test COM-Style Type Safety:**
    - Create test where signature intentionally mismatches
    - Verify C compiler catches error at vtable initialization
    - Document this in test comments

### Phase 2: Vtable Structure Generation

**Implementation Steps:**

1. **Analyze Class for Virtual Methods:**
   - Walk class hierarchy
   - Collect all virtual methods (including inherited)
   - Determine override relationships
   - Build vtable layout (destructor first, then methods in order)

2. **Generate Static Declarations:**
   ```cpp
   std::string generateStaticDeclarations(
       const clang::CXXRecordDecl* cppRecord,
       const std::vector<clang::CXXMethodDecl*>& virtualMethods,
       const std::string& className
   );
   ```
   - For each virtual method, generate: `static RetType ClassName__methodName(struct ClassName *this, params...);`
   - Special case destructor: `static void ClassName__dtor(struct ClassName *this);`

3. **Generate Vtable Struct:**
   ```cpp
   std::string generateVtableStruct(
       const clang::CXXRecordDecl* cppRecord,
       const std::vector<clang::CXXMethodDecl*>& virtualMethods,
       const std::string& className
   );
   ```
   - Create `struct ClassName__vtable { ... };`
   - First field: `const struct __class_type_info *type_info;`
   - Then strongly typed function pointers

4. **Generate Vtable Instance:**
   ```cpp
   std::string generateVtableInstance(
       const clang::CXXRecordDecl* cppRecord,
       const std::vector<clang::CXXMethodDecl*>& virtualMethods,
       const std::string& className
   );
   ```
   - Create `static struct ClassName__vtable ClassName__vtable_instance = { ... };`
   - Use designated initializers
   - Handle inheritance (resolve overrides)

### Phase 3: Struct Modification

**Implementation Steps:**

1. **Add Vptr Field to Struct:**
   - Retrieve struct RecordDecl from RecordHandler's DeclMapper
   - Create field: `const struct ClassName__vtable *__vptr;`
   - Insert as FIRST field (before existing fields)
   - Register in DeclMapper

2. **Coordinate with RecordHandler:**
   - RecordHandler creates struct shell
   - VirtualMethodHandler adds `__vptr` if polymorphic
   - Field order: `__vptr`, then regular fields

### Phase 4: Method Translation

**Implementation Steps:**

1. **Virtual Method Declaration:**
   - Same as InstanceMethodHandler (create FunctionDecl with this parameter)
   - Mark as `static` storage class
   - Register in DeclMapper

2. **Virtual Method Call Translation:**
   - Detect virtual call in ExpressionHandler
   - Transform: `obj->method(args)` → `obj->__vptr->method(obj, args)`
   - Note: ExpressionHandler integration deferred to Phase 5

3. **Constructor Vtable Initialization:**
   - In ConstructorHandler, add: `this->__vptr = &ClassName__vtable_instance;`
   - Must be FIRST statement in constructor body
   - Handle inheritance correctly

### Phase 5: Integration Testing

**Integration Tests:**

1. **Simple Virtual Class:**
   - Full translation from C++ to C
   - Compile generated C code
   - Verify vtable structure correct
   - Verify calls work correctly

2. **Inheritance Hierarchy:**
   - Base class with virtual methods
   - Derived class with overrides
   - Verify correct vtable per class
   - Verify override resolution

3. **Multiple Virtual Methods:**
   - Class with multiple virtual methods
   - Verify vtable order correct
   - Verify all methods callable

4. **Namespace + Virtual Methods:**
   - Virtual methods in namespaced classes
   - Verify `__` separator throughout
   - Verify no naming conflicts

## File Structure

```
include/dispatch/
  VirtualMethodHandler.h          (NEW, ~400 lines)

src/dispatch/
  VirtualMethodHandler.cpp        (NEW, ~500 lines)

tests/unit/dispatch/
  VirtualMethodHandlerDispatcherTest.cpp  (NEW, ~1200 lines, 13+ tests)

CMakeLists.txt
  Add VirtualMethodHandler.cpp to cpptoc_core
  Add VirtualMethodHandlerDispatcherTest to test targets
```

## Microsoft COM/DCOM References

From web search research:

**COM Vtable Structure:**
> "In C, MAPI objects are defined by creating a data structure and an array of ordered function pointers known as a virtual function table (vtable), where a pointer to the vtable must be the first member of the data structure with one pointer for every method in each interface supported by the object."
>
> "Each function in the list takes that interface pointer as its first parameter (this)."

**Binary Standard:**
> "For any given platform, COM defines a standard way to lay out virtual function tables (vtables) in memory, and a standard way to call functions through the vtables."

**Implementation Pattern:**
> "In C, an object appears as a structure whose first member is a pointer to the virtual function table (lpVtbl); that is, the first member points to an array containing function pointers."

**Key Principle:** Strongly typed function pointers with explicit static declarations for compile-time type safety.

## Success Criteria

✅ **Code Quality:**
- All 13+ tests passing (100% coverage)
- Zero compiler warnings
- Follows SOLID principles
- TDD red-green-refactor cycle documented

✅ **Functionality:**
- Virtual methods detected correctly
- Vtable structures generated with strongly typed pointers
- Static declarations generated for compile-time safety
- `__vptr` field added to polymorphic structs
- Vtable instances initialized correctly
- Name mangling uses `__` separator everywhere
- Inheritance and overrides handled correctly

✅ **Integration:**
- Handler registers with dispatcher
- Coordinates with RecordHandler for struct modification
- Delegates to TypeHandler for types
- Delegates to ParameterHandler for parameters
- Registration order correct (after RecordHandler)

✅ **Documentation:**
- All public methods documented
- Test cases document expected behavior
- COM pattern references cited
- SUMMARY.md created with key findings

## Output Location

Save all implementation files in the project, then create:

**File:** `.prompts/053-virtual-method-handler-do/SUMMARY.md`

**Structure:**
```markdown
# Virtual Method Handler Implementation Summary

**COM-style vtable generation with strongly typed function pointers integrated into dispatcher framework**

## Key Findings
• VirtualMethodHandler handles virtual methods (filters: !isStatic() && isVirtual())
• COM pattern: static declarations + strongly typed function pointers + compile-time safety
• Vtable structure: type_info + destructor (first) + methods (declaration order)
• Name mangling: all `::` → `__` (namespace__ClassName__methodName)
• Coordination: RecordHandler creates struct, VirtualMethodHandler adds __vptr

## Files Created
- include/dispatch/VirtualMethodHandler.h (~400 lines)
- src/dispatch/VirtualMethodHandler.cpp (~500 lines)
- tests/unit/dispatch/VirtualMethodHandlerDispatcherTest.cpp (~1200 lines, 13 tests)
- CMakeLists.txt (updated with new files)

## Test Results
- 13/13 VirtualMethodHandler tests passing
- Zero compiler warnings
- Zero linting errors
- Full TDD coverage (red-green-refactor)

## Decisions Needed
None - ready for use

## Blockers
None

## Next Step
Integrate VirtualMethodHandler registration in main dispatcher initialization
```

## Notes

- **DO NOT** modify existing InstanceMethodHandler or StaticMethodHandler
- **DO NOT** use old VtableGenerator code directly (reference for patterns only)
- **DO** follow exact dispatcher pattern from StaticMethodHandler/InstanceMethodHandler
- **DO** use COM-style static declarations for compile-time type safety
- **DO** use `__` separator for ALL C++ scope resolution
- **DO** follow TDD strictly (write test, see it fail, make it pass, refactor)
- **DO** run linters before completion

## Commit Message

```
feat(dispatch): Implement VirtualMethodHandler with COM-style vtables

- Add VirtualMethodHandler for new dispatcher framework
- Implement strongly typed vtable generation (COM/DCOM pattern)
- Generate static declarations for compile-time type safety
- Add __vptr field to polymorphic structs
- Use __ separator for all name mangling
- Handle inheritance and override resolution
- 13/13 tests passing, zero warnings

Follows Chain of Responsibility pattern established by StaticMethodHandler
and InstanceMethodHandler. Coordinates with RecordHandler for struct
modification and delegates to TypeHandler/ParameterHandler as needed.

References:
- Microsoft COM vtable design
- docs/VTABLE_IMPLEMENTATION.md
- StaticMethodHandler (commit 505f372)
- InstanceMethodHandler (commit b950845)
```

---

**IMPORTANT:** This is a comprehensive "Do" prompt. Execute the full implementation with TDD, create all files, ensure 100% test coverage, run linters, and create SUMMARY.md documenting the results.

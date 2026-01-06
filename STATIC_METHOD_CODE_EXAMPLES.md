# Static Method Handler - Code Examples

## Example 1: Simple Static Method

### C++ Input
```cpp
class Counter {
public:
    static int getVersion() {
        return 1;
    }
};
```

### Handler Flow

**1. Dispatcher Routes to StaticMethodHandler**
```
dispatch(Counter::getVersion CXXMethodDecl)
  ↓
TypeHandler.canHandle()? No
FunctionHandler.canHandle()? No (it's CXXMethodDecl, not FunctionDecl)
RecordHandler.canHandle()? No
MethodHandler.canHandle()? No (isStatic() == true, excluded)
StaticMethodHandler.canHandle()? YES ✓
  → StaticMethodHandler.handleStaticMethod()
```

**2. canHandle() Evaluation**
```cpp
bool StaticMethodHandler::canHandle(const clang::Decl* D) {
    assert(D);

    // getVersion is CXXMethod, not CXXConstructor or CXXDestructor
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);

    // Not constructor/destructor
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // IS static
    return method->isStatic();  // ✓ Returns true
}
```

**3. handleStaticMethod() Translation**
```cpp
void StaticMethodHandler::handleStaticMethod(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    const auto* cppMethod = llvm::cast<clang::CXXMethodDecl>(D);

    // Step 1: Extract properties
    std::string methodName = "getVersion";
    std::string className = "Counter";

    // Step 2: Check for namespace (none in this case)
    const auto* classDecl = cppMethod->getParent();  // CXXRecordDecl for Counter
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
            classDecl->getDeclContext())) {
        // Not in namespace, skip
    }

    // Step 3: Mangle name
    std::string mangledName = "Counter__getVersion";

    // Step 4: Translate return type
    clang::QualType cppReturnType = cppMethod->getReturnType();  // int
    const clang::Type* cppReturnTypePtr = cppReturnType.getTypePtr();
    disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Type*>(cppReturnTypePtr));
    clang::QualType cReturnType = disp.getTypeMapper().getCreated(cppReturnTypePtr);
    // cReturnType = int (no conversion needed)

    // Step 5: Get parameters
    std::vector<clang::ParmVarDecl*> cParams = translateParameters(...);
    // No parameters in this case, returns empty vector

    // Step 6: Get body
    clang::CompoundStmt* cBody = nullptr;
    if (cppMethod->hasBody()) {
        // Translate body (dispatch to StmtMapper)
        // For now, simplified
    }

    // Step 7: Create C function
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(
        "Counter__getVersion",
        cReturnType,  // int
        cParams,      // empty
        cBody         // nullptr for Phase 1
    );

    // Step 8: Add to C TranslationUnit
    std::string targetPath = disp.getTargetPath(cppASTContext, D);
    clang::TranslationUnitDecl* cTU = disp.getPathMapper().getOrCreateTU(targetPath);
    cFunc->setDeclContext(cTU);
    cTU->addDecl(cFunc);

    // Step 9: Register location
    disp.getPathMapper().setNodeLocation(cFunc, targetPath);

    llvm::outs() << "[StaticMethodHandler] Translated: getVersion → Counter__getVersion\n";
}
```

### C Output
```c
int Counter__getVersion(void);
```

---

## Example 2: Static Method with Parameters

### C++ Input
```cpp
class Math {
public:
    static int add(int a, int b) {
        return a + b;
    }
};
```

### Handler Flow (Abbreviated)

**canHandle():** Returns true (isStatic() == true)

**handleStaticMethod():**
```
1. methodName = "add", className = "Math"
2. No namespace
3. mangledName = "Math__add"
4. Return type: int → int
5. Parameters:
   - Dispatch ParmVarDecl for 'a' → ParameterHandler → creates int a
   - Dispatch ParmVarDecl for 'b' → ParameterHandler → creates int b
   - Result: [int a, int b]
6. Create C function: int Math__add(int a, int b)
```

### C Output
```c
int Math__add(int a, int b);
```

---

## Example 3: Static Method in Namespace

### C++ Input
```cpp
namespace engine {
    class Renderer {
    public:
        static void initialize() {
            // Implementation
        }
    };
}
```

### Handler Flow (Key Steps)

**1. Dispatcher routes through:**
- TranslationUnitHandler → processes namespace
- NamespaceHandler → processes namespace, recurses on children
- Dispatcher sees Renderer CXXRecordDecl → RecordHandler
- RecordHandler translates Renderer struct
- RecordHandler processes children → sees initialize static method
- Dispatcher routes initialize to StaticMethodHandler

**2. canHandle() Path:**
```cpp
// D is CXXMethodDecl for initialize
// isStatic() == true
// Not constructor/destructor
→ Returns true
```

**3. handleStaticMethod() Translation:**
```cpp
// Extract class parent
const auto* classDecl = cppMethod->getParent();  // CXXRecordDecl "Renderer"

// Check if in namespace
if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
        classDecl->getDeclContext())) {
    // classDecl->getDeclContext() = NamespaceDecl "engine"
    std::string nsPath = NamespaceHandler::getNamespacePath(ns);  // "engine"
    className = "engine__Renderer";  // Double underscore for namespace
}

// Mangle name
std::string mangledName = "engine__Renderer_initialize";  // NS__Class_method

// Create C function: void engine__Renderer_initialize(void)
```

### C Output
```c
void engine__Renderer_initialize(void);
```

---

## Example 4: Static Method with Reference Parameters

### C++ Input
```cpp
class Processor {
public:
    static void process(const int& value) {
        // Use value
    }
};
```

### Handler Flow (Parameter Translation)

**1. Parameter dispatch:**
```cpp
// In handleStaticMethod(), call translateParameters()
for (const auto* cppParam : method->parameters()) {
    // cppParam: ParmVarDecl "value" with type "const int&"

    // Dispatch to ParameterHandler
    disp.dispatch(cppASTContext, cASTContext, cppParam);

    // ParameterHandler:
    // 1. Extracts type: const int& (reference)
    // 2. Dispatches type to TypeHandler
    // 3. TypeHandler converts reference → pointer: const int*
    // 4. Creates ParmVarDecl with const int* type
    // 5. Stores mapping in DeclMapper

    // Retrieve created parameter
    clang::ParmVarDecl* cParam = disp.getDeclMapper().getCreated(cppParam);
    // cParam: "value" with type "const int*"

    cParams.push_back(cParam);
}
```

### C Output
```c
void Processor_process(const int* value);
```

---

## Example 5: Class with Both Static and Instance Methods

### C++ Input
```cpp
class GameEntity {
private:
    int health;

public:
    void takeDamage(int amount) {
        health -= amount;
    }

    static int getMaxHealth() {
        return 100;
    }
};
```

### Handler Routing

**RecordHandler processes GameEntity:**
1. Creates `struct GameEntity { int health; }`
2. Finds child declarations
3. Finds takeDamage method → dispatches
4. Finds getMaxHealth method → dispatches

**Dispatcher routes takeDamage:**
```
canHandle() evaluations:
→ MethodHandler.canHandle():
    - Is CXXMethodDecl? YES
    - isStatic()? NO
    - Is constructor? NO
    - Is destructor? NO
    → Returns true ✓
→ Handled by MethodHandler
  - Creates: void GameEntity__takeDamage(struct GameEntity* this, int amount)
```

**Dispatcher routes getMaxHealth:**
```
canHandle() evaluations:
→ MethodHandler.canHandle():
    - Is CXXMethodDecl? YES
    - isStatic()? YES
    → Returns false (excludes static) ✗
→ StaticMethodHandler.canHandle():
    - Is CXXMethodDecl? YES
    - isStatic()? YES
    - Is constructor? NO
    - Is destructor? NO
    → Returns true ✓
→ Handled by StaticMethodHandler
  - Creates: int GameEntity__getMaxHealth(void)
```

### C Output
```c
struct GameEntity {
    int health;
};

void GameEntity__takeDamage(struct GameEntity* this, int amount);
int GameEntity__getMaxHealth(void);
```

**Key Observation:** MethodHandler adds 'this' parameter, StaticMethodHandler doesn't.

---

## Example 6: Nested Namespace

### C++ Input
```cpp
namespace io {
    namespace network {
        class Connection {
        public:
            static void connect(const char* host) {
                // Implementation
            }
        };
    }
}
```

### Name Mangling

**Step 1: Get namespace path**
```cpp
const auto* classDecl = cppMethod->getParent();  // Connection
const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
    classDecl->getDeclContext());  // network namespace

std::string nsPath = NamespaceHandler::getNamespacePath(ns);
// Walks parent contexts: network → io
// Reverses: io, network
// Joins with "__": "io__network"
```

**Step 2: Apply to class name**
```cpp
std::string className = classDecl->getNameAsString();  // "Connection"
className = nsPath + "__" + className;  // "io__network__Connection"
```

**Step 3: Mangle method name**
```cpp
std::string methodName = cppMethod->getNameAsString();  // "connect"
std::string mangledName = className + "_" + methodName;
// "io__network__Connection_connect"
```

### C Output
```c
void io__network__Connection_connect(const char* host);
```

---

## Example 7: Complementary Filtering (No Collision)

### C++ Input
```cpp
class MyClass {
    void instanceMethod() {}        // Instance method
    static void staticMethod() {}   // Static method
};
```

### Handler Predicate Evaluation

**For instanceMethod:**
```cpp
// MethodHandler.canHandle()
const auto* m = llvm::dyn_cast<clang::CXXMethodDecl>(D);
if (!m) return false;  // IS CXXMethodDecl

if (llvm::isa<clang::CXXConstructorDecl>(m) ||
    llvm::isa<clang::CXXDestructorDecl>(m)) {
    return false;  // Is neither
}

return !m->isStatic();  // Returns true (!false = true) ✓
→ MethodHandler handles instanceMethod

// StaticMethodHandler.canHandle()
if (D->getKind() != clang::Decl::CXXMethod) {
    return false;  // IS CXXMethod
}

if (llvm::isa<clang::CXXConstructorDecl>(m) ||
    llvm::isa<clang::CXXDestructorDecl>(m)) {
    return false;  // Is neither
}

return m->isStatic();  // Returns false (!true = false) ✗
→ StaticMethodHandler skips instanceMethod
```

**For staticMethod:**
```cpp
// MethodHandler.canHandle()
return !m->isStatic();  // Returns false (!(true) = false) ✗
→ MethodHandler skips staticMethod

// StaticMethodHandler.canHandle()
return m->isStatic();  // Returns true ✓
→ StaticMethodHandler handles staticMethod
```

**Result:**
- Each method is handled by exactly one handler
- No duplication, no conflicts

### C Output
```c
void MyClass_instanceMethod(struct MyClass* this);
void MyClass_staticMethod(void);
```

---

## Example 8: Type Conversions in Static Methods

### C++ Input
```cpp
class Container {
public:
    static Container& getInstance() {
        static Container instance;
        return instance;
    }
};
```

### Type Translation Flow

**1. Return type analysis**
```cpp
clang::QualType cppReturnType = cppMethod->getReturnType();
// cppReturnType = "Container&" (LValueReferenceType)

const clang::Type* cppReturnTypePtr = cppReturnType.getTypePtr();

// Step 2: Dispatch to TypeHandler
disp.dispatch(cppASTContext, cASTContext,
              const_cast<clang::Type*>(cppReturnTypePtr));

// TypeHandler processes:
// - Detects LValueReferenceType
// - Converts to PointerType
// - Stores mapping: Container& → Container*

// Step 3: Retrieve translated type
clang::QualType cReturnType = disp.getTypeMapper().getCreated(cppReturnTypePtr);
// cReturnType = "Container*" (PointerType)
```

**2. Function creation**
```cpp
clang::CNodeBuilder builder(cASTContext);
clang::FunctionDecl* cFunc = builder.funcDecl(
    "Container_getInstance",
    cReturnType,  // struct Container* (translated from Container&)
    cParams,      // empty
    nullptr       // body
);
```

### C Output
```c
struct Container* Container_getInstance(void);
```

---

## Example 9: Parameter Direction Guide

### Decision Tree for Method Dispatch

```
Is it a CXXMethodDecl?
├─ NO → Not our job (other handlers)
│
└─ YES → Check kind()
    ├─ CXXConstructorDecl → ConstructorHandler
    ├─ CXXDestructorDecl → DestructorHandler
    │
    └─ Regular CXXMethodDecl → Check isStatic()
        ├─ isStatic() == false → MethodHandler
        │   (adds 'this' parameter)
        │   (Signature: ClassName_method(struct ClassName* this, ...))
        │
        └─ isStatic() == true → StaticMethodHandler
            (NO 'this' parameter)
            (Signature: ClassName_method(...))
```

---

## Example 10: Registration Order Impact

### Correct Order
```cpp
// Initialization code
void initializeDispatchers(CppToCVisitorDispatcher& disp) {
    TypeHandler::registerWith(disp);              // 1. Types must come first
    NamespaceHandler::registerWith(disp);         // 2. Scope tracking
    ParameterHandler::registerWith(disp);         // 3. Parameters depend on types
    FunctionHandler::registerWith(disp);          // 4. Functions
    RecordHandler::registerWith(disp);            // 5. Structs/classes
    MethodHandler::registerWith(disp);            // 6. Instance methods
    StaticMethodHandler::registerWith(disp);      // 7. Static methods last
}

// Why? Each handler uses outputs from handlers registered before it
// TypeHandler output → used by FunctionHandler, RecordHandler, MethodHandler, StaticMethodHandler
// NamespaceHandler output → used by FunctionHandler, MethodHandler, StaticMethodHandler
// ParameterHandler output → used by FunctionHandler, MethodHandler, StaticMethodHandler
// etc.
```

### Wrong Order (Would Fail)
```cpp
void wrongInit(CppToCVisitorDispatcher& disp) {
    StaticMethodHandler::registerWith(disp);     // ✗ TOO EARLY
    MethodHandler::registerWith(disp);           // Type translation not available yet
    RecordHandler::registerWith(disp);
    FunctionHandler::registerWith(disp);
    ParameterHandler::registerWith(disp);
    NamespaceHandler::registerWith(disp);
    TypeHandler::registerWith(disp);

    // Result: StaticMethodHandler tries to use TypeMapper
    // but TypeHandler hasn't registered yet → null mappings!
}
```

---

## Summary

These examples demonstrate:

1. **Consistent Pattern:** All handlers follow same registerWith/canHandle/handle pattern
2. **Proper Routing:** Dispatcher correctly routes static vs instance methods
3. **Type Handling:** Types are translated before function creation
4. **Name Mangling:** Namespace and class prefixes applied correctly
5. **No This Parameter:** Static methods have no 'this' parameter
6. **Complementary Filtering:** No overlap between MethodHandler and StaticMethodHandler
7. **Registration Order:** Each handler depends on outputs from previously registered handlers


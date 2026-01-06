# Handler Implementation Order

## Overview

This document defines the exact order to implement the 9 specialized handlers, including progressive implementation across multiple phases and dependency management. Each handler starts simple and gains functionality in later phases.

**Total Handlers:** 9 core handlers
**Implementation Approach:** Progressive - start basic, add features incrementally
**Parallelization:** Identified where handlers can be built concurrently

---

## Handler 1: FunctionHandler

### Responsibility
Translate C++ function declarations and definitions to C functions.

### Implementation Phases

#### Phase 1: Basic Standalone Functions
**Features:**
- Simple function declarations (`int foo();`)
- Function definitions with body
- Parameter translation (simple types: int, float, double, char)
- Return type handling (simple types)
- No overloading, no defaults, no templates

**Methods to implement:**
- `canHandle(Decl*)` - Check if it's a FunctionDecl (not method)
- `handleFunctionDecl(FunctionDecl*)` - Create C FunctionDecl
- `translateParameters(FunctionDecl*)` - Convert parameter list
- `translateReturnType(QualType)` - Convert return type
- `translateBody(Stmt*)` - Delegate to StatementHandler

**LOC:** 200-300
**Effort:** 3-4 hours

#### Phase 5: Reference Parameters
**Features:**
- Reference parameters (`int&`) → pointers (`int*`)
- Const references (`const int&`) → const pointers
- Update call sites to pass addresses

**Methods to add:**
- `translateReferenceParam(ParmVarDecl*)` - Convert reference to pointer
- `rewriteCallSite(CallExpr*)` - Add `&` for reference arguments

**Additional LOC:** +100-150
**Effort:** 2-3 hours

#### Phase 7: Function Overloading (if needed)
**Features:**
- Name mangling for overloaded functions
- Type-based name suffix generation

**Methods to add:**
- `mangleFunctionName(FunctionDecl*)` - Create unique name
- `generateTypeSignature(FunctionDecl*)` - Type-based suffix

**Additional LOC:** +100-150
**Effort:** 2-3 hours

#### Phase 12: Namespace Prefix
**Features:**
- Add namespace prefix to function names

**Methods to add:**
- Integration with NamespaceHandler for name generation

**Additional LOC:** +50-100
**Effort:** 1-2 hours

### Total Implementation
**LOC:** 450-700
**Effort:** 8-12 hours
**Complexity:** 2/5

### Dependencies
- **Phase 1:** StatementHandler (for body translation), ExpressionHandler (for return values)
- **Phase 5:** TypeTranslator (for reference → pointer conversion)
- **Phase 12:** NamespaceHandler (for namespace prefixing)

### Can Parallelize With
- VariableHandler (they don't depend on each other in Phase 1)

### Test Coverage Target
**Unit tests:** 30-40 tests
- Empty function, with params, with return, with body
- Reference parameters
- Inline functions, static functions
- Overloaded functions (if supported)

---

## Handler 2: VariableHandler

### Responsibility
Translate C++ variable declarations (local, global, static) to C variable declarations.

### Implementation Phases

#### Phase 1: Local Variables
**Features:**
- Local variable declarations
- Initialization expressions
- Simple types (int, float, double, char)

**Methods to implement:**
- `canHandle(Decl*)` - Check if it's a VarDecl
- `handleVarDecl(VarDecl*)` - Create C VarDecl
- `translateType(QualType)` - Delegate to TypeTranslator
- `translateInitExpr(Expr*)` - Delegate to ExpressionHandler

**LOC:** 150-200
**Effort:** 2-3 hours

#### Phase 3: Global and Static Variables
**Features:**
- Global variable declarations
- Static local variables
- Storage class handling (static, extern)
- Array declarations

**Methods to add:**
- `handleGlobalVar(VarDecl*)` - Handle global scope
- `handleStaticLocal(VarDecl*)` - Handle static keyword
- `handleArrayDecl(VarDecl*)` - Handle array types

**Additional LOC:** +150-200
**Effort:** 2-3 hours

#### Phase 4: Struct Member Variables (FieldDecl)
**Features:**
- Field declarations within structs
- Handled by RecordHandler, but VariableHandler provides type translation

**Methods to add:**
- Helper methods for field type translation

**Additional LOC:** +50-100
**Effort:** 1-2 hours

### Total Implementation
**LOC:** 350-500
**Effort:** 5-8 hours
**Complexity:** 2/5

### Dependencies
- **Phase 1:** ExpressionHandler (for initialization expressions)
- **Phase 3:** TypeTranslator (for type translation)

### Can Parallelize With
- FunctionHandler (in Phase 1)
- ExpressionHandler (partial - can start basic expressions)

### Test Coverage Target
**Unit tests:** 25-35 tests
- Uninitialized variables, initialized variables
- Global variables, static locals
- Arrays, pointers
- Const variables

---

## Handler 3: ExpressionHandler

### Responsibility
Translate C++ expressions to C expressions.

### Implementation Phases

#### Phase 1: Basic Expressions
**Features:**
- Integer literals, floating-point literals
- Binary operators: `+`, `-`, `*`, `/`, `%`
- Variable references (DeclRefExpr)
- Implicit casts (transparent)

**Methods to implement:**
- `canHandle(Expr*)` - Check if it's a handleable expression
- `handleIntegerLiteral(IntegerLiteral*)` - Pass through
- `handleFloatingLiteral(FloatingLiteral*)` - Pass through
- `handleBinaryOperator(BinaryOperator*)` - Translate arithmetic
- `handleDeclRefExpr(DeclRefExpr*)` - Translate variable reference
- `handleImplicitCastExpr(ImplicitCastExpr*)` - Usually transparent

**LOC:** 300-400
**Effort:** 4-5 hours

#### Phase 2: Comparison and Logical Operators
**Features:**
- Comparison operators: `==`, `!=`, `<`, `>`, `<=`, `>=`
- Logical operators: `&&`, `||`, `!`
- Unary operators: `++`, `--`, `-`, `+`, `!`

**Methods to add:**
- Extend `handleBinaryOperator()` for comparison/logical
- `handleUnaryOperator(UnaryOperator*)` - Unary operations

**Additional LOC:** +100-150
**Effort:** 2-3 hours

#### Phase 3: Literals and Casts
**Features:**
- String literals
- Character literals
- C-style casts
- Array subscript expressions

**Methods to add:**
- `handleStringLiteral(StringLiteral*)` - Translate strings
- `handleCharacterLiteral(CharacterLiteral*)` - Translate chars
- `handleCStyleCastExpr(CStyleCastExpr*)` - Translate casts
- `handleArraySubscriptExpr(ArraySubscriptExpr*)` - Translate `arr[i]`

**Additional LOC:** +100-150
**Effort:** 2-3 hours

#### Phase 4: Member Access (Structs)
**Features:**
- Field access: `struct.field`, `ptr->field`

**Methods to add:**
- `handleMemberExpr(MemberExpr*)` - Translate field access

**Additional LOC:** +100-150
**Effort:** 2-3 hours

#### Phase 5: Pointer Operations
**Features:**
- Address-of: `&variable`
- Dereference: `*ptr`
- Pointer arithmetic
- nullptr → NULL

**Methods to add:**
- Extend `handleUnaryOperator()` for `&` and `*`
- Extend `handleBinaryOperator()` for pointer arithmetic
- `handleCXXNullPtrLiteralExpr()` - Translate nullptr

**Additional LOC:** +200-250
**Effort:** 3-4 hours

#### Phase 6: Class Member Access
**Features:**
- `this` pointer translation
- Member access rewriting for classes

**Methods to add:**
- `handleCXXThisExpr()` - Translate `this`
- Extend `handleMemberExpr()` for class fields

**Additional LOC:** +100-150
**Effort:** 2-3 hours

#### Phase 7: Method Calls
**Features:**
- Method call expressions
- Convert `obj.method()` to `Class_method(&obj)`

**Methods to add:**
- `handleCXXMemberCallExpr()` - Translate method calls
- `extractObjectExpr()` - Get object being called on
- `insertThisArgument()` - Add object as first argument

**Additional LOC:** +250-350
**Effort:** 4-5 hours

#### Phase 8: Enum References
**Features:**
- Enum constant references
- Scoped enum prefixing

**Methods to add:**
- Extend `handleDeclRefExpr()` for enum constants
- `prefixEnumReference()` - Add prefix for scoped enums

**Additional LOC:** +50-100
**Effort:** 1-2 hours

#### Phase 9: Base Class Access
**Features:**
- Rewrite base field access to use `__base`
- Rewrite base method calls

**Methods to add:**
- `rewriteBaseFieldAccess()` - Insert `__base` in path
- `rewriteBaseMethodCall()` - Call base method with `&this->__base`

**Additional LOC:** +150-200
**Effort:** 3-4 hours

#### Phase 11: Virtual Method Calls
**Features:**
- Translate virtual calls to vtable indirection

**Methods to add:**
- `handleVirtualCall()` - Translate to `obj->__vtable->method(obj)`

**Additional LOC:** +150-200
**Effort:** 3-4 hours

### Total Implementation
**LOC:** 1500-2100
**Effort:** 27-38 hours (spread across phases)
**Complexity:** 4/5

### Dependencies
- **Phase 1:** None (can start immediately)
- **Phase 4:** RecordHandler (for field declarations)
- **Phase 6:** RecordHandler, MethodHandler (for class context)
- **Phase 7:** MethodHandler (for method mapping)
- **Phase 9:** Inheritance infrastructure
- **Phase 11:** VirtualMethodHandler

### Can Parallelize With
- Can start in parallel with FunctionHandler and VariableHandler
- Most extensions happen in later phases

### Test Coverage Target
**Unit tests:** 80-100 tests
- Each operator separately
- Each literal type
- Pointer operations
- Member access variations
- Method calls
- Virtual calls

---

## Handler 4: StatementHandler

### Responsibility
Translate C++ statements to C statements.

### Implementation Phases

#### Phase 1: Basic Statements
**Features:**
- Return statements
- Compound statements (blocks: `{ }`)
- Declaration statements (variable declarations)

**Methods to implement:**
- `canHandle(Stmt*)` - Check if it's a handleable statement
- `handleReturnStmt(ReturnStmt*)` - Translate return
- `handleCompoundStmt(CompoundStmt*)` - Translate blocks
- `handleDeclStmt(DeclStmt*)` - Translate variable declarations

**LOC:** 50-100
**Effort:** 1-2 hours

#### Phase 2: Control Flow Statements
**Features:**
- If/else statements
- While loops
- For loops
- Switch statements
- Break, continue

**Methods to add:**
- `handleIfStmt(IfStmt*)` - Translate if/else
- `handleWhileStmt(WhileStmt*)` - Translate while
- `handleForStmt(ForStmt*)` - Translate for
- `handleSwitchStmt(SwitchStmt*)` - Translate switch
- `handleCaseStmt(CaseStmt*)` - Translate case
- `handleDefaultStmt(DefaultStmt*)` - Translate default
- `handleBreakStmt(BreakStmt*)` - Translate break
- `handleContinueStmt(ContinueStmt*)` - Translate continue

**Additional LOC:** +200-300
**Effort:** 3-4 hours

### Total Implementation
**LOC:** 250-400
**Effort:** 4-6 hours
**Complexity:** 2/5

### Dependencies
- **Phase 1:** ExpressionHandler (for conditions, return values)
- **Phase 2:** Full ExpressionHandler (for loop conditions)

### Can Parallelize With
- Can start with FunctionHandler
- Most dependencies are on ExpressionHandler

### Test Coverage Target
**Unit tests:** 30-40 tests
- Return statements (with/without value)
- Compound statements (nested)
- Control flow statements (if, while, for, switch)
- Break/continue

---

## Handler 5: RecordHandler

### Responsibility
Translate C++ struct and class declarations to C structs.

### Implementation Phases

#### Phase 4: C-style Structs
**Features:**
- Simple struct declarations
- Field declarations
- Nested structs

**Methods to implement:**
- `canHandle(Decl*)` - Check if it's a RecordDecl/CXXRecordDecl
- `handleRecordDecl(RecordDecl*)` - Translate C-style structs (pass-through)
- `translateFields(RecordDecl*)` - Extract and translate field declarations

**LOC:** 200-300
**Effort:** 3-4 hours

#### Phase 6: Classes
**Features:**
- C++ class → C struct
- Access specifier removal (public/private/protected)
- Member variable extraction (no methods)

**Methods to add:**
- `handleCXXRecordDecl(CXXRecordDecl*)` - Translate class to struct
- `stripAccessSpecifiers()` - Remove access control
- `extractMemberVariables()` - Get fields only

**Additional LOC:** +100-150
**Effort:** 2-3 hours

#### Phase 9: Inheritance
**Features:**
- Embed base class as first field (`__base`)
- Handle single inheritance only

**Methods to add:**
- `handleInheritance(CXXRecordDecl*)` - Detect base classes
- `embedBaseStruct()` - Add `__base` field
- `checkSingleInheritance()` - Verify single inheritance only

**Additional LOC:** +200-250
**Effort:** 3-4 hours

#### Phase 11: Virtual Methods
**Features:**
- Add vtable pointer to classes with virtual methods

**Methods to add:**
- `detectVirtualMethods()` - Check if class has virtual methods
- `addVtableField()` - Add `__vtable` pointer as first field

**Additional LOC:** +100-150
**Effort:** 2-3 hours

### Total Implementation
**LOC:** 600-850
**Effort:** 10-14 hours (spread across phases)
**Complexity:** 3/5

### Dependencies
- **Phase 4:** VariableHandler (for field types)
- **Phase 6:** TypeTranslator
- **Phase 9:** Must run after basic class translation established
- **Phase 11:** VirtualMethodHandler (for vtable generation)

### Can Parallelize With
- Initial implementation (Phase 4) can run in parallel with method handlers
- Later phases depend on method infrastructure

### Test Coverage Target
**Unit tests:** 40-50 tests
- Simple structs, nested structs
- Class to struct conversion
- Access specifier removal
- Inheritance embedding
- Vtable field addition

---

## Handler 6: MethodHandler

### Responsibility
Translate C++ methods (member functions) to C functions with explicit `this` parameter.

### Implementation Phases

#### Phase 6: Basic Methods
**Features:**
- Method → function with `this` parameter
- Method name mangling: `ClassName_methodName`
- Member access via `this->`

**Methods to implement:**
- `canHandle(Decl*)` - Check if it's a CXXMethodDecl
- `handleCXXMethodDecl(CXXMethodDecl*)` - Translate method
- `addThisParameter()` - Add `struct ClassName* this` as first param
- `mangleMethodName()` - Create `ClassName_methodName`
- `translateMemberAccess()` - Rewrite field access to use `this->`

**LOC:** 250-350
**Effort:** 4-5 hours

#### Phase 7: Method Overloading
**Features:**
- Name mangling for overloaded methods
- Type-based name suffix

**Methods to add:**
- `mangleOverloadedName()` - Create unique names for overloads
- `generateTypeSignature()` - Type-based suffix

**Additional LOC:** +100-150
**Effort:** 2-3 hours

#### Phase 9: Base Method Calls
**Features:**
- Handle calls to base class methods
- Pass `&this->__base` as this pointer

**Methods to add:**
- `handleBaseMethodCall()` - Translate base method calls

**Additional LOC:** +50-100
**Effort:** 1-2 hours

#### Phase 11: Virtual Method Handling
**Features:**
- Mark virtual methods
- Integrate with VirtualMethodHandler for vtable generation

**Methods to add:**
- `isVirtual()` - Check if method is virtual
- `registerVirtualMethod()` - Add to vtable

**Additional LOC:** +100-150
**Effort:** 2-3 hours

### Total Implementation
**LOC:** 500-750
**Effort:** 9-13 hours (spread across phases)
**Complexity:** 3/5

### Dependencies
- **Phase 6:** RecordHandler (for struct definitions), ExpressionHandler (for method bodies)
- **Phase 7:** Full expression handling
- **Phase 9:** Inheritance infrastructure
- **Phase 11:** VirtualMethodHandler

### Can Parallelize With
- ConstructorHandler (similar but different logic)

### Test Coverage Target
**Unit tests:** 35-45 tests
- Simple methods, methods with parameters
- Const methods
- Overloaded methods
- Base method calls
- Virtual methods

---

## Handler 7: ConstructorHandler

### Responsibility
Translate C++ constructors to C initialization functions.

### Implementation Phases

#### Phase 6: Basic Constructors
**Features:**
- Constructor → `ClassName_init` function
- Simple member initialization (in body)
- Constructor parameters

**Methods to implement:**
- `canHandle(Decl*)` - Check if it's a CXXConstructorDecl
- `handleCXXConstructorDecl(CXXConstructorDecl*)` - Translate constructor
- `createInitFunction()` - Create `ClassName_init`
- `translateConstructorBody()` - Handle initialization

**LOC:** 200-250
**Effort:** 3-4 hours

#### Phase 9: Base Constructor Calls
**Features:**
- Call base class constructor
- Initialize base before derived

**Methods to add:**
- `callBaseConstructor()` - Insert `Base_init(&this->__base, ...)`
- `initializeBaseFirst()` - Ensure correct order

**Additional LOC:** +100-150
**Effort:** 2-3 hours

#### Phase 11: Vtable Initialization
**Features:**
- Set vtable pointer in constructor

**Methods to add:**
- `setVtablePointer()` - Insert `this->__vtable = &ClassName__vtable_instance`

**Additional LOC:** +50-100
**Effort:** 1-2 hours

### Total Implementation
**LOC:** 350-500
**Effort:** 6-9 hours (spread across phases)
**Complexity:** 3/5

### Dependencies
- **Phase 6:** RecordHandler, MethodHandler
- **Phase 9:** Inheritance infrastructure
- **Phase 11:** VirtualMethodHandler

### Can Parallelize With
- Can work in parallel with DestructorHandler
- Both are similar patterns

### Test Coverage Target
**Unit tests:** 25-35 tests
- Default constructors, parameterized constructors
- Constructor body translation
- Base constructor calls
- Vtable initialization

---

## Handler 8: DestructorHandler

### Responsibility
Translate C++ destructors to C cleanup functions. Also handles automatic destructor injection.

### Implementation Phases

#### Phase 6: Basic Destructors
**Features:**
- Destructor → `ClassName_destroy` function
- Destructor body translation
- Automatic destructor injection at scope end

**Methods to implement:**
- `canHandle(Decl*)` - Check if it's a CXXDestructorDecl
- `handleCXXDestructorDecl(CXXDestructorDecl*)` - Translate destructor
- `createDestroyFunction()` - Create `ClassName_destroy`
- `injectDestructorCalls()` - Auto-insert calls at scope end

**LOC:** 100-150
**Effort:** 2-3 hours

#### Phase 9: Base Destructor Calls
**Features:**
- Call base class destructor after derived cleanup

**Methods to add:**
- `callBaseDestructor()` - Insert `Base_destroy(&this->__base)`
- `destroyDerivedFirst()` - Ensure correct order (derived → base)

**Additional LOC:** +50-100
**Effort:** 1-2 hours

#### Phase 11: Virtual Destructors
**Features:**
- Mark destructor as virtual
- Add to vtable

**Methods to add:**
- `isVirtual()` - Check if destructor is virtual
- `registerVirtualDestructor()` - Add to vtable

**Additional LOC:** +50-100
**Effort:** 1-2 hours

### Total Implementation
**LOC:** 200-350
**Effort:** 4-7 hours (spread across phases)
**Complexity:** 3/5

### Dependencies
- **Phase 6:** RecordHandler, MethodHandler
- **Phase 9:** Inheritance infrastructure
- **Phase 11:** VirtualMethodHandler

### Can Parallelize With
- ConstructorHandler (similar patterns)

### Test Coverage Target
**Unit tests:** 20-30 tests
- Simple destructors, with cleanup code
- Automatic injection
- Base destructor calls
- Virtual destructors

---

## Handler 9: EnumHandler

### Responsibility
Translate C++ enums (both unscoped and scoped) to C enums.

### Implementation Phases

#### Phase 8: Enums
**Features:**
- Unscoped enums (pass-through)
- Scoped enums (enum class) → prefix constants
- Enum constant references

**Methods to implement:**
- `canHandle(Decl*)` - Check if it's an EnumDecl
- `handleEnumDecl(EnumDecl*)` - Translate enum declaration
- `generateEnumConstants()` - Create enum constants
- `prefixScopedEnum()` - Add `EnumName__` prefix for scoped enums

**LOC:** 200-250
**Effort:** 3-4 hours

### Total Implementation
**LOC:** 200-250
**Effort:** 3-4 hours
**Complexity:** 2/5

### Dependencies
- **Phase 8:** None (can be implemented independently)
- Uses ExpressionHandler for enum constant references (handled by ExpressionHandler)

### Can Parallelize With
- Can be implemented independently in Phase 8
- No dependencies on other handlers

### Test Coverage Target
**Unit tests:** 25-30 tests
- Unscoped enums, scoped enums
- Enum constant references
- Enum in switch statements
- Enum as function parameters

---

## Special Handlers

### TemplateMonomorphizer (Existing, needs extension)

**Implementation:** Phase 10
**Responsibility:** Detect template instantiations and generate monomorphized concrete types
**LOC:** +400-500 (extensions to existing code)
**Effort:** 6-8 hours
**Complexity:** 5/5

**Dependencies:**
- RecordHandler (for template classes)
- FunctionHandler (for template functions)

**Note:** This handler already exists in the codebase but needs integration with the new handler chain.

### VirtualMethodHandler (New, Phase 11 only)

**Implementation:** Phase 11
**Responsibility:** Generate vtables for classes with virtual methods
**LOC:** 500-700
**Effort:** 8-10 hours
**Complexity:** 5/5

**Dependencies:**
- RecordHandler (for class structure)
- MethodHandler (for virtual methods)
- ConstructorHandler (for vtable initialization)

### NamespaceHandler (New, Phase 12 only)

**Implementation:** Phase 12
**Responsibility:** Track namespace context and generate prefixed names
**LOC:** 200-300
**Effort:** 3-4 hours
**Complexity:** 3/5

**Dependencies:**
- All handlers (adds namespace prefix to all names)

---

## Implementation Order Summary

### Phase-by-Phase Handler Schedule

**Phase 1:** (Parallel possible)
1. FunctionHandler (basic) - 200-300 LOC, 3-4 hours
2. VariableHandler (local) - 150-200 LOC, 2-3 hours
3. ExpressionHandler (basic) - 300-400 LOC, 4-5 hours
4. StatementHandler (basic) - 50-100 LOC, 1-2 hours

**Total Phase 1:** 700-1000 LOC, 10-14 hours

**Phase 2:** (Extensions)
- StatementHandler + ExpressionHandler extensions - 300-450 LOC, 5-7 hours

**Phase 3:** (Extensions)
- VariableHandler + ExpressionHandler extensions - 250-350 LOC, 4-6 hours

**Phase 4:** (New handler)
- RecordHandler (basic) - 200-300 LOC, 3-4 hours
- ExpressionHandler extensions - 100-150 LOC, 2-3 hours

**Total Phase 4:** 300-450 LOC, 5-7 hours

**Phase 5:** (Extensions)
- FunctionHandler + ExpressionHandler extensions - 300-400 LOC, 5-7 hours

**Phase 6:** (New handlers + extensions)
- RecordHandler extensions - 100-150 LOC, 2-3 hours
- MethodHandler (new) - 250-350 LOC, 4-5 hours
- ConstructorHandler (new) - 200-250 LOC, 3-4 hours
- DestructorHandler (new) - 100-150 LOC, 2-3 hours
- ExpressionHandler extensions - 100-150 LOC, 2-3 hours

**Total Phase 6:** 750-1050 LOC, 13-18 hours

**Phase 7:** (Extensions)
- ExpressionHandler + MethodHandler extensions - 350-500 LOC, 6-8 hours

**Phase 8:** (New handler)
- EnumHandler (new) - 200-250 LOC, 3-4 hours
- ExpressionHandler extensions - 50-100 LOC, 1-2 hours

**Total Phase 8:** 250-350 LOC, 4-6 hours

**Phase 9:** (Extensions across multiple handlers)
- RecordHandler extensions - 200-250 LOC, 3-4 hours
- ConstructorHandler + DestructorHandler extensions - 150-200 LOC, 3-4 hours
- ExpressionHandler extensions - 150-200 LOC, 3-4 hours

**Total Phase 9:** 500-650 LOC, 9-12 hours

**Phase 10:** (Existing handler extension)
- TemplateMonomorphizer extensions - 400-500 LOC, 6-8 hours

**Phase 11:** (New handler + extensions)
- VirtualMethodHandler (new) - 500-700 LOC, 8-10 hours
- RecordHandler + ConstructorHandler + ExpressionHandler extensions - 250-350 LOC, 5-7 hours

**Total Phase 11:** 750-1050 LOC, 13-17 hours

**Phase 12:** (New handler + extensions)
- NamespaceHandler (new) - 200-300 LOC, 3-4 hours
- All handlers get namespace integration - 150-200 LOC, 3-4 hours

**Total Phase 12:** 350-500 LOC, 6-8 hours

---

## Parallelization Strategy

### Can Run in Parallel

**Phase 1:**
- FunctionHandler, VariableHandler, ExpressionHandler (basic), StatementHandler (basic)
- All are independent and can be developed simultaneously
- **Max parallelism:** 4 developers

**Phase 6:**
- MethodHandler, ConstructorHandler, DestructorHandler
- After RecordHandler is complete, these can run in parallel
- **Max parallelism:** 3 developers

**Phase 8:**
- EnumHandler is completely independent
- Can be developed while other work continues

### Must Be Sequential

**Handler Dependencies:**
1. RecordHandler (Phase 4) must complete before MethodHandler (Phase 6)
2. MethodHandler must complete before method call translation (Phase 7)
3. Inheritance (Phase 9) requires basic class infrastructure (Phase 6)
4. Virtual methods (Phase 11) require inheritance (Phase 9)

**Phase Dependencies:**
- Phase 1 must complete first (foundation)
- Phases 2-3 can extend Phase 1 handlers
- Phase 4 requires Phase 1 foundation
- Phases 5-12 build on previous phases

---

## Total Handler LOC and Effort

### By Handler

1. **FunctionHandler:** 450-700 LOC, 8-12 hours
2. **VariableHandler:** 350-500 LOC, 5-8 hours
3. **ExpressionHandler:** 1500-2100 LOC, 27-38 hours
4. **StatementHandler:** 250-400 LOC, 4-6 hours
5. **RecordHandler:** 600-850 LOC, 10-14 hours
6. **MethodHandler:** 500-750 LOC, 9-13 hours
7. **ConstructorHandler:** 350-500 LOC, 6-9 hours
8. **DestructorHandler:** 200-350 LOC, 4-7 hours
9. **EnumHandler:** 200-250 LOC, 3-4 hours

**Subtotal (9 core handlers):** 4400-6400 LOC, 76-111 hours

### Special Handlers

- **TemplateMonomorphizer:** 400-500 LOC, 6-8 hours
- **VirtualMethodHandler:** 500-700 LOC, 8-10 hours
- **NamespaceHandler:** 200-300 LOC, 3-4 hours

**Special handlers:** 1100-1500 LOC, 17-22 hours

### Infrastructure

- **HandlerRegistry:** 100-150 LOC, 2-3 hours
- **HandlerContext:** 200-300 LOC, 3-4 hours
- **TranslationOrchestrator:** 200-300 LOC, 3-4 hours
- **TypeTranslator:** 150-200 LOC, 2-3 hours

**Infrastructure:** 650-950 LOC, 10-14 hours

### Grand Total

**Implementation LOC:** 6150-8850 LOC
**Implementation Effort:** 103-147 hours

**Testing LOC:** ~11,350-13,250 LOC (roughly 1.8x implementation)
**Testing Effort:** ~101-134 hours

**Total Project:** 17,500-22,100 LOC, 204-281 hours

---

## Critical Path

The critical path for handler implementation:

```
Phase 1: FunctionHandler + VariableHandler + ExpressionHandler + StatementHandler (10-14 hours)
  ↓
Phase 2-3: Extensions (9-13 hours)
  ↓
Phase 4: RecordHandler (5-7 hours)
  ↓
Phase 5: Pointer extensions (5-7 hours)
  ↓
Phase 6: MethodHandler + ConstructorHandler + DestructorHandler (13-18 hours)
  ↓
Phase 7: Method call extensions (6-8 hours)
  ↓
Phase 8: EnumHandler (4-6 hours)
  ↓
Phase 9: Inheritance extensions (9-12 hours)
  ↓
Phase 10: Template extensions (6-8 hours)
  ↓
Phase 11: VirtualMethodHandler (13-17 hours)
  ↓
Phase 12: NamespaceHandler (6-8 hours)
```

**Critical path total:** 86-118 hours (~11-15 working days, solo developer)

**With parallelization (4 developers):** Could reduce to ~6-8 weeks calendar time

---

## Handler Readiness Checklist

For each handler, before marking "complete":

- [ ] All `canHandle()` methods implemented
- [ ] All `handle*()` methods implemented for current phase
- [ ] Unit tests written and passing (target coverage met)
- [ ] Integration tests passing
- [ ] Registered with HandlerRegistry
- [ ] Documentation updated
- [ ] Code reviewed
- [ ] No TODOs or FIXMEs remaining

---

## Next Steps

**Immediate:** Begin Phase 1 handler implementation
1. Set up handler infrastructure (HandlerRegistry, HandlerContext, TranslationOrchestrator)
2. Implement Phase 1 handlers in parallel (FunctionHandler, VariableHandler, ExpressionHandler, StatementHandler)
3. Write unit tests for each handler
4. Integrate and test end-to-end

**After Phase 1:** Continue with Phase 2-3 extensions, then Phase 4 RecordHandler

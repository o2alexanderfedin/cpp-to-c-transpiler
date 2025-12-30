<objective>
Integrate C++ dynamic_cast<>() operator (CXXDynamicCastExpr) with the dispatcher framework by creating a CXXDynamicCastExprHandler that delegates to DynamicCastTranslator.

C++ dynamic_cast<>() provides safe runtime type casting with NULL return on failure:
- **Downcast**: `Derived* d = dynamic_cast<Derived*>(base_ptr)` - Cast to derived class
- **Crosscast**: `Sibling* s = dynamic_cast<Sibling*>(other_ptr)` - Cast across hierarchy
- **Upcast**: `Base* b = dynamic_cast<Base*>(derived_ptr)` - Cast to base (compile-time safe)

This handler detects CXXDynamicCastExpr nodes and translates them to C runtime function calls using the existing DynamicCastTranslator infrastructure.

WHY this matters:
- dynamic_cast is essential for safe polymorphic type conversions
- DynamicCastTranslator already exists but is NOT integrated with the dispatcher
- Integration ensures dynamic_cast works seamlessly with other expression handlers
- Enables complex expressions like `dynamic_cast<Derived*>(arr[i]->getBase())` to translate correctly
</objective>

<context>
Project: C++ to C Transpiler using Clang AST
Dispatcher Pattern: Chain of Responsibility with recursive dispatch

Existing RTTI infrastructure:
@include/DynamicCastTranslator.h - Handles dynamic_cast<>() translation (already implemented)
@src/DynamicCastTranslator.cpp - Translation logic (already implemented)
@docs/RTTI_TRANSLATION.md - Comprehensive guide with examples
@docs/features/rtti.md - Implementation guide with Itanium ABI details
@transpiled/runtime/rtti_runtime.h - Runtime functions (cxx_dynamic_cast, hierarchy traversal)
@transpiled/runtime/rtti_runtime.c - Runtime implementation

Existing dispatcher handlers (REFERENCE PATTERN):
@include/dispatch/CXXOperatorCallExprHandler.h - Delegates to SpecialOperatorTranslator
@include/dispatch/CXXTypeidExprHandler.h - Delegates to TypeidTranslator (once created)
@include/dispatch/BinaryOperatorHandler.h - Built-in binary operators

Dispatcher framework:
@include/dispatch/CppToCVisitorDispatcher.h
@src/dispatch/CppToCVisitorDispatcher.cpp

Expression mapping:
@include/mapping/ExprMapper.h

Read @CLAUDE.md for project conventions (TDD, SOLID, etc.).
</context>

<requirements>
1. Create CXXDynamicCastExprHandler following the dispatcher pattern
2. Handler must implement:
   - `static void registerWith(CppToCVisitorDispatcher& dispatcher)`
   - `static bool canHandle(const clang::Expr* E)` - Check for CXXDynamicCastExprClass
   - `static void handleDynamicCast(...)` - Translate using DynamicCastTranslator
3. Use DynamicCastTranslator as the underlying implementation:
   - Call `DynamicCastTranslator::translateDynamicCast()` to get C CallExpr
   - Store result in ExprMapper
4. Handle all dynamic_cast forms:
   - **Downcast**: Cast to derived class (runtime check required)
   - **Crosscast**: Cast across hierarchy (runtime check required)
   - **Upcast**: Cast to base (compile-time safe, but translated for consistency)
   - **Pointer casts**: `dynamic_cast<T*>(ptr)` - Returns NULL on failure
   - **Reference casts**: `dynamic_cast<T&>(ref)` - Throws bad_cast on failure (not supported in C)
5. Generate runtime call to `cxx_dynamic_cast()`:
   ```c
   void* cxx_dynamic_cast(const void* ptr,
                          const struct __class_type_info* src_type,
                          const struct __class_type_info* dst_type,
                          ptrdiff_t offset);
   ```
6. Handle argument dispatch:
   - Dispatch subexpression (the pointer/reference being cast) recursively
   - DynamicCastTranslator handles source/target type extraction
7. Create comprehensive unit tests (minimum 12 tests)
8. Integrate with existing DynamicCastTranslator infrastructure

Follow TDD: Write failing tests, implement to pass, refactor.
</requirements>

<implementation>
File structure to create:
1. `./include/dispatch/CXXDynamicCastExprHandler.h` - Handler interface
2. `./src/dispatch/CXXDynamicCastExprHandler.cpp` - Handler implementation
3. `./tests/unit/dispatch/CXXDynamicCastExprHandlerDispatcherTest.cpp` - Unit tests

Key implementation details:
- CXXDynamicCastExpr represents `dynamic_cast<TargetType>(expr)` syntax
- Use `E->getStmtClass() == clang::Stmt::CXXDynamicCastExprClass` to detect
- Cast to `clang::CXXDynamicCastExpr` to access:
  * `getSubExpr()` - Returns the expression being cast
  * `getTypeAsWritten()` - Returns the target type
  * `getCastKind()` - Returns cast kind (CK_DynamicCast)
- Use DynamicCastTranslator::translateDynamicCast() to translate to C CallExpr
- Store translated CallExpr in ExprMapper
- Handle argument dispatch:
  * CXXDynamicCastExpr has subexpression requiring dispatch
  * Dispatch subexpression recursively through dispatcher
  * DynamicCastTranslator handles C function call construction

Translation examples (from docs/RTTI_TRANSLATION.md):

**Example 1: Successful downcast**
```cpp
// C++ Code:
Base* a = new Derived();
Derived* d = dynamic_cast<Derived*>(a);

// Translated C (from DynamicCastTranslator):
struct Base* a = Derived_new();
struct Derived* d = (struct Derived*)cxx_dynamic_cast(
    a,
    &__ti_Base,
    &__ti_Derived,
    0  // offset
);
```

**Example 2: Failed downcast**
```cpp
// C++ Code:
Base* a = new Base();
Derived* d = dynamic_cast<Derived*>(a);  // Returns NULL

// Translated C (from DynamicCastTranslator):
struct Base* a = Base_new();
struct Derived* d = (struct Derived*)cxx_dynamic_cast(
    a,
    &__ti_Base,
    &__ti_Derived,
    0
);
// d will be NULL
```

**Example 3: Crosscast**
```cpp
// C++ Code (multiple inheritance):
// class A { virtual ~A(); };
// class B { virtual ~B(); };
// class C : public A, public B {};
C* c = new C();
B* b = dynamic_cast<B*>((A*)c);

// Translated C (from DynamicCastTranslator):
struct C* c = C_new();
struct B* b = (struct B*)cxx_dynamic_cast(
    (struct A*)c,
    &__ti_A,
    &__ti_B,
    offsetof(struct C, B_base)  // offset to B subobject
);
```

Runtime function signature (from transpiled/runtime/rtti_runtime.h):
```c
/**
 * @brief Perform dynamic_cast at runtime
 * @param ptr Pointer to object being cast
 * @param src_type Type info for source type
 * @param dst_type Type info for destination type
 * @param offset Offset from src to dst (for upcasts)
 * @return Casted pointer on success, NULL on failure
 */
void* cxx_dynamic_cast(const void* ptr,
                       const struct __class_type_info* src_type,
                       const struct __class_type_info* dst_type,
                       ptrdiff_t offset);
```

WHY these patterns matter:
- CXXDynamicCastExpr is distinct from static_cast (runtime vs compile-time)
- Recursive dispatch ensures complex expressions in subexpr translate correctly
- DynamicCastTranslator integration reuses existing, tested translation logic
- ExprMapper prevents duplicate translations
- Runtime function provides Itanium ABI-compliant type checking

DO NOT:
- Confuse dynamic_cast with static_cast or reinterpret_cast
- Re-implement DynamicCastTranslator logic (reuse existing infrastructure)
- Skip dispatching subexpression (causes incomplete translation)
- Forget ExprMapper.hasCreated() check (causes duplication)
- Support reference casts (C has no exceptions, only pointer casts supported)
</implementation>

<output>
Create these files:
- `./include/dispatch/CXXDynamicCastExprHandler.h` - Handler header with documentation
- `./src/dispatch/CXXDynamicCastExprHandler.cpp` - Handler implementation with logging
- `./tests/unit/dispatch/CXXDynamicCastExprHandlerDispatcherTest.cpp` - Tests (minimum 12)
- Update `./CMakeLists.txt` if needed for test target

Integration requirements:
- Handler must be registered in CppToCVisitorDispatcher::registerDefaultHandlers()
- Handler must work with existing DynamicCastTranslator
- Handler must integrate with ExprMapper
- Handler must depend on rtti_runtime.h being available (runtime linkage)

Save output to: `.prompts/051-dynamic-cast-handler-dispatcher/dynamic-cast-handler-dispatcher.md`
Create SUMMARY.md with findings and next steps.
</output>

<verification>
Before declaring complete:
1. Code compiles without errors or warnings
2. Run tests: `ctest -R CXXDynamicCastExprHandlerDispatcherTest --output-on-failure`
3. All tests pass (100%)
4. Test all dynamic_cast forms:
   - Successful downcast (returns valid pointer)
   - Failed downcast (returns NULL)
   - Crosscast (multiple inheritance)
   - Upcast (to base class)
5. Test integration scenarios:
   - dynamic_cast with complex subexpression: `dynamic_cast<D*>(arr[i].getPtr())`
   - dynamic_cast in conditional: `if (D* d = dynamic_cast<D*>(b))`
   - dynamic_cast with member access: `dynamic_cast<D*>(obj->getBase())`
   - Nested dynamic_cast: `dynamic_cast<C*>(dynamic_cast<B*>(a))`
6. Verify DynamicCastTranslator integration works correctly
7. Verify runtime function call is generated correctly
8. Check debug output is informative
9. Verify SOLID principles compliance
</verification>

<success_criteria>
- CXXDynamicCastExprHandler.h created with full documentation
- CXXDynamicCastExprHandler.cpp implements delegation to DynamicCastTranslator
- Unit tests cover:
  * Handler registration
  * Successful downcast
  * Failed downcast (NULL return)
  * Crosscast (multiple inheritance)
  * Upcast (to base)
  * DynamicCastTranslator integration
  * ExprMapper integration
  * Predicate correctness (matches only CXXDynamicCastExpr)
  * Distinguish from static_cast/reinterpret_cast
  * Complex nested subexpressions
  * Integration with conditionals and member access
  * Runtime call generation
- All tests pass (100%)
- Code compiles cleanly
- Handler ready for dispatcher integration
- Integration with existing RTTI infrastructure verified
- Runtime linkage verified (rtti_runtime.h/c accessible)
</success_criteria>

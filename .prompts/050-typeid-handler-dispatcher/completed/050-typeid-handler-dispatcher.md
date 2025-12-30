<objective>
Integrate C++ typeid() operator (CXXTypeidExpr) with the dispatcher framework by creating a CXXTypeidExprHandler that delegates to TypeidTranslator.

C++ typeid() operator provides runtime type information (RTTI) in two forms:
- **Polymorphic**: `typeid(*ptr)` - Queries vtable at runtime for dynamic type
- **Static**: `typeid(Type)` or `typeid(obj)` - Resolved at compile time

This handler detects CXXTypeidExpr nodes and translates them to C expressions using the existing TypeidTranslator infrastructure.

WHY this matters:
- typeid() is fundamental for RTTI-based code (debugging, serialization, reflection)
- TypeidTranslator already exists but is NOT integrated with the dispatcher
- Integration ensures typeid() works seamlessly with other expression handlers
- Enables complex expressions like `if (typeid(*a) == typeid(*b))` to translate correctly
</objective>

<context>
Project: C++ to C Transpiler using Clang AST
Dispatcher Pattern: Chain of Responsibility with recursive dispatch

Existing RTTI infrastructure:
@include/TypeidTranslator.h - Handles typeid() translation (already implemented)
@src/TypeidTranslator.cpp - Translation logic (already implemented)
@docs/RTTI_TRANSLATION.md - Comprehensive guide with examples
@docs/features/rtti.md - Implementation guide with Itanium ABI details

Existing dispatcher handlers (REFERENCE PATTERN):
@include/dispatch/CXXOperatorCallExprHandler.h - Delegates to SpecialOperatorTranslator
@include/dispatch/BinaryOperatorHandler.h - Built-in binary operators
@include/dispatch/UnaryOperatorHandler.h - Built-in unary operators

Dispatcher framework:
@include/dispatch/CppToCVisitorDispatcher.h
@src/dispatch/CppToCVisitorDispatcher.cpp

Expression mapping:
@include/mapping/ExprMapper.h

Read @CLAUDE.md for project conventions (TDD, SOLID, etc.).
</context>

<requirements>
1. Create CXXTypeidExprHandler following the dispatcher pattern
2. Handler must implement:
   - `static void registerWith(CppToCVisitorDispatcher& dispatcher)`
   - `static bool canHandle(const clang::Expr* E)` - Check for CXXTypeidExprClass
   - `static void handleTypeidExpr(...)` - Translate using TypeidTranslator
3. Use TypeidTranslator as the underlying implementation:
   - Call `TypeidTranslator::translateTypeid()` to get C expression
   - Store result in ExprMapper
4. Handle both forms of typeid:
   - **Polymorphic typeid**: `typeid(*ptr)` → vtable lookup: `ptr->vptr->type_info`
   - **Static typeid**: `typeid(Type)` → static reference: `&__ti_ClassName`
5. Distinguish polymorphic vs static:
   - Use `TypeidTranslator::isPolymorphicTypeid(const CXXTypeidExpr*)`
   - Polymorphic: Requires vtable lookup at runtime
   - Static: Compile-time constant reference
6. Handle argument dispatch:
   - If polymorphic (operand is expression): Dispatch operand recursively
   - If static (operand is type): No dispatch needed
7. Create comprehensive unit tests (minimum 10 tests)
8. Integrate with existing TypeidTranslator infrastructure

Follow TDD: Write failing tests, implement to pass, refactor.
</requirements>

<implementation>
File structure to create:
1. `./include/dispatch/CXXTypeidExprHandler.h` - Handler interface
2. `./src/dispatch/CXXTypeidExprHandler.cpp` - Handler implementation
3. `./tests/unit/dispatch/CXXTypeidExprHandlerDispatcherTest.cpp` - Unit tests

Key implementation details:
- CXXTypeidExpr represents `typeid(expr)` or `typeid(Type)` syntax
- Use `E->getStmtClass() == clang::Stmt::CXXTypeidExprClass` to detect
- Cast to `clang::CXXTypeidExpr` to access:
  * `isTypeOperand()` - Returns true if `typeid(Type)`, false if `typeid(expr)`
  * `getExprOperand()` - Returns expression for `typeid(expr)` form
  * `getTypeOperand()` - Returns type for `typeid(Type)` form
- Use TypeidTranslator::translateTypeid() to translate to C expression
- Store translated expression in ExprMapper
- Handle argument dispatch:
  * CXXTypeidExpr may have expression operand requiring dispatch
  * Dispatch expression operand recursively through dispatcher
  * TypeidTranslator handles C expression construction

Translation examples (from docs/RTTI_TRANSLATION.md):

**Example 1: Polymorphic typeid**
```cpp
// C++ Code:
Base* a = new Derived();
const std::type_info& ti = typeid(*a);

// Translated C (from TypeidTranslator):
struct Base* a = Derived_new();
const struct __class_type_info* ti = a->vptr->type_info;
```

**Example 2: Static typeid**
```cpp
// C++ Code:
const std::type_info& ti = typeid(Derived);

// Translated C (from TypeidTranslator):
const struct __class_type_info* ti = &__ti_Derived;
```

**Example 3: Static typeid with object**
```cpp
// C++ Code:
Derived d;
const std::type_info& ti = typeid(d);

// Translated C (from TypeidTranslator):
struct Derived d;
const struct __class_type_info* ti = &__ti_Derived;
```

WHY these patterns matter:
- CXXTypeidExpr is distinct from other operators (unique AST node type)
- Recursive dispatch ensures complex expressions in operand translate correctly
- TypeidTranslator integration reuses existing, tested translation logic
- ExprMapper prevents duplicate translations

DO NOT:
- Confuse polymorphic vs static typeid (different translation strategies)
- Re-implement TypeidTranslator logic (reuse existing infrastructure)
- Skip dispatching expression operand (causes incomplete translation)
- Forget ExprMapper.hasCreated() check (causes duplication)
</implementation>

<output>
Create these files:
- `./include/dispatch/CXXTypeidExprHandler.h` - Handler header with documentation
- `./src/dispatch/CXXTypeidExprHandler.cpp` - Handler implementation with logging
- `./tests/unit/dispatch/CXXTypeidExprHandlerDispatcherTest.cpp` - Tests (minimum 10)
- Update `./CMakeLists.txt` if needed for test target

Integration requirements:
- Handler must be registered in CppToCVisitorDispatcher::registerDefaultHandlers()
- Handler must work with existing TypeidTranslator
- Handler must integrate with ExprMapper

Save output to: `.prompts/050-typeid-handler-dispatcher/typeid-handler-dispatcher.md`
Create SUMMARY.md with findings and next steps.
</output>

<verification>
Before declaring complete:
1. Code compiles without errors or warnings
2. Run tests: `ctest -R CXXTypeidExprHandlerDispatcherTest --output-on-failure`
3. All tests pass (100%)
4. Test both forms of typeid:
   - Polymorphic typeid with expression operand
   - Static typeid with type operand
   - Static typeid with object operand (non-polymorphic)
5. Test integration scenarios:
   - typeid in comparison: `typeid(*a) == typeid(*b)`
   - typeid with complex expression: `typeid(*(arr[i].ptr))`
   - typeid with member access: `typeid(*obj.getPtr())`
6. Verify TypeidTranslator integration works correctly
7. Check debug output is informative
8. Verify SOLID principles compliance
</verification>

<success_criteria>
- CXXTypeidExprHandler.h created with full documentation
- CXXTypeidExprHandler.cpp implements delegation to TypeidTranslator
- Unit tests cover:
  * Handler registration
  * Polymorphic typeid (vtable lookup)
  * Static typeid with type operand
  * Static typeid with object operand
  * TypeidTranslator integration
  * ExprMapper integration
  * Predicate correctness (matches only CXXTypeidExpr)
  * Distinguish polymorphic vs static
  * Complex nested expressions
  * Integration with comparison operators
- All tests pass (100%)
- Code compiles cleanly
- Handler ready for dispatcher integration
- Integration with existing RTTI infrastructure verified
</success_criteria>

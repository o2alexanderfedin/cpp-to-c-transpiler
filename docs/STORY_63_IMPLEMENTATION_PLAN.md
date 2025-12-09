# Story #63: Complete Constructor/Destructor Chaining with Inheritance

## Implementation Plan

**Epic:** #39 - Advanced Constructor/Destructor Features
**Story:** #63 - Complete Constructor/Destructor Chaining with Inheritance
**Status:** In Progress
**Date:** 2025-12-08

---

## Executive Summary

### Objective
Complete the constructor/destructor chaining implementation by adding member constructor and destructor calls, ensuring correct C++ semantics for construction and destruction order.

### Current State (From Research)
- ✅ Base constructor chaining (Story #51)
- ✅ Base destructor chaining (Story #52)
- ✅ Member initialization list ordering (Story #61)
- ✅ Implicit constructors with member calls (Story #62)
- ❌ **GAP:** Member constructor calls in explicit constructors
- ❌ **GAP:** Member destructor calls in all destructors

### Target State
- **Construction order:** Base → Members (declaration order) → Derived body ✅
- **Destruction order:** Derived body → Members (reverse declaration order) → Base ✅

---

## Research Findings

### Gap 1: Member Constructors in Explicit Constructors

**Location:** `src/CppToCVisitor.cpp:207-246` (VisitCXXConstructorDecl)

**Current Behavior:**
```cpp
// Point(int x, int y) : inner(val) {}
// Current output:
void Point__ctor(struct Point *this, int x, int y) {
  this->inner = val;  // ❌ WRONG: Assignment instead of constructor call
}
```

**Expected Behavior:**
```cpp
// Expected output:
void Point__ctor(struct Point *this, int x, int y) {
  Inner__ctor(&this->inner, val);  // ✅ CORRECT: Constructor call
}
```

**Root Cause:**
- `translateExpr(InitExpr)` doesn't detect `CXXConstructExpr` for class-type members
- Member initializers are translated as assignments for all types
- Implicit constructors (Story #62) DO handle this correctly via `generateDefaultConstructor()`

**Available Pattern:**
```cpp
// From generateDefaultConstructor (lines 1032-1046) - WORKING ✅
if (fieldType->isRecordType()) {
  FunctionDecl *MemberCtor = getCtor(fieldCtorName);
  MemberExpr *ThisMember = Builder.member(Builder.ref(thisParam), Field);
  Expr *memberAddr = Builder.addrOf(ThisMember);
  CallExpr *memberCtorCall = Builder.call(MemberCtor, {memberAddr});
  stmts.push_back(memberCtorCall);
}
```

### Gap 2: Member Destructors Missing Entirely

**Location:** `src/CppToCVisitor.cpp:377-390` (VisitCXXDestructorDecl)

**Current Behavior:**
```cpp
// Container::~Container() {}
// Current output:
void Container__dtor(struct Container *this) {
  // Derived body
  Base__dtor((struct Base*)this);  // Base destructor
  // ❌ MISSING: Member destructors
}
```

**Expected Behavior:**
```cpp
// Expected output:
void Container__dtor(struct Container *this) {
  // Derived body
  Resource__dtor(&this->res);      // ✅ Member destructor (reverse order)
  Base__dtor((struct Base*)this);  // Base destructor
}
```

**Root Cause:**
- No code iterates through fields in `VisitCXXDestructorDecl`
- Infrastructure exists but unused: `hasNonTrivialDestructor()`, `createDestructorCall()`

**Available Pattern:**
```cpp
// From emitBaseDestructorCalls (lines 613-657) - WORKING ✅
for (const CXXBaseSpecifier &Base : DerivedClass->bases()) {
  CXXRecordDecl *BaseClass = Base.getType()->getAsCXXRecordDecl();
  CXXDestructorDecl *BaseDtor = BaseClass->getDestructor();
  FunctionDecl *BaseDFunc = dtorMap[BaseDtor];
  CallExpr *BaseCall = Builder.call(BaseDFunc, {Builder.ref(thisParam)});
  stmts.push_back(BaseCall);
}
```

---

## Technical Design

### Solution 1: Member Constructor Calls

**New Method:** `emitMemberConstructorCalls()`

**Signature:**
```cpp
void CppToCVisitor::emitMemberConstructorCalls(
    clang::CXXConstructorDecl *CD,
    clang::ParmVarDecl *thisParam,
    std::vector<clang::Stmt*> &stmts);
```

**Algorithm:**
1. Get parent class from constructor
2. Iterate fields in **declaration order** (not init list order)
3. For each field:
   - Find initializer in init list (if any)
   - If class-type member:
     - If initializer is `CXXConstructExpr`: extract args, call member constructor
     - If initializer is other expr: copy/assignment
     - If no initializer: call default constructor
   - If primitive member:
     - Keep existing assignment logic

**Helper Method:** `findInitializerForField()`

**Signature:**
```cpp
clang::CXXCtorInitializer* CppToCVisitor::findInitializerForField(
    clang::CXXConstructorDecl *CD,
    clang::FieldDecl *Field);
```

**Integration Point:**
- File: `src/CppToCVisitor.cpp`
- Location: `VisitCXXConstructorDecl` line 207
- Replace: Lines 207-246 (current member init translation)
- With: Single call to `emitMemberConstructorCalls(CD, thisParam, stmts)`

**Order Guarantee:**
```cpp
// VisitCXXConstructorDecl new order:
emitBaseConstructorCalls(CD, thisParam, stmts);      // 1. Base
emitMemberConstructorCalls(CD, thisParam, stmts);    // 2. Members ← NEW
// Constructor body                                  // 3. Derived body
```

### Solution 2: Member Destructor Calls

**New Method:** `emitMemberDestructorCalls()`

**Signature:**
```cpp
void CppToCVisitor::emitMemberDestructorCalls(
    clang::CXXRecordDecl *ClassDecl,
    clang::ParmVarDecl *thisParam,
    std::vector<clang::Stmt*> &stmts);
```

**Algorithm:**
1. Collect all fields with non-trivial destructors
2. Iterate fields in **reverse declaration order**
3. For each field with non-trivial destructor:
   - Get field type's destructor from `dtorMap`
   - Build destructor call: `FieldDtor(&this->field)`
   - Append to statements

**Integration Point:**
- File: `src/CppToCVisitor.cpp`
- Location: `VisitCXXDestructorDecl` line 388
- Insert: Between destructor body and base destructor calls

**Order Guarantee:**
```cpp
// VisitCXXDestructorDecl new order:
// Derived destructor body                          // 1. Derived body
emitMemberDestructorCalls(ClassDecl, thisParam, stmts);  // 2. Members (reverse) ← NEW
emitBaseDestructorCalls(DD, thisParam, stmts);           // 3. Base
```

---

## Header Changes

**File:** `include/CppToCVisitor.h`

**Add after line 150:**
```cpp
/**
 * @brief Create member constructor call statements for constructor
 * @param CD The C++ constructor declaration
 * @param thisParam The 'this' parameter of the constructor
 * @param stmts Output vector to append member constructor calls to
 *
 * Single Responsibility: Handle member constructor calls (Story #63)
 * Open/Closed: Can extend for const/reference members without modifying
 *
 * Processes member fields in declaration order and generates constructor
 * calls for class-type members, either from explicit init list or default.
 */
void emitMemberConstructorCalls(clang::CXXConstructorDecl *CD,
                                 clang::ParmVarDecl *thisParam,
                                 std::vector<clang::Stmt*> &stmts);

/**
 * @brief Create member destructor call statements for destructor
 * @param ClassDecl The C++ class declaration
 * @param thisParam The 'this' parameter of the destructor
 * @param stmts Output vector to append member destructor calls to
 *
 * Single Responsibility: Handle member destructor calls (Story #63)
 * Open/Closed: Can extend for virtual destructors without modifying
 *
 * Processes member fields in REVERSE declaration order and generates
 * destructor calls for class-type members with non-trivial destructors.
 */
void emitMemberDestructorCalls(clang::CXXRecordDecl *ClassDecl,
                                clang::ParmVarDecl *thisParam,
                                std::vector<clang::Stmt*> &stmts);

/**
 * @brief Find initializer for a specific field in constructor init list
 * @param CD The C++ constructor declaration
 * @param Field The field to find initializer for
 * @return Initializer for the field, or nullptr if not found
 *
 * Single Responsibility: Lookup helper for member initializers
 */
clang::CXXCtorInitializer* findInitializerForField(
    clang::CXXConstructorDecl *CD,
    clang::FieldDecl *Field);
```

---

## Test Strategy (TDD)

### Test File
`tests/InheritanceTest.cpp` (add after Test 25)

### Test 26: Simple Member Constructor Calls
**Purpose:** Verify class-type members get constructor calls in explicit constructors

**Input C++:**
```cpp
class Inner {
  int value;
public:
  Inner(int v) : value(v) {}
  int getValue() const { return value; }
};

class Outer {
  Inner inner;
public:
  Outer(int v) : inner(v) {}
  int getInnerValue() const { return inner.getValue(); }
};
```

**Expected C Output:**
```c
void Outer__ctor(struct Outer *this, int v) {
  Inner__ctor(&this->inner, v);  // ✅ Member constructor call
}
```

**Verification:**
```cpp
ASSERT_NE(outerCtor, nullptr) << "Outer constructor not found";
CompoundStmt *body = dyn_cast<CompoundStmt>(outerCtor->getBody());
ASSERT_EQ(body->size(), 1) << "Expected 1 statement (member ctor call)";
CallExpr *memberCtorCall = dyn_cast<CallExpr>(body->body_front());
ASSERT_NE(memberCtorCall, nullptr) << "Expected member constructor call";
```

### Test 27: Member Destructor Calls
**Purpose:** Verify class-type members get destructor calls

**Input C++:**
```cpp
class Resource {
  int *data;
public:
  Resource() { data = new int(42); }
  ~Resource() { delete data; }
  int getValue() const { return *data; }
};

class Container {
  Resource res;
public:
  Container() {}
  ~Container() {}
  int getResourceValue() const { return res.getValue(); }
};
```

**Expected C Output:**
```c
void Container__dtor(struct Container *this) {
  // Derived body (empty)
  Resource__dtor(&this->res);  // ✅ Member destructor call
}
```

**Verification:**
```cpp
ASSERT_NE(containerDtor, nullptr) << "Container destructor not found";
CompoundStmt *body = dyn_cast<CompoundStmt>(containerDtor->getBody());
ASSERT_EQ(body->size(), 1) << "Expected 1 statement (member dtor call)";
CallExpr *memberDtorCall = dyn_cast<CallExpr>(body->body_front());
ASSERT_NE(memberDtorCall, nullptr) << "Expected member destructor call";
```

### Test 28: Complete Chaining - Base, Members, and Derived
**Purpose:** Verify complete chaining with inheritance and members

**Input C++:**
```cpp
class Base {
  int baseVal;
public:
  Base(int v) : baseVal(v) {}
  ~Base() {}
  int getBaseVal() const { return baseVal; }
};

class Member {
  int memberVal;
public:
  Member(int v) : memberVal(v) {}
  ~Member() {}
  int getMemberVal() const { return memberVal; }
};

class Derived : public Base {
  Member mem;
public:
  Derived(int b, int m) : Base(b), mem(m) {}
  ~Derived() {}
  int getMemberValue() const { return mem.getMemberVal(); }
};
```

**Expected Constructor Output:**
```c
void Derived__ctor(struct Derived *this, int b, int m) {
  Base__ctor((struct Base*)this, b);     // 1. Base constructor
  Member__ctor(&this->mem, m);           // 2. Member constructor
  // 3. Derived body (empty)
}
```

**Expected Destructor Output:**
```c
void Derived__dtor(struct Derived *this) {
  // 1. Derived body (empty)
  Member__dtor(&this->mem);              // 2. Member destructor
  Base__dtor((struct Base*)this);        // 3. Base destructor
}
```

**Verification:**
```cpp
// Constructor: Base → Member → Body
CompoundStmt *ctorBody = dyn_cast<CompoundStmt>(derivedCtor->getBody());
ASSERT_EQ(ctorBody->size(), 2) << "Expected 2 statements (base ctor, member ctor)";

CallExpr *baseCtorCall = dyn_cast<CallExpr>(ctorBody->body()[0]);
ASSERT_NE(baseCtorCall, nullptr) << "Expected base constructor call first";

CallExpr *memberCtorCall = dyn_cast<CallExpr>(ctorBody->body()[1]);
ASSERT_NE(memberCtorCall, nullptr) << "Expected member constructor call second";

// Destructor: Body → Member → Base
CompoundStmt *dtorBody = dyn_cast<CompoundStmt>(derivedDtor->getBody());
ASSERT_EQ(dtorBody->size(), 2) << "Expected 2 statements (member dtor, base dtor)";

CallExpr *memberDtorCall = dyn_cast<CallExpr>(dtorBody->body()[0]);
ASSERT_NE(memberDtorCall, nullptr) << "Expected member destructor call first";

CallExpr *baseDtorCall = dyn_cast<CallExpr>(dtorBody->body()[1]);
ASSERT_NE(baseDtorCall, nullptr) << "Expected base destructor call second";
```

### Test 29: Multiple Members - Order Verification
**Purpose:** Verify members constructed in declaration order, destructed in reverse

**Input C++:**
```cpp
class A { public: A() {} ~A() {} };
class B { public: B() {} ~B() {} };
class C { public: C() {} ~C() {} };

class Multi {
  A a;  // Declaration order: a, b, c
  B b;
  C c;
public:
  Multi() : c(), b(), a() {}  // Init list order: c, b, a (different!)
  ~Multi() {}
};
```

**Expected Constructor Order:**
```c
void Multi__ctor(struct Multi *this) {
  A__ctor(&this->a);  // 1. a (declaration order)
  B__ctor(&this->b);  // 2. b
  C__ctor(&this->c);  // 3. c
}
```

**Expected Destructor Order:**
```c
void Multi__dtor(struct Multi *this) {
  C__dtor(&this->c);  // 1. c (reverse declaration order)
  B__dtor(&this->b);  // 2. b
  A__dtor(&this->a);  // 3. a
}
```

---

## Implementation Sequence (TDD)

### Phase 1: Test Setup (Write Failing Tests)
1. ✅ Add Test 26 to `tests/InheritanceTest.cpp`
2. ✅ Add Test 27 to `tests/InheritanceTest.cpp`
3. ✅ Add Test 28 to `tests/InheritanceTest.cpp`
4. ✅ Add Test 29 to `tests/InheritanceTest.cpp`
5. ✅ Run tests → **EXPECT FAILURES** (functions not implemented)
6. ✅ Commit: "test(story63): add failing tests for member ctor/dtor chaining"

### Phase 2: Header Declarations
1. ✅ Add method declarations to `include/CppToCVisitor.h`
2. ✅ Add documentation comments
3. ✅ Commit: "feat(story63): add member chaining method declarations"

### Phase 3: Member Constructor Implementation
1. ✅ Implement `findInitializerForField()` helper
2. ✅ Run tests → verify helper works
3. ✅ Implement `emitMemberConstructorCalls()`
4. ✅ Integrate into `VisitCXXConstructorDecl` (replace lines 207-246)
5. ✅ Run tests → verify Tests 26, 28, 29 constructor parts pass
6. ✅ Refactor while keeping tests green
7. ✅ Commit: "feat(story63): implement member constructor chaining"

### Phase 4: Member Destructor Implementation
1. ✅ Implement `emitMemberDestructorCalls()`
2. ✅ Integrate into `VisitCXXDestructorDecl` (insert at line 388)
3. ✅ Run tests → verify Tests 27, 28, 29 destructor parts pass
4. ✅ Refactor while keeping tests green
5. ✅ Commit: "feat(story63): implement member destructor chaining"

### Phase 5: Integration and Verification
1. ✅ Run full InheritanceTest suite
2. ✅ Verify all 29 tests pass
3. ✅ Run linters (clang-tidy, cppcheck)
4. ✅ Fix any warnings
5. ✅ Commit: "refactor(story63): address linter warnings"

### Phase 6: Code Review and Documentation
1. ✅ Launch review subtask
2. ✅ Address review findings
3. ✅ Update EPICS.md
4. ✅ Commit: "docs(story63): update documentation"

### Phase 7: Git Flow Release
1. ✅ Push all commits
2. ✅ Create release: "v0.63.0 - Complete Constructor/Destructor Chaining"
3. ✅ Close Story #63 on GitHub

---

## Success Criteria

### Functional Requirements
- ✅ Class-type members get constructor calls in explicit constructors
- ✅ Constructor calls use correct arguments from init list
- ✅ Members without init list get default constructor calls
- ✅ Class-type members get destructor calls
- ✅ Construction order: Base → Members (declaration) → Derived body
- ✅ Destruction order: Derived body → Members (reverse) → Base

### Quality Requirements
- ✅ All tests pass (existing + new)
- ✅ No regressions in Epic #5, #6, #7 tests
- ✅ Code follows SOLID principles
- ✅ Single Responsibility: Each helper does one thing
- ✅ Open/Closed: Extensible for future features
- ✅ DRY: Reuses existing patterns
- ✅ No linter warnings

### Documentation Requirements
- ✅ Method documentation comments
- ✅ Implementation plan (this document)
- ✅ EPICS.md updated
- ✅ Git commit messages follow conventions

---

## Risk Mitigation

### Risk 1: Init List Order vs Declaration Order
**Mitigation:** Always iterate `ClassDecl->fields()` for declaration order, NOT `CD->inits()` for init list order.

### Risk 2: Destructor Map Not Populated
**Mitigation:** Ensure `dtorMap` is populated in `VisitCXXDestructorDecl` before calling `emitMemberDestructorCalls()`.

### Risk 3: Regression in Existing Tests
**Mitigation:** Run full test suite after each commit, fix immediately.

### Risk 4: Constructor Expression Casting
**Mitigation:** Use `dyn_cast<CXXConstructExpr>()` safely, handle null case.

---

## References

### Related Stories
- **Story #51:** Constructor chaining (base before derived)
- **Story #52:** Destructor chaining (derived before base)
- **Story #61:** Member initialization list ordering
- **Story #62:** Implicit default and copy constructors
- **Epic #5:** RAII destructor injection for local variables

### Key Files
- `src/CppToCVisitor.cpp` - Visitor implementation
- `include/CppToCVisitor.h` - Visitor header
- `tests/InheritanceTest.cpp` - Test suite

### Clang API
- `CXXConstructorDecl::inits()` - Get init list (order: as written)
- `CXXRecordDecl::fields()` - Get fields (order: declaration)
- `CXXCtorInitializer::isAnyMemberInitializer()` - Check if member init
- `CXXCtorInitializer::getAnyMember()` - Get field being initialized
- `CXXCtorInitializer::getInit()` - Get initialization expression
- `CXXConstructExpr` - Constructor call expression
- `CXXDestructorDecl` - Destructor declaration

---

**Document Version:** 1.0
**Last Updated:** 2025-12-08
**Author:** Claude Code (TDD Pair Programming)
**Status:** Ready for Implementation

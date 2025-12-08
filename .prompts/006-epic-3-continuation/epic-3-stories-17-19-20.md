# Epic #3 Continuation: Stories #17, #19, #20

**Meta-Prompt for Completing Epic #3 Translation Layer**

## Executive Summary

Complete the remaining 50% of Epic #3 (Simple Class Translation) by implementing Stories #17, #19, and #20. This continuation focuses on expression/statement translation and integration testing to finish the core C++ → C translation capability.

**Target**: 15 story points across 3 user stories (#19, #17, #20)
**Dependencies**: Stories #15, #16, #18 complete ✅
**Current Epic #3 Status**: 50% (11/26 story points delivered)
**Architecture Reference**: [ARCHITECTURE.md - Translation Layer](docs/ARCHITECTURE.md#32-translation-layer-recursiveastvisitor)

## Context from Previous Session

### What's Complete ✅

**Story #15**: Class-to-Struct Conversion (3 points)
- `VisitCXXRecordDecl()` converts C++ classes to C structs
- Field layout preserved
- C++ → C mapping stored

**Story #18**: Basic Name Mangling (3 points)
- `NameMangler` class generates unique C function names
- Handles overloads with parameter type suffixes
- Constructor naming: `ClassName__ctor`

**Story #16**: Method-to-Function Conversion (5 points)
- `VisitCXXMethodDecl()` converts methods to C functions
- Adds `struct ClassName *this` as first parameter
- Name mangling applied

### What's Remaining ❌

**Story #19**: Member Access Transformation (5 points) ← **START HERE**
**Story #17**: Constructor Translation (5 points) ← Blocked by #19
**Story #20**: Translation Integration Tests (5 points) ← Blocked by #17, #19

## Critical Success Factors

### 1. Source of Truth
**THE GITHUB PROJECT IS THE ONLY SOURCE OF TRUTH.**

```bash
# Verify Story #19 details
gh issue view 19 --json title,body,state

# Verify Story #17 details
gh issue view 17 --json title,body,state

# Verify Story #20 details
gh issue view 20 --json title,body,state
```

### 2. GitHub Issue Status Management

**CRITICAL**:

1. Mark **Story #19** as in-progress when starting:
   ```bash
   gh issue edit 19 --add-label "in-progress"
   ```

2. Close **Story #19** when complete:
   ```bash
   gh issue close 19 --comment "✅ Story completed: Member access transformation implemented, implicit this handled, unit tests passing, code committed."
   ```

3. Repeat for Stories #17 and #20

4. Close **Epic #3** when all stories complete:
   ```bash
   gh issue close 3 --comment "✅ Epic #3 COMPLETE: All 6 stories (26 story points) delivered, all acceptance criteria passed!"
   ```

### 3. TDD Methodology

**RED-GREEN-REFACTOR** for every feature.

## Implementation Order

### Priority 1: Story #19 - Member Access Transformation (5 points)

**Why First**: Unblocks Stories #17 and #20. This is the critical path.

**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/19

**Objective**: Transform C++ member access expressions to C `this->member` syntax.

**Acceptance Criteria**:
- [ ] Translate MemberExpr (obj.member) to this->member
- [ ] Handle implicit this in method bodies
- [ ] Transform member variable references
- [ ] Transform member function calls
- [ ] Preserve expression types and value categories

**TDD Test Cases**:
1. `ImplicitThisRead`: `return x;` → `return this->x;`
2. `ImplicitThisWrite`: `x = val;` → `this->x = val;`
3. `ExplicitMemberAccess`: `obj.x` → `obj.x` (if obj is struct)
4. `MemberFunctionCall`: `obj.method()` → `ClassName_method(&obj)`

**Implementation Approach**:

```cpp
// Step 1: Add expression translation infrastructure
class CppToCVisitor {
    // Store current context
    ParmVarDecl *currentThisParam = nullptr;
    CXXMethodDecl *currentMethod = nullptr;

public:
    // Main translation entry point
    Expr* translateExpr(Expr *E);

    // Specific translators
    Expr* translateMemberExpr(MemberExpr *ME);
    Expr* translateDeclRefExpr(DeclRefExpr *DRE);
    Expr* translateCallExpr(CallExpr *CE);
    Expr* translateBinaryOperator(BinaryOperator *BO);

    // Statement translation
    Stmt* translateStmt(Stmt *S);
    Stmt* translateReturnStmt(ReturnStmt *RS);
    Stmt* translateExprStmt(Stmt *S);
};

// Step 2: Implement translateExpr (dispatcher)
Expr* CppToCVisitor::translateExpr(Expr *E) {
    if (!E) return nullptr;

    if (MemberExpr *ME = dyn_cast<MemberExpr>(E)) {
        return translateMemberExpr(ME);
    }

    if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(E)) {
        return translateDeclRefExpr(DRE);
    }

    if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
        return translateCallExpr(CE);
    }

    if (BinaryOperator *BO = dyn_cast<BinaryOperator>(E)) {
        return translateBinaryOperator(BO);
    }

    // Default: return as-is
    return E;
}

// Step 3: Implement translateDeclRefExpr (implicit this)
Expr* CppToCVisitor::translateDeclRefExpr(DeclRefExpr *DRE) {
    ValueDecl *D = DRE->getDecl();

    // Check if this is an implicit member access
    if (FieldDecl *FD = dyn_cast<FieldDecl>(D)) {
        // Convert 'x' to 'this->x'
        return builder.arrowMember(
            builder.ref(currentThisParam),
            FD->getName()
        );
    }

    // Regular variable reference
    return builder.ref(D);
}

// Step 4: Implement translateMemberExpr (explicit access)
Expr* CppToCVisitor::translateMemberExpr(MemberExpr *ME) {
    Expr *Base = ME->getBase();
    ValueDecl *Member = ME->getMemberDecl();

    // Translate base recursively
    Expr *TranslatedBase = translateExpr(Base);

    // Determine if we need -> or .
    if (Base->getType()->isPointerType()) {
        return builder.arrowMember(TranslatedBase, Member->getName());
    } else {
        return builder.member(TranslatedBase, Member->getName());
    }
}
```

**Files to Modify**:
- `include/CppToCVisitor.h`: Add `translateExpr()` and helper methods
- `src/CppToCVisitor.cpp`: Implement translation methods
- `src/CppToCVisitor.cpp`: Update `VisitCXXMethodDecl()` to call `translateStmt()` for body
- `tests/CppToCVisitorTest.cpp`: Add 4+ test cases

**Definition of Done**:
- [ ] `translateExpr()` infrastructure implemented
- [ ] Implicit `this` handled (DeclRefExpr → this->member)
- [ ] Explicit member access handled (MemberExpr)
- [ ] Expression types preserved
- [ ] 4 unit tests passing
- [ ] Code committed to develop branch
- [ ] Issue #19 closed

---

### Priority 2: Story #17 - Constructor Translation (5 points)

**Why Second**: Requires Story #19's expression translation infrastructure.

**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/17

**Objective**: Convert C++ constructors to C init functions.

**Acceptance Criteria**:
- [ ] VisitCXXConstructorDecl() handles constructors
- [ ] Generate `ClassName__ctor(struct ClassName *this, ...params)`
- [ ] Translate member initializers to assignments
- [ ] Translate constructor body
- [ ] Handle default constructor (no params)
- [ ] Handle parameterized constructors

**TDD Test Cases**:
1. `DefaultConstructor`: `Point() {}` → `void Point__ctor(struct Point *this) {}`
2. `MemberInitializers`: `Point(int x, int y) : x(x), y(y) {}` → assignments
3. `ConstructorWithBody`: Constructor with statements in body

**Implementation Approach**:

```cpp
bool CppToCVisitor::VisitCXXConstructorDecl(CXXConstructorDecl *CD) {
    if (CD->isImplicit()) return true;

    CXXRecordDecl *Parent = CD->getParent();
    RecordDecl *CStruct = getCStruct(Parent);

    // Build parameter list: this + original params
    std::vector<ParmVarDecl*> params;

    // Add 'this' parameter
    ParmVarDecl *thisParam = builder.param(
        builder.ptrType(builder.structType(Parent->getName())),
        "this"
    );
    params.push_back(thisParam);

    // Add original parameters
    for (ParmVarDecl *Param : CD->parameters()) {
        params.push_back(builder.param(Param->getType(), Param->getName()));
    }

    // Create C init function
    std::string funcName = mangler.mangleConstructor(CD);
    FunctionDecl *CFunc = builder.funcDecl(
        funcName,
        builder.voidType(),
        params,
        nullptr  // Body built below
    );

    // Build function body
    std::vector<Stmt*> stmts;

    // Set current context for expression translation
    currentThisParam = thisParam;
    currentMethod = CD;

    // Translate member initializers: this->x = x;
    for (CXXCtorInitializer *Init : CD->inits()) {
        if (Init->isAnyMemberInitializer()) {
            FieldDecl *Field = Init->getAnyMember();
            Expr *InitExpr = Init->getInit();

            // Translate: this->field = initExpr;
            stmts.push_back(builder.exprStmt(
                builder.assign(
                    builder.arrowMember(
                        builder.ref(thisParam),
                        Field->getName()
                    ),
                    translateExpr(InitExpr)  // Use Story #19's translator!
                )
            ));
        }
    }

    // Translate constructor body statements
    if (CD->hasBody()) {
        CompoundStmt *Body = dyn_cast<CompoundStmt>(CD->getBody());
        for (Stmt *S : Body->body()) {
            stmts.push_back(translateStmt(S));  // Use Story #19's translator!
        }
    }

    // Clear context
    currentThisParam = nullptr;
    currentMethod = nullptr;

    // Set function body
    CFunc->setBody(builder.block(stmts));

    // Store mapping
    ctorMap[CD] = CFunc;

    return true;
}
```

**Files to Modify**:
- `include/CppToCVisitor.h`: Add `VisitCXXConstructorDecl()`, `ctorMap`
- `src/CppToCVisitor.cpp`: Implement `VisitCXXConstructorDecl()`
- `tests/CppToCVisitorTest.cpp`: Add 3+ test cases

**Definition of Done**:
- [ ] VisitCXXConstructorDecl() implemented
- [ ] Member initializers translated to assignments
- [ ] Constructor body translated
- [ ] 3 unit tests passing
- [ ] Code committed to develop branch
- [ ] Issue #17 closed

---

### Priority 3: Story #20 - Translation Integration Tests (5 points)

**Why Last**: Validates that Stories #15-19 work together end-to-end.

**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/20

**Objective**: Create end-to-end integration tests for complete C++ → C translation.

**Acceptance Criteria**:
- [ ] Integration test framework setup
- [ ] Test complete C++ class → C struct + functions transformation
- [ ] Validate generated C AST structure
- [ ] Test C++ to C mapping correctness
- [ ] End-to-end test cases (5+ scenarios)
- [ ] AST validation (no null nodes, correct types)

**TDD Test Cases**:
1. `EmptyClass`: Full translation of empty class
2. `SimpleClassWithMethod`: Class with one getter method
3. `ConstructorTranslation`: Class with constructor and member initializers
4. `OverloadedMethods`: Class with overloaded methods → unique C names
5. `ComplexClass`: Rectangle with constructor + 3 methods

**Implementation Approach**:

```cpp
class TranslationIntegrationTest : public ::testing::Test {
protected:
    ASTContext Context;
    CNodeBuilder builder;
    CppToCVisitor visitor;

    // Helper: Parse C++ code and run translation
    TranslationUnitDecl* translateCode(const std::string &cppCode) {
        // 1. Parse C++ code using Clang
        // 2. Run visitor on C++ AST
        // 3. Return translated C AST
    }

    // Helper: Validate C AST structure
    void validateCAST(TranslationUnitDecl *TU) {
        // Check no null nodes
        // Check all types are valid
        // Check all references resolved
    }
};

TEST_F(TranslationIntegrationTest, EmptyClass) {
    const char *cpp = "class Empty {};";
    TranslationUnitDecl *CTU = translateCode(cpp);

    // Validate: struct Empty {}; generated
    ASSERT_EQ(CTU->decls_size(), 1);

    RecordDecl *RD = dyn_cast<RecordDecl>(*CTU->decls_begin());
    ASSERT_TRUE(RD != nullptr);
    EXPECT_EQ(RD->getName(), "Empty");
}

TEST_F(TranslationIntegrationTest, ComplexClass) {
    const char *cpp = R"(
        class Rectangle {
            int width, height;
        public:
            Rectangle(int w, int h) : width(w), height(h) {}
            int getWidth() { return width; }
            int getHeight() { return height; }
            int area() { return width * height; }
        };
    )";

    TranslationUnitDecl *CTU = translateCode(cpp);

    // Validate: struct + 4 functions (ctor + 3 methods)
    ASSERT_EQ(CTU->decls_size(), 5);

    // Validate struct
    RecordDecl *RD = dyn_cast<RecordDecl>(*CTU->decls_begin());
    ASSERT_TRUE(RD != nullptr);
    EXPECT_EQ(RD->field_size(), 2);

    // Validate functions (ctor + 3 methods)
    // Check signatures, bodies, this parameters
}
```

**Files to Create**:
- `tests/TranslationIntegrationTest.cpp`: End-to-end tests
- `CMakeLists.txt`: Add integration test

**Definition of Done**:
- [ ] Integration test framework setup
- [ ] 5 end-to-end test cases passing
- [ ] AST validation implemented
- [ ] All translation scenarios covered
- [ ] Code committed to develop branch
- [ ] Issue #20 closed

---

## Implementation Summary

### Execution Order

1. **Story #19** (5 points) - Start here, unblocks everything
2. **Story #17** (5 points) - Uses #19's expression translation
3. **Story #20** (5 points) - Validates #15-19 work together

### Git Workflow

```bash
# After Story #19
git add .
git commit -m "feat(epic3): implement member access transformation (Story #19)

- translateExpr() infrastructure implemented
- Implicit this handled (x -> this->x)
- Explicit member access (obj.member)
- Expression types preserved
- 4 unit tests passing

Closes #19"
git push origin develop

# After Story #17
git add .
git commit -m "feat(epic3): implement constructor translation (Story #17)

- VisitCXXConstructorDecl() handles constructors
- Member initializers translated to assignments
- Constructor body translated
- 3 unit tests passing

Closes #17"
git push origin develop

# After Story #20
git add .
git commit -m "feat(epic3): add translation integration tests (Story #20)

- Integration test framework setup
- 5 end-to-end test cases passing
- Complete C++ to C translation validated
- AST validation implemented

Closes #20"
git push origin develop

# Close Epic #3
gh issue close 3 --comment "✅ Epic #3 COMPLETE: All 6 stories (26 story points) delivered!"
```

### Final Deliverables

**Code**:
- Updated `include/CppToCVisitor.h` with translation methods
- Updated `src/CppToCVisitor.cpp` with implementations
- Updated `tests/CppToCVisitorTest.cpp` with 7+ new tests
- New `tests/TranslationIntegrationTest.cpp` with 5+ tests

**Documentation**:
- `.prompts/completed/006-epic-3-continuation-RESULTS.md`
- Update `EPIC-3-VERIFICATION.md` (complete all 26 acceptance criteria)

**GitHub**:
- Issues #19, #17, #20 closed
- Epic #3 closed
- All code pushed to develop

### Success Metrics

- **Story Points**: 15/15 delivered (completing 26/26 total for Epic #3)
- **Acceptance Criteria**: 15/15 passed (completing 30/30 total)
- **Tests**: 12+ new tests passing (completing 20+ total)
- **Epic #3**: 100% complete ✅

---

## Execution Instructions

1. **Read and understand** this document
2. **Verify GitHub issues** for Stories #19, #17, #20
3. **Mark Epic #3 as in-progress** (if not already)
4. **Implement Story #19 FIRST** (critical path!)
5. **Follow TDD**: RED → GREEN → REFACTOR
6. **Commit after each story**
7. **Close issues** with detailed comments
8. **Generate results summary**
9. **Close Epic #3** with celebration! 🎉

**Repository**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler
**Branch**: develop
**Current Epic #3 Progress**: 50% → 100%

**Let's finish Epic #3! 🚀**

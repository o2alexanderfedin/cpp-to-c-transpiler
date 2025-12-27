# Phase 39-01a: Foundation Infrastructure & FunctionHandler

## Objective

Implement test infrastructure and FunctionHandler as the first working component of the transpiler. This establishes the pattern for all future handlers and validates the TDD workflow.

**Goal:** Get test infrastructure working and transpile simple C++ functions to C.

**Scope:** Tasks 1-3 from Phase 39-01 (Infrastructure + FunctionHandler only)

## Context

@docs/architecture/10-phase1-detailed-plan.md - Steps 0-10 (infrastructure + FunctionHandler)
@docs/architecture/08-test-fixtures-design.md - Test infrastructure design
@docs/architecture/handlers/FunctionHandler.md - Handler specification
@docs/architecture/02-handler-chain-pattern.md - Handler interfaces
@include/CNodeBuilder.h - Existing C AST builder (reuse this)
@CMakeLists.txt - Build configuration

## Tasks

### Task 1: Create MockASTContext Test Fixture
**Type**: auto
**Estimated**: 4-5 hours

**Action**: Create `tests/fixtures/MockASTContext.h` and `tests/fixtures/MockASTContext.cpp`

**Implementation:**
```cpp
// MockASTContext.h
#pragma once
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include <memory>
#include <string>
#include <vector>

class MockASTContext {
private:
    std::unique_ptr<clang::ASTContext> context_;
    std::vector<std::unique_ptr<clang::Decl>> ownedDecls_;

    clang::QualType parseType(const std::string& typeStr);
    clang::ParmVarDecl* createParameter(const std::string& paramStr);

public:
    MockASTContext();
    ~MockASTContext();

    clang::ASTContext& getContext() { return *context_; }

    // C++ AST node creation methods
    clang::FunctionDecl* createFunction(
        const std::string& returnType,
        const std::string& name,
        const std::vector<std::string>& params,
        clang::Stmt* body = nullptr
    );

    clang::VarDecl* createVariable(
        const std::string& type,
        const std::string& name,
        clang::Expr* init = nullptr
    );

    clang::IntegerLiteral* createIntLiteral(int value);
    clang::FloatingLiteral* createFloatLiteral(double value);

    clang::BinaryOperator* createBinaryOp(
        clang::BinaryOperatorKind op,
        clang::Expr* lhs,
        clang::Expr* rhs
    );

    clang::DeclRefExpr* createVarRef(clang::VarDecl* var);
    clang::ReturnStmt* createReturnStmt(clang::Expr* expr = nullptr);
    clang::CompoundStmt* createCompoundStmt(const std::vector<clang::Stmt*>& stmts);
};
```

**Verify:**
- Compiles without errors
- Can create simple function AST nodes
- Memory properly managed (no leaks)

---

### Task 2: Create HandlerTestFixture Base Class
**Type**: auto
**Estimated**: 2-3 hours

**Action**: Create `tests/fixtures/HandlerTestFixture.h` and `.cpp`

**Implementation:**
```cpp
// HandlerTestFixture.h
#pragma once
#include "MockASTContext.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include <gtest/gtest.h>

class HandlerTestFixture : public ::testing::Test {
protected:
    MockASTContext mockCpp;
    MockASTContext mockC;
    std::unique_ptr<CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    void SetUp() override;
    void TearDown() override;

    // Helper assertion methods
    void assertFunctionEquals(
        clang::FunctionDecl* actual,
        const std::string& expectedName,
        const std::string& expectedReturnType,
        size_t expectedParamCount
    );
};
```

**Verify:**
- Reduces test boilerplate
- Proper setup/teardown
- Helper methods work

---

### Task 3: Create Handler Infrastructure
**Type**: auto
**Estimated**: 3-4 hours

**Action**: Create base handler classes and context

**Files to create:**

1. `include/handlers/ASTHandler.h`:
   - Base interface for all handlers
   - `canHandle()` and `handle()` methods

2. `include/handlers/HandlerContext.h` + `src/handlers/HandlerContext.cpp`:
   - C++ and C AST contexts
   - CNodeBuilder reference
   - Symbol tables (declMap, typeMap)
   - Registration and lookup methods

3. Update `CMakeLists.txt`:
   - Add handlers library
   - Add test fixtures library
   - Configure Google Test

**Verify:**
- All files compile
- Interfaces follow SOLID
- CMake properly configured

---

### Task 4: Implement FunctionHandler with TDD (20+ tests)
**Type**: auto
**Estimated**: 4-6 hours

**Action**: Create `include/handlers/FunctionHandler.h` and `src/handlers/FunctionHandler.cpp`

**TDD Cycles (following detailed plan):**

**Test 1: Empty Function**
```cpp
TEST_F(FunctionHandlerTest, EmptyFunction) {
    auto* cppFunc = mockCpp.createFunction("void", "foo", {}, nullptr);

    FunctionHandler handler;
    auto* cDecl = handler.handleDecl(cppFunc, *context);

    ASSERT_NE(cDecl, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(cDecl);
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "foo");
    EXPECT_TRUE(cFunc->getReturnType()->isVoidType());
    EXPECT_EQ(cFunc->getNumParams(), 0);
}
```

**Implement to pass → Refactor**

**Test 2-10:** (Continue with detailed plan steps)
- FunctionWithIntReturn
- FunctionWithParams
- FunctionWithTwoParams
- FunctionWithFloatReturn
- etc.

**Implementation Pattern:**
```cpp
class FunctionHandler : public ASTHandler {
public:
    bool canHandle(const clang::Decl* D) const override;
    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override;

private:
    clang::FunctionDecl* translateFunction(
        const clang::FunctionDecl* cppFunc,
        HandlerContext& ctx
    );

    std::vector<clang::ParmVarDecl*> translateParameters(
        const clang::FunctionDecl* cppFunc,
        HandlerContext& ctx
    );
};
```

**Verify:**
- 20+ unit tests pass
- Simple functions translate correctly
- Parameters handled
- Return types correct
- Registered in HandlerContext

---

### Task 5: Create Basic Integration Test
**Type**: auto
**Estimated**: 1-2 hours

**Action**: Write one integration test to validate handler infrastructure works

**Test:**
```cpp
TEST(IntegrationTest, SimpleFunctionTranslation) {
    // Setup
    MockASTContext mockCpp;
    MockASTContext mockC;
    CNodeBuilder builder(mockC.getContext());
    HandlerContext context(mockCpp.getContext(), mockC.getContext(), builder);

    // Create C++ function
    auto* cppFunc = mockCpp.createFunction("int", "add", {"int a", "int b"}, nullptr);

    // Translate
    FunctionHandler handler;
    auto* cFunc = handler.handleDecl(cppFunc, context);

    // Verify
    ASSERT_NE(cFunc, nullptr);
    // ... assertions
}
```

**Verify:**
- Integration test passes
- Handler cooperates with context
- Symbol registration works

---

## Verification

**Phase 39-01a Completion Criteria:**

1. **Test Infrastructure:**
   - [ ] MockASTContext compiles and works
   - [ ] HandlerTestFixture reduces boilerplate
   - [ ] Can create C++ AST nodes for testing

2. **Handler Infrastructure:**
   - [ ] ASTHandler base interface complete
   - [ ] HandlerContext manages state correctly
   - [ ] CMake properly configured

3. **FunctionHandler:**
   - [ ] 20+ unit tests pass (100%)
   - [ ] Simple functions translate correctly
   - [ ] Parameters handled properly
   - [ ] Return types correct

4. **Integration:**
   - [ ] At least 1 integration test passes
   - [ ] Handler works with context
   - [ ] Symbol registration works

5. **Code Quality:**
   - [ ] No compiler warnings
   - [ ] Code follows SOLID principles
   - [ ] Well documented
   - [ ] Clean and readable

## Success Criteria

✅ Test infrastructure complete and reusable
✅ Handler infrastructure follows architecture design
✅ FunctionHandler fully implemented with TDD
✅ 20+ tests passing for FunctionHandler
✅ Pattern established for future handlers
✅ Ready for Phase 39-01b (VariableHandler + ExpressionHandler)

**Estimated Total:** 14-20 hours (achievable in focused session)

## Output

Create `.planning/phases/39-foundation-implementation/39-01a-SUMMARY.md` with:

**Deliverables:**
- Test infrastructure files (MockASTContext, HandlerTestFixture)
- Handler infrastructure files (ASTHandler, HandlerContext)
- FunctionHandler implementation
- 20+ tests passing

**Statistics:**
- Files created
- LOC implementation
- LOC tests
- Test count

**Next Steps:**
- Phase 39-01b: VariableHandler + ExpressionHandler
- Phase 39-01c: StatementHandler + Integration
- Phase 39-01d: E2E + CodeGenerator + Pipeline

**Commit:**
Format: `feat(phase1): Add test infrastructure and FunctionHandler`

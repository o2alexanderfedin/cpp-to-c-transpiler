# Phase 1 Detailed Implementation Plan: TDD Step-by-Step

## Objective

Implement the complete foundation for the C++ to C transpiler by building basic functions, local variables, arithmetic expressions, and simple statements. This phase establishes the end-to-end pipeline and handler infrastructure.

**Goal:** Get simple C++ programs transpiling to working C code.

---

## Scope

### In Scope
- Standalone functions (no classes/methods)
- Local variables with initialization
- Arithmetic operators: `+`, `-`, `*`, `/`, `%`
- Integer and float literals
- Variable references
- Return statements
- Function calls (no overloading)
- Compound statements (`{ }` blocks)

### Out of Scope (Future Phases)
- Global variables (Phase 3)
- Control flow (if/while/for) (Phase 2)
- Classes and methods (Phase 6)
- Pointers (Phase 5)
- Enums (Phase 8)
- Templates (Phase 10)

---

## Prerequisites

1. Clang/LLVM installed and configured
2. CMake build system setup
3. Google Test framework integrated
4. Basic understanding of Clang AST

---

## Implementation Steps

### Step 0: Setup Test Infrastructure (8-10 hours)

#### Step 0.1: Create MockASTContext (4-5 hours)

**Test:** None (infrastructure)

**Implementation:**
1. Create `tests/fixtures/MockASTContext.h` and `.cpp`
2. Implement constructor/destructor with AST context ownership
3. Implement `createFunction()` method:
   ```cpp
   clang::FunctionDecl* MockASTContext::createFunction(
       const std::string& returnType,
       const std::string& name,
       const std::vector<std::string>& params,
       clang::Stmt* body
   ) {
       // Parse return type
       clang::QualType retType = parseType(returnType);

       // Create function declaration
       clang::FunctionDecl* func = clang::FunctionDecl::Create(
           *cppContext_,
           /* DeclContext */ cppContext_->getTranslationUnitDecl(),
           clang::SourceLocation(),
           clang::SourceLocation(),
           clang::DeclarationName(&cppContext_->Idents.get(name)),
           retType,
           /* TypeSourceInfo */ nullptr,
           clang::SC_None
       );

       // Create and add parameters
       std::vector<clang::ParmVarDecl*> paramDecls;
       for (const auto& paramStr : params) {
           paramDecls.push_back(createParameter(paramStr));
       }
       func->setParams(paramDecls);

       // Set body if provided
       if (body) {
           func->setBody(body);
       }

       ownedDecls_.push_back(std::unique_ptr<clang::Decl>(func));
       return func;
   }
   ```

4. Implement `createVariable()`, `createIntLiteral()`, `createBinaryOp()`, `createVarRef()`, `createReturnStmt()`, `createCompoundStmt()`
5. Implement `parseType()` helper for simple types

**Verification:**
- Compiles without errors
- Can create simple function AST nodes
- Memory is properly managed

#### Step 0.2: Create CNodeBuilder (2-3 hours)

**Test:** None (infrastructure, tested through handlers)

**Implementation:**
1. Create `include/CNodeBuilder.h` and `src/CNodeBuilder.cpp`
2. Implement C AST node creation methods:
   ```cpp
   clang::FunctionDecl* CNodeBuilder::createFunctionDecl(
       const std::string& name,
       clang::QualType returnType,
       const std::vector<clang::ParmVarDecl*>& params
   ) {
       auto* func = clang::FunctionDecl::Create(
           cContext_,
           cContext_.getTranslationUnitDecl(),
           clang::SourceLocation(),
           clang::SourceLocation(),
           clang::DeclarationName(&cContext_.Idents.get(name)),
           returnType,
           nullptr,
           clang::SC_None
       );
       func->setParams(params);
       return func;
   }
   ```

3. Implement `createParmVarDecl()`, `createDeclRefExpr()`, `createBinaryOperator()`, `createReturnStmt()`, `createCompoundStmt()`

**Verification:**
- Compiles without errors
- Methods create valid C AST nodes

#### Step 0.3: Create HandlerTestFixture (1-2 hours)

**Test:** None (base class for tests)

**Implementation:**
1. Create `tests/fixtures/HandlerTestFixture.h`
2. Implement base test class:
   ```cpp
   class HandlerTestFixture : public ::testing::Test {
   protected:
       std::unique_ptr<MockASTContext> mock_;
       std::unique_ptr<CNodeBuilder> builder_;
       std::unique_ptr<HandlerContext> context_;

       void SetUp() override {
           mock_ = std::make_unique<MockASTContext>();
           builder_ = std::make_unique<CNodeBuilder>(mock_->getCContext());
           context_ = std::make_unique<HandlerContext>(
               mock_->getCppContext(),
               mock_->getCContext(),
               *builder_
           );
       }

       void TearDown() override {
           context_.reset();
           builder_.reset();
           mock_.reset();
       }
   };
   ```

**Verification:**
- Compiles without errors
- SetUp/TearDown work correctly

#### Step 0.4: Setup CMake (1 hour)

**Implementation:**
1. Create `tests/CMakeLists.txt`
2. Add test fixtures library target
3. Add unit test discovery
4. Configure for GoogleTest

**Verification:**
- `cmake -B build` succeeds
- `cmake --build build` compiles tests

---

### Step 1: FunctionHandler - Empty Function (1 hour)

**TDD Cycle:**

#### RED: Write Failing Test
```cpp
// tests/unit/handlers/FunctionHandlerTest.cpp
class FunctionHandlerTest : public HandlerTestFixture {};

TEST_F(FunctionHandlerTest, EmptyFunction) {
    // Arrange: Create C++ empty function
    auto* cppFunc = getMock().createFunction("void", "foo", {}, nullptr);

    // Act: Translate
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, getContext());

    // Assert: Verify C function created
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "foo");
    EXPECT_EQ(cFunc->getNumParams(), 0);
    EXPECT_TRUE(cFunc->getReturnType()->isVoidType());
}
```

**Run test:** `ctest -R FunctionHandlerTest.EmptyFunction` → **FAILS** (handler doesn't exist)

#### GREEN: Minimal Implementation
```cpp
// include/handlers/FunctionHandler.h
class FunctionHandler : public ASTHandler {
public:
    bool canHandle(const clang::Decl* D) const override {
        return llvm::isa<clang::FunctionDecl>(D);
    }

    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override {
        auto* FD = llvm::cast<clang::FunctionDecl>(D);

        // Create C function with same name and return type
        std::string name = FD->getNameAsString();
        clang::QualType returnType = FD->getReturnType();

        auto* cFunc = ctx.getBuilder().createFunctionDecl(name, returnType, {});

        // Register mapping
        ctx.registerDecl(FD, cFunc);

        return cFunc;
    }
};
```

**Run test:** → **PASSES**

#### REFACTOR: Clean up (if needed)
- Code is already clean for this simple case

---

### Step 2: FunctionHandler - With Return Type (0.5 hour)

#### RED: Write Failing Test
```cpp
TEST_F(FunctionHandlerTest, FunctionWithIntReturn) {
    auto* cppFunc = getMock().createFunction("int", "bar", {}, nullptr);

    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, getContext());

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "bar");
    EXPECT_TRUE(cFunc->getReturnType()->isIntegerType());
}
```

**Run test:** → **PASSES** (already works from Step 1!)

---

### Step 3: FunctionHandler - With Parameters (1 hour)

#### RED: Write Failing Test
```cpp
TEST_F(FunctionHandlerTest, FunctionWithParameters) {
    auto* cppFunc = getMock().createFunction("int", "add", {"int a", "int b"}, nullptr);

    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, getContext());

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
    EXPECT_EQ(cFunc->getParamDecl(0)->getNameAsString(), "a");
    EXPECT_EQ(cFunc->getParamDecl(1)->getNameAsString(), "b");
}
```

**Run test:** → **FAILS** (no parameters translated)

#### GREEN: Implement Parameter Translation
```cpp
clang::Decl* FunctionHandler::handleDecl(const clang::Decl* D, HandlerContext& ctx) {
    auto* FD = llvm::cast<clang::FunctionDecl>(D);

    std::string name = FD->getNameAsString();
    clang::QualType returnType = FD->getReturnType();

    // Translate parameters
    std::vector<clang::ParmVarDecl*> cParams;
    for (auto* param : FD->parameters()) {
        clang::QualType paramType = param->getType();
        std::string paramName = param->getNameAsString();

        auto* cParam = ctx.getBuilder().createParmVarDecl(paramName, paramType);
        cParams.push_back(cParam);
    }

    auto* cFunc = ctx.getBuilder().createFunctionDecl(name, returnType, cParams);
    ctx.registerDecl(FD, cFunc);

    return cFunc;
}
```

**Run test:** → **PASSES**

**Continue this pattern for all 18 FunctionHandler tests...**

---

### Step 4-6: Implement Remaining FunctionHandler Tests (4-6 hours)

Follow TDD cycle for:
- Function with body
- Function with local variables
- Static function
- Inline function
- Function calling another
- etc.

Each iteration:
1. Write test (RED)
2. Make it pass (GREEN)
3. Refactor if needed

---

### Step 7: VariableHandler - Uninitialized Variable (1 hour)

#### RED: Write Failing Test
```cpp
class VariableHandlerTest : public HandlerTestFixture {};

TEST_F(VariableHandlerTest, UninitializedLocalInt) {
    auto* cppVar = getMock().createVariable("int", "x", nullptr, false);

    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, getContext());

    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);
    EXPECT_EQ(cVar->getNameAsString(), "x");
    EXPECT_TRUE(cVar->getType()->isIntegerType());
    EXPECT_FALSE(cVar->hasInit());
}
```

**Run test:** → **FAILS** (VariableHandler doesn't exist)

#### GREEN: Implement VariableHandler
```cpp
class VariableHandler : public ASTHandler {
public:
    bool canHandle(const clang::Decl* D) const override {
        return llvm::isa<clang::VarDecl>(D);
    }

    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override {
        auto* VD = llvm::cast<clang::VarDecl>(D);

        std::string name = VD->getNameAsString();
        clang::QualType type = VD->getType();

        // Create C variable
        auto* cVar = ctx.getBuilder().createVarDecl(name, type);

        // Handle initialization if present
        if (VD->hasInit()) {
            // Delegate to ExpressionHandler
            clang::Expr* initExpr = VD->getInit();
            clang::Expr* cInitExpr = translateExpr(initExpr, ctx);
            cVar->setInit(cInitExpr);
        }

        ctx.registerDecl(VD, cVar);
        return cVar;
    }

private:
    clang::Expr* translateExpr(clang::Expr* E, HandlerContext& ctx) {
        // TODO: Implement or delegate to ExpressionHandler
        return nullptr;
    }
};
```

**Run test:** → **PASSES** (for uninitialized case)

---

### Step 8-15: Complete VariableHandler (3-4 hours)

Follow TDD for remaining 14 tests:
- Initialized variables
- Different types
- Const variables
- etc.

---

### Step 16: ExpressionHandler - Integer Literal (0.5 hour)

#### RED: Write Failing Test
```cpp
class ExpressionHandlerTest : public HandlerTestFixture {};

TEST_F(ExpressionHandlerTest, IntegerLiteral_Positive) {
    auto* cppLiteral = getMock().createIntLiteral(42);

    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppLiteral, getContext());

    auto* cLiteral = llvm::dyn_cast<clang::IntegerLiteral>(result);
    ASSERT_NE(cLiteral, nullptr);
    EXPECT_EQ(cLiteral->getValue().getSExtValue(), 42);
}
```

**Run test:** → **FAILS**

#### GREEN: Implement ExpressionHandler
```cpp
class ExpressionHandler : public ASTHandler {
public:
    bool canHandle(const clang::Expr* E) const override {
        return true;  // Handles all expressions
    }

    clang::Expr* handleExpr(const clang::Expr* E, HandlerContext& ctx) override {
        // Dispatch based on expression kind
        if (auto* IL = llvm::dyn_cast<clang::IntegerLiteral>(E)) {
            return handleIntegerLiteral(IL, ctx);
        }
        // ... other cases

        return nullptr;
    }

private:
    clang::Expr* handleIntegerLiteral(const clang::IntegerLiteral* IL, HandlerContext& ctx) {
        // Integer literals pass through unchanged
        return const_cast<clang::IntegerLiteral*>(IL);
    }
};
```

**Run test:** → **PASSES**

---

### Step 17-30: Complete Expression Literals (2 hours)

TDD for:
- Negative integers
- Zero
- Float literals
- Double literals

---

### Step 31: ExpressionHandler - Binary Addition (1 hour)

#### RED: Write Failing Test
```cpp
TEST_F(ExpressionHandlerTest, BinaryAdd) {
    auto* varA = getMock().createVariable("int", "a");
    auto* varB = getMock().createVariable("int", "b");
    auto* refA = getMock().createVarRef(varA);
    auto* refB = getMock().createVarRef(varB);
    auto* cppExpr = getMock().createBinaryOp(clang::BO_Add, refA, refB);

    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, getContext());

    auto* cExpr = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(cExpr, nullptr);
    EXPECT_EQ(cExpr->getOpcode(), clang::BO_Add);
}
```

**Run test:** → **FAILS**

#### GREEN: Implement Binary Operator
```cpp
clang::Expr* ExpressionHandler::handleBinaryOperator(
    const clang::BinaryOperator* BO,
    HandlerContext& ctx
) {
    // Recursively translate operands
    clang::Expr* lhs = handleExpr(BO->getLHS(), ctx);
    clang::Expr* rhs = handleExpr(BO->getRHS(), ctx);

    // Create C binary operator
    return ctx.getBuilder().createBinaryOperator(
        BO->getOpcode(),
        lhs,
        rhs,
        BO->getType()
    );
}
```

**Run test:** → **PASSES**

---

### Step 32-50: Complete ExpressionHandler (6-8 hours)

TDD for all 35 expression tests:
- All arithmetic operators
- Variable references
- Complex expressions
- Function calls
- Implicit casts

---

### Step 51: StatementHandler - Return Statement (0.5 hour)

#### RED: Write Failing Test
```cpp
class StatementHandlerTest : public HandlerTestFixture {};

TEST_F(StatementHandlerTest, ReturnStmtWithValue) {
    auto* literal = getMock().createIntLiteral(42);
    auto* cppReturn = getMock().createReturnStmt(literal);

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppReturn, getContext());

    auto* cReturn = llvm::dyn_cast<clang::ReturnStmt>(result);
    ASSERT_NE(cReturn, nullptr);
    ASSERT_NE(cReturn->getRetValue(), nullptr);
}
```

**Run test:** → **FAILS**

#### GREEN: Implement StatementHandler
```cpp
class StatementHandler : public ASTHandler {
public:
    bool canHandle(const clang::Stmt* S) const override {
        return true;  // Handles all statements
    }

    clang::Stmt* handleStmt(const clang::Stmt* S, HandlerContext& ctx) override {
        if (auto* RS = llvm::dyn_cast<clang::ReturnStmt>(S)) {
            return handleReturnStmt(RS, ctx);
        }
        // ... other cases

        return nullptr;
    }

private:
    clang::Stmt* handleReturnStmt(const clang::ReturnStmt* RS, HandlerContext& ctx) {
        clang::Expr* retValue = nullptr;
        if (RS->getRetValue()) {
            // Delegate to ExpressionHandler
            retValue = translateExpr(RS->getRetValue(), ctx);
        }

        return ctx.getBuilder().createReturnStmt(retValue);
    }
};
```

**Run test:** → **PASSES**

---

### Step 52-63: Complete StatementHandler (2-3 hours)

TDD for all 12 statement tests:
- Empty compound stmt
- Compound with statements
- Return void
- Return with expression
- Declaration statements

---

### Step 64: Integration Test - Function With Local Variable (1 hour)

```cpp
// tests/integration/handlers/Phase1IntegrationTest.cpp
TEST(Phase1IntegrationTest, FunctionWithLocalVariableAndReturn) {
    MockASTContext mock;

    // Create: int foo() { int x = 10; return x; }
    auto* literal = mock.createIntLiteral(10);
    auto* varX = mock.createVariable("int", "x", literal);
    auto* varRef = mock.createVarRef(varX);
    auto* returnStmt = mock.createReturnStmt(varRef);
    auto* body = mock.createCompoundStmt({varX, returnStmt});
    auto* func = mock.createFunction("int", "foo", {}, body);

    // Translate with full handler chain
    HandlerRegistry registry;
    registry.registerHandler(new FunctionHandler());
    registry.registerHandler(new VariableHandler());
    registry.registerHandler(new ExpressionHandler());
    registry.registerHandler(new StatementHandler());

    CNodeBuilder builder(mock.getCContext());
    HandlerContext ctx(mock.getCppContext(), mock.getCContext(), builder);
    TranslationOrchestrator orchestrator(registry, ctx, /* C TU */);

    clang::Decl* result = orchestrator.translateDecl(func);

    // Verify complete C AST structure
    ASSERT_NE(result, nullptr);
    // ... detailed assertions
}
```

---

### Step 65-88: Complete Integration Tests (5-7 hours)

Write and pass all 25 integration tests from test plan.

---

### Step 89: E2E Test - Simple Program (2 hours)

```cpp
TEST(TranspilerE2ETest, SimpleProgram) {
    IntegrationTestHarness harness;

    auto result = harness.runTest(
        R"(
            int add(int a, int b) {
                return a + b;
            }
            int main() {
                return add(3, 4);
            }
        )"
    );

    ASSERT_TRUE(result.transpilationSuccess);
    ASSERT_TRUE(result.compilationSuccess);
    EXPECT_EQ(result.exitCode, 7);
}
```

**This requires:**
1. Implement IntegrationTestHarness
2. Connect to full transpilation pipeline
3. Invoke gcc to compile
4. Run and verify output

---

### Step 90-98: Complete E2E Tests (3-4 hours)

Write and pass all 10 E2E tests.

---

## Verification Checklist

After completing all steps:

### Unit Tests
- [ ] All 80 unit tests pass
- [ ] 100% handler code coverage
- [ ] Tests run in < 5 seconds

### Integration Tests
- [ ] All 25 integration tests pass
- [ ] Multi-handler scenarios work
- [ ] Tests run in < 30 seconds

### E2E Tests
- [ ] All 10 E2E tests pass
- [ ] Generated C code compiles with `gcc -std=c99 -Wall -Werror`
- [ ] Executables produce correct output
- [ ] No memory leaks (valgrind clean)

### Code Quality
- [ ] No compiler warnings
- [ ] Code follows project style guide
- [ ] All public methods documented
- [ ] No TODOs or FIXMEs remaining

---

## Example TDD Session Timeline

**Day 1 (8 hours):**
- Setup test infrastructure (Steps 0.1-0.4): 8 hours
- **Checkpoint:** MockASTContext works, can create AST nodes

**Day 2 (8 hours):**
- FunctionHandler tests 1-10 (Steps 1-6): 6 hours
- FunctionHandler tests 11-18 (Steps 7+): 2 hours
- **Checkpoint:** FunctionHandler complete, 18 tests pass

**Day 3 (8 hours):**
- VariableHandler tests 1-15 (Steps 7-15): 5 hours
- ExpressionHandler tests 1-10 (Steps 16-26): 3 hours
- **Checkpoint:** VariableHandler complete, ExpressionHandler started

**Day 4 (8 hours):**
- ExpressionHandler tests 11-35 (Steps 27-50): 7 hours
- StatementHandler tests 1-5 (Steps 51-55): 1 hour
- **Checkpoint:** ExpressionHandler complete, StatementHandler started

**Day 5 (8 hours):**
- StatementHandler tests 6-12 (Steps 56-63): 3 hours
- Integration tests 1-15 (Steps 64-79): 5 hours
- **Checkpoint:** All handlers complete, integration testing started

**Day 6 (8 hours):**
- Integration tests 16-25 (Steps 80-88): 3 hours
- E2E tests 1-10 (Steps 89-98): 5 hours
- **Checkpoint:** All tests pass, Phase 1 complete!

---

## Troubleshooting Guide

### Issue: Test Fails After Passing Previously

**Diagnosis:**
- Check if recent change broke existing functionality
- Run git diff to see what changed

**Solution:**
- Revert recent changes
- Add regression test
- Fix properly with TDD

### Issue: Can't Create AST Node

**Diagnosis:**
- Missing SourceLocation
- Incorrect AST context
- Invalid QualType

**Solution:**
- Use SourceLocation::getInvalid() for test nodes
- Ensure using correct AST context (C++ vs C)
- Verify type with context.getTypeDeclType()

### Issue: Segfault in Handler

**Diagnosis:**
- Null pointer dereference
- Invalid cast
- Accessing destroyed object

**Solution:**
- Use gdb: `gdb --args ./test_name`
- Add null checks
- Use AddressSanitizer: `-fsanitize=address`

---

## Success Criteria

### Phase 1 Complete When:

1. **All Tests Pass:**
   - 80 unit tests ✅
   - 25 integration tests ✅
   - 10 E2E tests ✅

2. **Code Quality:**
   - 100% handler coverage ✅
   - No warnings ✅
   - Documented ✅

3. **E2E Verification:**
   - Simple programs transpile ✅
   - C code compiles ✅
   - Executables work correctly ✅
   - No memory leaks ✅

4. **Performance:**
   - Unit tests < 5s ✅
   - Integration tests < 30s ✅
   - E2E tests < 2min ✅

---

## Next Steps After Phase 1

**Immediate:**
1. Code review
2. Refactor if needed (keep tests passing)
3. Document any limitations discovered
4. Update architecture docs based on learnings

**Then:**
1. Begin Phase 2: Control Flow
2. Extend StatementHandler and ExpressionHandler
3. Maintain TDD discipline
4. Keep 100% coverage

---

## Key Principles to Remember

1. **Red-Green-Refactor:** Always follow TDD cycle
2. **One Test at a Time:** Don't write multiple failing tests
3. **Simplest Implementation:** Make test pass with minimal code
4. **Refactor Fearlessly:** Tests protect you
5. **Run Tests Frequently:** After every change
6. **Commit Often:** Each passing test is a commit point
7. **Document Decisions:** Why, not just what

---

## Estimated Completion Time

**Optimistic:** 21 hours (~3 days)
**Realistic:** 25 hours (~3-4 days)
**Pessimistic:** 29 hours (~4 days)

**Actual time will depend on:**
- Familiarity with Clang API
- Testing discipline
- Debug time for unexpected issues
- Code review iterations

**Track actual time vs estimates to improve future phase estimates.**

---

## Final Note

Phase 1 is the hardest because you're establishing patterns and learning the Clang API. Later phases will go faster as you:
- Reuse infrastructure
- Apply established patterns
- Understand AST structure better
- Have more test utilities

**Be patient. Get Phase 1 right. The rest will follow.**

🚀 **Ready to begin Phase 1 implementation!**

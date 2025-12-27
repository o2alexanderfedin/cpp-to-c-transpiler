# Test Fixtures and Mock Utilities Design

## Overview

This document specifies the design of mock utilities, test fixtures, and helper functions for surgical handler testing. The goal is to enable 100% handler unit test coverage by creating C++ AST nodes programmatically and verifying C AST output without code emission.

**Key Principle:** Test AST → AST translation, NOT code generation.

---

## MockASTContext: C++ AST Node Creation

### Purpose
Create minimal C++ AST nodes programmatically for testing handlers in isolation.

### Design

```cpp
// tests/fixtures/MockASTContext.h
namespace cpptoc::test {

class MockASTContext {
private:
    std::unique_ptr<clang::ASTContext> cppContext_;
    std::unique_ptr<clang::ASTContext> cContext_;
    std::vector<std::unique_ptr<clang::Decl>> ownedDecls_;
    std::vector<std::unique_ptr<clang::Stmt>> ownedStmts_;
    std::vector<std::unique_ptr<clang::Expr>> ownedExprs_;

public:
    MockASTContext();
    ~MockASTContext();

    clang::ASTContext& getCppContext() { return *cppContext_; }
    clang::ASTContext& getCContext() { return *cContext_; }

    // ========================================================================
    // Declaration Builders
    // ========================================================================

    /**
     * @brief Create a simple function declaration
     * @param returnType Return type as string (e.g., "int", "void")
     * @param name Function name
     * @param params Parameter declarations as strings (e.g., {"int a", "float b"})
     * @param body Optional function body (nullptr for declaration only)
     * @return FunctionDecl* (owned by MockASTContext)
     */
    clang::FunctionDecl* createFunction(
        const std::string& returnType,
        const std::string& name,
        const std::vector<std::string>& params = {},
        clang::Stmt* body = nullptr
    );

    /**
     * @brief Create a variable declaration
     * @param type Variable type as string
     * @param name Variable name
     * @param init Optional initializer expression
     * @param isGlobal Whether variable is global scope
     * @return VarDecl*
     */
    clang::VarDecl* createVariable(
        const std::string& type,
        const std::string& name,
        clang::Expr* init = nullptr,
        bool isGlobal = false
    );

    /**
     * @brief Create a C-style struct declaration
     * @param name Struct name
     * @param fields Field declarations as type-name pairs
     * @return RecordDecl*
     */
    clang::RecordDecl* createStruct(
        const std::string& name,
        const std::vector<std::pair<std::string, std::string>>& fields
    );

    /**
     * @brief Create a C++ class declaration
     * @param name Class name
     * @param fields Field declarations with access specifiers
     * @param methods Method declarations
     * @return CXXRecordDecl*
     */
    clang::CXXRecordDecl* createClass(
        const std::string& name,
        const std::vector<std::tuple<std::string, std::string, clang::AccessSpecifier>>& fields,
        const std::vector<clang::CXXMethodDecl*>& methods = {}
    );

    /**
     * @brief Create an enum declaration
     * @param name Enum name
     * @param constants Constant names
     * @param isScoped Whether enum is scoped (enum class)
     * @return EnumDecl*
     */
    clang::EnumDecl* createEnum(
        const std::string& name,
        const std::vector<std::string>& constants,
        bool isScoped = false
    );

    // ========================================================================
    // Statement Builders
    // ========================================================================

    /**
     * @brief Create a compound statement (block)
     * @param stmts Statements in block
     * @return CompoundStmt*
     */
    clang::CompoundStmt* createCompoundStmt(
        const std::vector<clang::Stmt*>& stmts
    );

    /**
     * @brief Create a return statement
     * @param value Return value expression (nullptr for void return)
     * @return ReturnStmt*
     */
    clang::ReturnStmt* createReturnStmt(clang::Expr* value = nullptr);

    /**
     * @brief Create an if statement
     * @param cond Condition expression
     * @param thenStmt Then branch
     * @param elseStmt Else branch (nullptr if no else)
     * @return IfStmt*
     */
    clang::IfStmt* createIfStmt(
        clang::Expr* cond,
        clang::Stmt* thenStmt,
        clang::Stmt* elseStmt = nullptr
    );

    /**
     * @brief Create a while loop
     * @param cond Loop condition
     * @param body Loop body
     * @return WhileStmt*
     */
    clang::WhileStmt* createWhileStmt(
        clang::Expr* cond,
        clang::Stmt* body
    );

    /**
     * @brief Create a for loop
     * @param init Initialization statement
     * @param cond Condition expression
     * @param inc Increment expression
     * @param body Loop body
     * @return ForStmt*
     */
    clang::ForStmt* createForStmt(
        clang::Stmt* init,
        clang::Expr* cond,
        clang::Expr* inc,
        clang::Stmt* body
    );

    // ========================================================================
    // Expression Builders
    // ========================================================================

    /**
     * @brief Create an integer literal
     * @param value Integer value
     * @return IntegerLiteral*
     */
    clang::IntegerLiteral* createIntLiteral(int value);

    /**
     * @brief Create a floating-point literal
     * @param value Float value
     * @param isFloat true for float, false for double
     * @return FloatingLiteral*
     */
    clang::FloatingLiteral* createFloatLiteral(double value, bool isFloat = false);

    /**
     * @brief Create a string literal
     * @param str String value
     * @return StringLiteral*
     */
    clang::StringLiteral* createStringLiteral(const std::string& str);

    /**
     * @brief Create a binary operator expression
     * @param op Operator kind (BO_Add, BO_Sub, etc.)
     * @param lhs Left-hand side expression
     * @param rhs Right-hand side expression
     * @return BinaryOperator*
     */
    clang::BinaryOperator* createBinaryOp(
        clang::BinaryOperatorKind op,
        clang::Expr* lhs,
        clang::Expr* rhs
    );

    /**
     * @brief Create a unary operator expression
     * @param op Operator kind (UO_Minus, UO_AddrOf, etc.)
     * @param expr Operand expression
     * @return UnaryOperator*
     */
    clang::UnaryOperator* createUnaryOp(
        clang::UnaryOperatorKind op,
        clang::Expr* expr
    );

    /**
     * @brief Create a variable reference expression
     * @param var Variable declaration to reference
     * @return DeclRefExpr*
     */
    clang::DeclRefExpr* createVarRef(clang::VarDecl* var);

    /**
     * @brief Create a function call expression
     * @param func Function to call
     * @param args Argument expressions
     * @return CallExpr*
     */
    clang::CallExpr* createFunctionCall(
        clang::FunctionDecl* func,
        const std::vector<clang::Expr*>& args
    );

    // ========================================================================
    // Helper Methods
    // ========================================================================

    /**
     * @brief Parse type from string (e.g., "int", "float*", "const char*")
     * @param typeStr Type string
     * @return QualType
     */
    clang::QualType parseType(const std::string& typeStr);

    /**
     * @brief Create type from TypeDecl
     * @param typeDecl Type declaration
     * @return QualType
     */
    clang::QualType getTypeFor(clang::TypeDecl* typeDecl);
};

} // namespace cpptoc::test
```

### Usage Example

```cpp
TEST(FunctionHandlerTest, SimpleFunctionDeclaration) {
    // Create mock C++ AST
    cpptoc::test::MockASTContext mock;
    clang::FunctionDecl* cppFunc = mock.createFunction("int", "add", {"int a", "int b"});

    // Create handler context
    cpptoc::CNodeBuilder builder(mock.getCContext());
    cpptoc::HandlerContext ctx(mock.getCppContext(), mock.getCContext(), builder);

    // Test handler
    cpptoc::FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, ctx);

    // Verify C AST
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "add");
    EXPECT_EQ(cFunc->getNumParams(), 2);
}
```

---

## CNodeBuilder: C AST Node Creation

### Purpose
Provide simplified API for creating C AST nodes.

### Design

```cpp
// include/CNodeBuilder.h
namespace cpptoc {

class CNodeBuilder {
private:
    clang::ASTContext& cContext_;

public:
    explicit CNodeBuilder(clang::ASTContext& cContext);

    /**
     * @brief Create a C function declaration
     * @param name Function name
     * @param returnType Return type
     * @param params Parameter declarations
     * @return FunctionDecl*
     */
    clang::FunctionDecl* createFunctionDecl(
        const std::string& name,
        clang::QualType returnType,
        const std::vector<clang::ParmVarDecl*>& params
    );

    /**
     * @brief Create a parameter declaration
     * @param name Parameter name
     * @param type Parameter type
     * @return ParmVarDecl*
     */
    clang::ParmVarDecl* createParmVarDecl(
        const std::string& name,
        clang::QualType type
    );

    /**
     * @brief Create a record (struct) declaration
     * @param name Struct name
     * @return RecordDecl*
     */
    clang::RecordDecl* createRecordDecl(const std::string& name);

    /**
     * @brief Create a field declaration
     * @param name Field name
     * @param type Field type
     * @return FieldDecl*
     */
    clang::FieldDecl* createFieldDecl(
        const std::string& name,
        clang::QualType type
    );

    /**
     * @brief Create an enum declaration
     * @param name Enum name
     * @return EnumDecl*
     */
    clang::EnumDecl* createEnumDecl(const std::string& name);

    /**
     * @brief Create an enum constant
     * @param name Constant name
     * @param value Constant value
     * @return EnumConstantDecl*
     */
    clang::EnumConstantDecl* createEnumConstant(
        const std::string& name,
        const llvm::APSInt& value
    );

    // Expression builders
    clang::DeclRefExpr* createDeclRefExpr(clang::ValueDecl* decl);
    clang::BinaryOperator* createBinaryOperator(
        clang::BinaryOperatorKind op,
        clang::Expr* lhs,
        clang::Expr* rhs,
        clang::QualType type
    );

    // Statement builders
    clang::CompoundStmt* createCompoundStmt(const std::vector<clang::Stmt*>& stmts);
    clang::ReturnStmt* createReturnStmt(clang::Expr* value);

    // Utility methods
    clang::ASTContext& getContext() { return cContext_; }
};

} // namespace cpptoc
```

---

## ASTMatcher: Verify C AST Structure

### Purpose
Use Clang AST matchers to verify handler output without code emission.

### Design

```cpp
// tests/fixtures/ASTMatcher.h
namespace cpptoc::test {

/**
 * @brief Helper class for matching AST nodes in tests
 */
class ASTMatcher {
public:
    /**
     * @brief Match function declaration with specific properties
     */
    static bool matchFunctionDecl(
        const clang::FunctionDecl* func,
        const std::string& name,
        const std::string& returnType,
        int numParams
    );

    /**
     * @brief Match binary operator expression
     */
    static bool matchBinaryOperator(
        const clang::Expr* expr,
        clang::BinaryOperatorKind op
    );

    /**
     * @brief Match variable reference
     */
    static bool matchDeclRefExpr(
        const clang::Expr* expr,
        const std::string& varName
    );

    /**
     * @brief Match record declaration (struct)
     */
    static bool matchRecordDecl(
        const clang::RecordDecl* record,
        const std::string& name,
        int numFields
    );

    /**
     * @brief Match enum declaration
     */
    static bool matchEnumDecl(
        const clang::EnumDecl* enumDecl,
        const std::string& name,
        int numConstants
    );

    /**
     * @brief Check if AST node matches using Clang AST matchers
     */
    template<typename T>
    static bool matches(
        const T* node,
        const clang::ast_matchers::internal::Matcher<T>& matcher,
        clang::ASTContext& context
    );
};

} // namespace cpptoc::test
```

### Usage Example

```cpp
TEST(ExpressionHandlerTest, BinaryAddition) {
    cpptoc::test::MockASTContext mock;

    // Create: a + b
    auto* varA = mock.createVariable("int", "a");
    auto* varB = mock.createVariable("int", "b");
    auto* refA = mock.createVarRef(varA);
    auto* refB = mock.createVarRef(varB);
    auto* cppExpr = mock.createBinaryOp(clang::BO_Add, refA, refB);

    // Translate
    cpptoc::CNodeBuilder builder(mock.getCContext());
    cpptoc::HandlerContext ctx(mock.getCppContext(), mock.getCContext(), builder);
    cpptoc::ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, ctx);

    // Verify using matchers
    ASSERT_TRUE(cpptoc::test::ASTMatcher::matchBinaryOperator(result, clang::BO_Add));
}
```

---

## HandlerTestFixture: Base Test Fixture

### Purpose
Provide common setup/teardown and helper methods for all handler tests.

### Design

```cpp
// tests/fixtures/HandlerTestFixture.h
namespace cpptoc::test {

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

    // Helper methods available to all tests
    MockASTContext& getMock() { return *mock_; }
    HandlerContext& getContext() { return *context_; }
    CNodeBuilder& getBuilder() { return *builder_; }

    /**
     * @brief Translate C++ declaration using handler
     */
    template<typename Handler>
    clang::Decl* translateDecl(clang::Decl* cppDecl) {
        Handler handler;
        return handler.handleDecl(cppDecl, *context_);
    }

    /**
     * @brief Translate C++ expression using handler
     */
    template<typename Handler>
    clang::Expr* translateExpr(clang::Expr* cppExpr) {
        Handler handler;
        return handler.handleExpr(cppExpr, *context_);
    }

    /**
     * @brief Translate C++ statement using handler
     */
    template<typename Handler>
    clang::Stmt* translateStmt(clang::Stmt* cppStmt) {
        Handler handler;
        return handler.handleStmt(cppStmt, *context_);
    }

    /**
     * @brief Assert that translation produced non-null result
     */
    void assertTranslated(clang::Decl* result) {
        ASSERT_NE(result, nullptr) << "Translation failed";
    }

    /**
     * @brief Assert that C AST node has expected type
     */
    template<typename T>
    T* assertNodeType(clang::Decl* node) {
        auto* typed = llvm::dyn_cast_or_null<T>(node);
        ASSERT_NE(typed, nullptr) << "Node is not of expected type";
        return typed;
    }
};

} // namespace cpptoc::test
```

### Usage Example

```cpp
class FunctionHandlerTest : public cpptoc::test::HandlerTestFixture {};

TEST_F(FunctionHandlerTest, SimpleFunction) {
    // Use fixture helpers
    auto* cppFunc = getMock().createFunction("int", "add", {"int a", "int b"});

    auto* result = translateDecl<cpptoc::FunctionHandler>(cppFunc);

    assertTranslated(result);
    auto* cFunc = assertNodeType<clang::FunctionDecl>(result);
    EXPECT_EQ(cFunc->getNameAsString(), "add");
}
```

---

## IntegrationTestHarness: E2E Testing

### Purpose
Run full transpilation pipeline and verify compiled C code works.

### Design

```cpp
// tests/fixtures/IntegrationTestHarness.h
namespace cpptoc::test {

class IntegrationTestHarness {
public:
    /**
     * @brief Run full transpilation pipeline
     * @param cppCode C++ source code as string
     * @param expectedCCode Expected C code (for verification)
     * @param expectedOutput Expected program output
     * @return TestResult
     */
    struct TestResult {
        bool transpilationSuccess;
        bool compilationSuccess;
        bool executionSuccess;
        std::string generatedC;
        std::string compilationErrors;
        std::string executionOutput;
        int exitCode;
    };

    TestResult runTest(
        const std::string& cppCode,
        const std::string& expectedCCode = "",
        const std::string& expectedOutput = ""
    );

    /**
     * @brief Compile generated C code
     * @param cCode C source code
     * @param outputBinary Output binary path
     * @return true if compilation succeeded
     */
    bool compileC(
        const std::string& cCode,
        const std::string& outputBinary
    );

    /**
     * @brief Execute compiled binary
     * @param binary Binary path
     * @param input Input data (stdin)
     * @return Execution output and exit code
     */
    std::pair<std::string, int> execute(
        const std::string& binary,
        const std::string& input = ""
    );

    /**
     * @brief Check for memory leaks using valgrind
     * @param binary Binary to check
     * @return true if no leaks detected
     */
    bool checkMemoryLeaks(const std::string& binary);

    /**
     * @brief Normalize whitespace for comparison
     */
    static std::string normalizeWhitespace(const std::string& code);

    /**
     * @brief Create temporary file with content
     */
    std::string createTempFile(
        const std::string& content,
        const std::string& extension
    );
};

} // namespace cpptoc::test
```

### Usage Example

```cpp
TEST(TranspilerIntegrationTest, SimpleProgram) {
    cpptoc::test::IntegrationTestHarness harness;

    auto result = harness.runTest(
        // C++ input
        R"(
            int add(int a, int b) {
                return a + b;
            }
            int main() {
                return add(3, 4);
            }
        )",
        // Expected C output
        R"(
            int add(int a, int b) {
                return a + b;
            }
            int main(void) {
                return add(3, 4);
            }
        )",
        // Expected output (via exit code)
        ""
    );

    ASSERT_TRUE(result.transpilationSuccess);
    ASSERT_TRUE(result.compilationSuccess);
    ASSERT_TRUE(result.executionSuccess);
    EXPECT_EQ(result.exitCode, 7);
}
```

---

## Test Data Organization

### Directory Structure

```
tests/
├── fixtures/
│   ├── MockASTContext.h
│   ├── MockASTContext.cpp
│   ├── ASTMatcher.h
│   ├── ASTMatcher.cpp
│   ├── HandlerTestFixture.h
│   ├── IntegrationTestHarness.h
│   └── IntegrationTestHarness.cpp
├── unit/
│   └── handlers/
│       ├── FunctionHandlerTest.cpp
│       ├── VariableHandlerTest.cpp
│       ├── ExpressionHandlerTest.cpp
│       ├── StatementHandlerTest.cpp
│       ├── RecordHandlerTest.cpp
│       ├── MethodHandlerTest.cpp
│       ├── ConstructorHandlerTest.cpp
│       ├── DestructorHandlerTest.cpp
│       └── EnumHandlerTest.cpp
├── integration/
│   └── handlers/
│       ├── Phase1IntegrationTest.cpp
│       ├── Phase2IntegrationTest.cpp
│       └── ... (one per phase)
├── e2e/
│   ├── phase1/
│   │   ├── simple_program.cpp
│   │   ├── arithmetic.cpp
│   │   └── ... (E2E test cases)
│   ├── phase2/
│   │   └── ...
│   └── ...
└── CMakeLists.txt
```

### Naming Conventions

**Unit Tests:**
- File: `{Handler}Test.cpp`
- Test case: `TEST(HandlerTest, FeatureName)`
- Example: `TEST(FunctionHandlerTest, SimpleFunctionDeclaration)`

**Integration Tests:**
- File: `Phase{N}IntegrationTest.cpp`
- Test case: `TEST(Phase{N}IntegrationTest, Scenario)`
- Example: `TEST(Phase1IntegrationTest, FunctionWithLocalVariables)`

**E2E Tests:**
- File: `descriptive_name.cpp`
- Location: `tests/e2e/phase{N}/`
- Example: `tests/e2e/phase1/simple_program.cpp`

---

## CMake Configuration

### Test Discovery

```cmake
# tests/CMakeLists.txt
enable_testing()
include(GoogleTest)

# Build test fixtures library
add_library(test_fixtures
    fixtures/MockASTContext.cpp
    fixtures/ASTMatcher.cpp
    fixtures/IntegrationTestHarness.cpp
)

target_link_libraries(test_fixtures
    PRIVATE
        clangAST
        clangBasic
        clangFrontend
        gtest
        gtest_main
)

# Unit tests
file(GLOB_RECURSE UNIT_TEST_SOURCES "unit/handlers/*Test.cpp")
foreach(TEST_SOURCE ${UNIT_TEST_SOURCES})
    get_filename_component(TEST_NAME ${TEST_SOURCE} NAME_WE)
    add_executable(${TEST_NAME} ${TEST_SOURCE})
    target_link_libraries(${TEST_NAME}
        PRIVATE
            transpiler_lib
            test_fixtures
            gtest
            gtest_main
    )
    gtest_discover_tests(${TEST_NAME}
        TEST_PREFIX "Unit."
    )
endforeach()

# Integration tests
file(GLOB_RECURSE INTEGRATION_TEST_SOURCES "integration/handlers/*Test.cpp")
foreach(TEST_SOURCE ${INTEGRATION_TEST_SOURCES})
    get_filename_component(TEST_NAME ${TEST_SOURCE} NAME_WE)
    add_executable(${TEST_NAME} ${TEST_SOURCE})
    target_link_libraries(${TEST_NAME}
        PRIVATE
            transpiler_lib
            test_fixtures
            gtest
            gtest_main
    )
    gtest_discover_tests(${TEST_NAME}
        TEST_PREFIX "Integration."
    )
endforeach()

# E2E tests
file(GLOB_RECURSE E2E_TEST_SOURCES "e2e/*/*.cpp")
foreach(TEST_SOURCE ${E2E_TEST_SOURCES})
    get_filename_component(TEST_NAME ${TEST_SOURCE} NAME_WE)
    add_test(NAME "E2E.${TEST_NAME}"
        COMMAND transpiler ${TEST_SOURCE} -o ${CMAKE_BINARY_DIR}/e2e_output/${TEST_NAME}.c
    )
endforeach()
```

---

## Summary

### Test Utilities Provided

1. **MockASTContext** - Create C++ AST nodes programmatically
2. **CNodeBuilder** - Create C AST nodes (handler output)
3. **ASTMatcher** - Verify AST structure without code emission
4. **HandlerTestFixture** - Base class for all handler unit tests
5. **IntegrationTestHarness** - Run full transpilation pipeline

### Key Benefits

- **Surgical Testing**: Test each handler in complete isolation
- **No Code Emission**: Unit tests verify AST structure only
- **Fast Execution**: Unit tests run in milliseconds
- **Easy Debugging**: Clear failure messages pointing to exact issue
- **100% Coverage**: All handler logic testable

### Implementation Effort

**Test Fixtures LOC:** 2000-3000 LOC
**Implementation Time:** 2-3 days
**Complexity:** Moderate (requires Clang API knowledge)

### Next Steps

1. Implement MockASTContext with basic builders (functions, variables, expressions)
2. Implement CNodeBuilder
3. Implement HandlerTestFixture
4. Write first unit test (FunctionHandler::EmptyFunction)
5. Expand fixtures as needed during TDD process

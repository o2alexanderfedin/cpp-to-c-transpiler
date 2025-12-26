/**
 * @file StatementHandlerTest.cpp
 * @brief TDD tests for StatementHandler
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (12+ tests):
 * Return Statements (6 tests):
 *   1. ReturnVoid
 *   2. ReturnInt
 *   3. ReturnFloat
 *   4. ReturnExpression
 *   5. ReturnComplexExpr
 *   6. ReturnVarRef
 *
 * Compound Statements (6+ tests):
 *   7. CompoundStmtEmpty
 *   8. CompoundStmtSingleStmt
 *   9. CompoundStmtMultiple
 *   10. NestedCompoundStmt
 *   11. CompoundWithVars
 *   12. CompoundWithExprs
 */

#include "handlers/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class StatementHandlerTest
 * @brief Test fixture for StatementHandler
 *
 * Uses clang::tooling::buildASTFromCode for real AST contexts.
 */
class StatementHandlerTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    void SetUp() override {
        // Create real AST contexts using minimal code
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr) << "Failed to create C++ AST";
        ASSERT_NE(cAST, nullptr) << "Failed to create C AST";

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );
    }

    void TearDown() override {
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Create an integer literal programmatically
     */
    clang::IntegerLiteral* createIntLiteral(int value) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        llvm::APInt apValue(32, value);
        return clang::IntegerLiteral::Create(
            ctx,
            apValue,
            ctx.IntTy,
            clang::SourceLocation()
        );
    }

    /**
     * @brief Create a floating literal programmatically
     */
    clang::FloatingLiteral* createFloatLiteral(double value) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        llvm::APFloat apValue(value);
        return clang::FloatingLiteral::Create(
            ctx,
            apValue,
            false, // isExact
            ctx.FloatTy,
            clang::SourceLocation()
        );
    }

    /**
     * @brief Create a variable declaration
     */
    clang::VarDecl* createVarDecl(const std::string& name, clang::QualType type, clang::Expr* init = nullptr) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        clang::IdentifierInfo& II = ctx.Idents.get(name);
        clang::DeclarationName declName(&II);

        clang::VarDecl* var = clang::VarDecl::Create(
            ctx,
            ctx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II,
            type,
            ctx.getTrivialTypeSourceInfo(type),
            clang::SC_None
        );

        if (init) {
            var->setInit(init);
        }

        return var;
    }

    /**
     * @brief Create a variable reference
     */
    clang::DeclRefExpr* createVarRef(clang::VarDecl* var) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::DeclRefExpr::Create(
            ctx,
            clang::NestedNameSpecifierLoc(),
            clang::SourceLocation(),
            var,
            false,
            clang::SourceLocation(),
            var->getType(),
            clang::VK_LValue
        );
    }

    /**
     * @brief Create a binary operator expression
     */
    clang::BinaryOperator* createBinaryOp(
        clang::BinaryOperatorKind op,
        clang::Expr* lhs,
        clang::Expr* rhs
    ) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::BinaryOperator::Create(
            ctx,
            lhs,
            rhs,
            op,
            lhs->getType(),
            clang::VK_PRValue,
            clang::OK_Ordinary,
            clang::SourceLocation(),
            clang::FPOptionsOverride()
        );
    }

    /**
     * @brief Create a return statement
     */
    clang::ReturnStmt* createReturnStmt(clang::Expr* expr = nullptr) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::ReturnStmt::Create(
            ctx,
            clang::SourceLocation(),
            expr,
            nullptr // NRVOCandidate
        );
    }

    /**
     * @brief Create a compound statement
     */
    clang::CompoundStmt* createCompoundStmt(const std::vector<clang::Stmt*>& stmts) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::CompoundStmt::Create(
            ctx,
            stmts,
            clang::FPOptionsOverride(),
            clang::SourceLocation(),
            clang::SourceLocation()
        );
    }
};

// ============================================================================
// TDD Test 1: Return Void
// ============================================================================

/**
 * Test 1: Translate void return statement
 *
 * C++ Input:  return;
 * C Output:   return;
 */
TEST_F(StatementHandlerTest, ReturnVoid) {
    // Arrange: Create C++ void return statement
    clang::ReturnStmt* cppStmt = createReturnStmt(nullptr);
    ASSERT_NE(cppStmt, nullptr);
    ASSERT_EQ(cppStmt->getRetValue(), nullptr) << "Should be void return";

    // Act: Translate using StatementHandler
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert: Verify C return statement created
    ASSERT_NE(result, nullptr) << "Translation returned null";

    auto* cStmt = llvm::dyn_cast<clang::ReturnStmt>(result);
    ASSERT_NE(cStmt, nullptr) << "Result is not a ReturnStmt";
    EXPECT_EQ(cStmt->getRetValue(), nullptr) << "Should be void return";
}

// ============================================================================
// TDD Test 2: Return Int
// ============================================================================

/**
 * Test 2: Translate return with integer literal
 *
 * C++ Input:  return 42;
 * C Output:   return 42;
 */
TEST_F(StatementHandlerTest, ReturnInt) {
    // Arrange
    clang::IntegerLiteral* lit = createIntLiteral(42);
    clang::ReturnStmt* cppStmt = createReturnStmt(lit);
    ASSERT_NE(cppStmt, nullptr);
    ASSERT_NE(cppStmt->getRetValue(), nullptr);

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::ReturnStmt>(result);
    ASSERT_NE(cStmt, nullptr);

    // Should have a return value
    ASSERT_NE(cStmt->getRetValue(), nullptr) << "Return value should not be null";

    // Should be an integer literal (for now, assuming passthrough)
    auto* cLit = llvm::dyn_cast<clang::IntegerLiteral>(cStmt->getRetValue());
    EXPECT_NE(cLit, nullptr) << "Return value should be IntegerLiteral";
}

// ============================================================================
// TDD Test 3: Return Float
// ============================================================================

/**
 * Test 3: Translate return with float literal
 *
 * C++ Input:  return 3.14f;
 * C Output:   return 3.14f;
 */
TEST_F(StatementHandlerTest, ReturnFloat) {
    // Arrange
    clang::FloatingLiteral* lit = createFloatLiteral(3.14);
    clang::ReturnStmt* cppStmt = createReturnStmt(lit);
    ASSERT_NE(cppStmt, nullptr);

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::ReturnStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    ASSERT_NE(cStmt->getRetValue(), nullptr);

    auto* cLit = llvm::dyn_cast<clang::FloatingLiteral>(cStmt->getRetValue());
    EXPECT_NE(cLit, nullptr) << "Return value should be FloatingLiteral";
}

// ============================================================================
// TDD Test 4: Return Expression
// ============================================================================

/**
 * Test 4: Translate return with binary expression
 *
 * C++ Input:  return 1 + 2;
 * C Output:   return 1 + 2;
 */
TEST_F(StatementHandlerTest, ReturnExpression) {
    // Arrange
    clang::IntegerLiteral* lhs = createIntLiteral(1);
    clang::IntegerLiteral* rhs = createIntLiteral(2);
    clang::BinaryOperator* expr = createBinaryOp(clang::BO_Add, lhs, rhs);
    clang::ReturnStmt* cppStmt = createReturnStmt(expr);
    ASSERT_NE(cppStmt, nullptr);

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::ReturnStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    ASSERT_NE(cStmt->getRetValue(), nullptr);

    auto* cExpr = llvm::dyn_cast<clang::BinaryOperator>(cStmt->getRetValue());
    EXPECT_NE(cExpr, nullptr) << "Return value should be BinaryOperator";
}

// ============================================================================
// TDD Test 5: Return Complex Expression
// ============================================================================

/**
 * Test 5: Translate return with complex nested expression
 *
 * C++ Input:  return (1 + 2) * 3;
 * C Output:   return (1 + 2) * 3;
 */
TEST_F(StatementHandlerTest, ReturnComplexExpr) {
    // Arrange
    clang::IntegerLiteral* lit1 = createIntLiteral(1);
    clang::IntegerLiteral* lit2 = createIntLiteral(2);
    clang::IntegerLiteral* lit3 = createIntLiteral(3);
    clang::BinaryOperator* add = createBinaryOp(clang::BO_Add, lit1, lit2);
    clang::BinaryOperator* mul = createBinaryOp(clang::BO_Mul, add, lit3);
    clang::ReturnStmt* cppStmt = createReturnStmt(mul);
    ASSERT_NE(cppStmt, nullptr);

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::ReturnStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    ASSERT_NE(cStmt->getRetValue(), nullptr);

    auto* cMul = llvm::dyn_cast<clang::BinaryOperator>(cStmt->getRetValue());
    ASSERT_NE(cMul, nullptr) << "Return value should be BinaryOperator (mul)";
    EXPECT_EQ(cMul->getOpcode(), clang::BO_Mul);
}

// ============================================================================
// TDD Test 6: Return Variable Reference
// ============================================================================

/**
 * Test 6: Translate return with variable reference
 *
 * C++ Input:  return x;
 * C Output:   return x;
 */
TEST_F(StatementHandlerTest, ReturnVarRef) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::VarDecl* var = createVarDecl("x", ctx.IntTy);
    clang::DeclRefExpr* ref = createVarRef(var);
    clang::ReturnStmt* cppStmt = createReturnStmt(ref);
    ASSERT_NE(cppStmt, nullptr);

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::ReturnStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    ASSERT_NE(cStmt->getRetValue(), nullptr);

    auto* cRef = llvm::dyn_cast<clang::DeclRefExpr>(cStmt->getRetValue());
    EXPECT_NE(cRef, nullptr) << "Return value should be DeclRefExpr";
}

// ============================================================================
// TDD Test 7: Empty Compound Statement
// ============================================================================

/**
 * Test 7: Translate empty compound statement
 *
 * C++ Input:  {}
 * C Output:   {}
 */
TEST_F(StatementHandlerTest, CompoundStmtEmpty) {
    // Arrange
    clang::CompoundStmt* cppStmt = createCompoundStmt({});
    ASSERT_NE(cppStmt, nullptr);
    ASSERT_EQ(cppStmt->size(), 0) << "Should be empty";

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cStmt, nullptr) << "Result should be CompoundStmt";
    EXPECT_EQ(cStmt->size(), 0) << "Should be empty";
}

// ============================================================================
// TDD Test 8: Compound Statement with Single Statement
// ============================================================================

/**
 * Test 8: Translate compound statement with single return
 *
 * C++ Input:  { return 42; }
 * C Output:   { return 42; }
 */
TEST_F(StatementHandlerTest, CompoundStmtSingleStmt) {
    // Arrange
    clang::IntegerLiteral* lit = createIntLiteral(42);
    clang::ReturnStmt* retStmt = createReturnStmt(lit);
    clang::CompoundStmt* cppStmt = createCompoundStmt({retStmt});
    ASSERT_NE(cppStmt, nullptr);
    ASSERT_EQ(cppStmt->size(), 1);

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    EXPECT_EQ(cStmt->size(), 1) << "Should have 1 statement";

    // First statement should be a return
    auto* firstStmt = llvm::dyn_cast<clang::ReturnStmt>(cStmt->body_front());
    EXPECT_NE(firstStmt, nullptr) << "First statement should be ReturnStmt";
}

// ============================================================================
// TDD Test 9: Compound Statement with Multiple Statements
// ============================================================================

/**
 * Test 9: Translate compound statement with multiple returns
 *
 * C++ Input:  { return 1; return 2; }
 * C Output:   { return 1; return 2; }
 */
TEST_F(StatementHandlerTest, CompoundStmtMultiple) {
    // Arrange
    clang::ReturnStmt* ret1 = createReturnStmt(createIntLiteral(1));
    clang::ReturnStmt* ret2 = createReturnStmt(createIntLiteral(2));
    clang::CompoundStmt* cppStmt = createCompoundStmt({ret1, ret2});
    ASSERT_NE(cppStmt, nullptr);
    ASSERT_EQ(cppStmt->size(), 2);

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    EXPECT_EQ(cStmt->size(), 2) << "Should have 2 statements";
}

// ============================================================================
// TDD Test 10: Nested Compound Statements
// ============================================================================

/**
 * Test 10: Translate nested compound statements
 *
 * C++ Input:  { { return 42; } }
 * C Output:   { { return 42; } }
 */
TEST_F(StatementHandlerTest, NestedCompoundStmt) {
    // Arrange
    clang::ReturnStmt* ret = createReturnStmt(createIntLiteral(42));
    clang::CompoundStmt* inner = createCompoundStmt({ret});
    clang::CompoundStmt* outer = createCompoundStmt({inner});
    ASSERT_NE(outer, nullptr);
    ASSERT_EQ(outer->size(), 1);

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(outer, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    EXPECT_EQ(cStmt->size(), 1) << "Outer should have 1 statement";

    // First statement should be a compound statement
    auto* innerStmt = llvm::dyn_cast<clang::CompoundStmt>(cStmt->body_front());
    ASSERT_NE(innerStmt, nullptr) << "Inner should be CompoundStmt";
    EXPECT_EQ(innerStmt->size(), 1) << "Inner should have 1 statement";
}

// ============================================================================
// TDD Test 11: Compound Statement with Variables
// ============================================================================

/**
 * Test 11: Translate compound statement with variable declaration
 *
 * C++ Input:  { int x = 5; return x; }
 * C Output:   { int x = 5; return x; }
 *
 * Note: This test focuses on statement structure, not full variable translation
 */
TEST_F(StatementHandlerTest, CompoundWithVars) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::VarDecl* var = createVarDecl("x", ctx.IntTy, createIntLiteral(5));

    // Create DeclStmt for variable
    clang::DeclStmt* declStmt = new (ctx) clang::DeclStmt(
        clang::DeclGroupRef(var),
        clang::SourceLocation(),
        clang::SourceLocation()
    );

    clang::DeclRefExpr* ref = createVarRef(var);
    clang::ReturnStmt* ret = createReturnStmt(ref);
    clang::CompoundStmt* cppStmt = createCompoundStmt({declStmt, ret});
    ASSERT_NE(cppStmt, nullptr);
    ASSERT_EQ(cppStmt->size(), 2);

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    EXPECT_EQ(cStmt->size(), 2) << "Should have 2 statements (decl + return)";
}

// ============================================================================
// TDD Test 12: Compound Statement with Expressions
// ============================================================================

/**
 * Test 12: Translate compound statement with multiple return statements
 *
 * C++ Input:  { return 1; return 2; return 3; }
 * C Output:   { return 1; return 2; return 3; }
 *
 * Note: Multiple returns in sequence is unusual but valid for testing
 */
TEST_F(StatementHandlerTest, CompoundWithExprs) {
    // Arrange
    clang::ReturnStmt* ret1 = createReturnStmt(createIntLiteral(1));
    clang::ReturnStmt* ret2 = createReturnStmt(createIntLiteral(2));
    clang::ReturnStmt* ret3 = createReturnStmt(createIntLiteral(3));

    clang::CompoundStmt* cppStmt = createCompoundStmt({ret1, ret2, ret3});
    ASSERT_NE(cppStmt, nullptr);
    ASSERT_EQ(cppStmt->size(), 3);

    // Act
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    EXPECT_EQ(cStmt->size(), 3) << "Should have 3 statements";
}

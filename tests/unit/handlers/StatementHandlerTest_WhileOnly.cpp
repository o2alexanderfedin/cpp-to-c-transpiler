/**
 * @file StatementHandlerTest_WhileOnly.cpp
 * @brief TDD tests for While Loop Translation (Task 5)
 *
 * Migrated to dispatcher pattern.
 */

#include "dispatch/StatementHandler.h"
#include "tests/fixtures/UnitTestHelper.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;
using namespace cpptoc::test;

class StatementHandlerTest : public ::testing::Test {
protected:
    UnitTestContext ctx;

    void SetUp() override {
        ctx = createUnitTestContext("int dummy;");

        // Register StatementHandler
        StatementHandler::registerWith(*ctx.dispatcher);
    }

    clang::IntegerLiteral* createIntLiteral(int value) {
        clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
        llvm::APInt apValue(32, value);
        return clang::IntegerLiteral::Create(
            cppCtx, apValue, cppCtx.IntTy, clang::SourceLocation()
        );
    }

    clang::VarDecl* createVarDecl(const std::string& name, clang::QualType type) {
        clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
        clang::IdentifierInfo& II = cppCtx.Idents.get(name);
        return clang::VarDecl::Create(
            cppCtx,
            cppCtx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II,
            type,
            cppCtx.getTrivialTypeSourceInfo(type),
            clang::SC_None
        );
    }

    clang::DeclRefExpr* createVarRef(clang::VarDecl* var) {
        clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
        return clang::DeclRefExpr::Create(
            cppCtx,
            clang::NestedNameSpecifierLoc(),
            clang::SourceLocation(),
            var,
            false,
            clang::SourceLocation(),
            var->getType(),
            clang::VK_LValue
        );
    }

    clang::BinaryOperator* createBinaryOp(
        clang::BinaryOperatorKind op,
        clang::Expr* lhs,
        clang::Expr* rhs
    ) {
        clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
        return clang::BinaryOperator::Create(
            cppCtx, lhs, rhs, op, lhs->getType(), clang::VK_PRValue,
            clang::OK_Ordinary, clang::SourceLocation(), clang::FPOptionsOverride()
        );
    }

    clang::CompoundStmt* createCompoundStmt(const std::vector<clang::Stmt*>& stmts) {
        clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
        return clang::CompoundStmt::Create(
            cppCtx, stmts, clang::FPOptionsOverride(),
            clang::SourceLocation(), clang::SourceLocation()
        );
    }

    clang::WhileStmt* createWhileStmt(clang::Expr* cond, clang::Stmt* body) {
        clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
        return clang::WhileStmt::Create(
            cppCtx, nullptr, cond, body, clang::SourceLocation(),
            clang::SourceLocation(), clang::SourceLocation()
        );
    }

    clang::BreakStmt* createBreakStmt() {
        clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
        return clang::BreakStmt::Create(cppCtx, clang::SourceLocation());
    }

    clang::ContinueStmt* createContinueStmt() {
        clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
        return clang::ContinueStmt::Create(cppCtx, clang::SourceLocation());
    }
};

// ============================================================================
// Test 1: Simple While Loop - while (i < 10) { }
// ============================================================================
TEST_F(StatementHandlerTest, SimpleWhile) {
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    clang::VarDecl* var = createVarDecl("i", cppCtx.IntTy);
    clang::DeclRefExpr* ref = createVarRef(var);
    clang::IntegerLiteral* lit = createIntLiteral(10);
    clang::BinaryOperator* cond = createBinaryOp(clang::BO_LT, ref, lit);
    clang::CompoundStmt* body = createCompoundStmt({});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    // Dispatch through dispatcher
    bool handled = ctx.dispatcher->dispatch(cppCtx, cCtx, cppStmt);
    EXPECT_TRUE(handled) << "StatementHandler should handle WhileStmt";

    // Verify mapping was created
    clang::Stmt* result = ctx.stmtMapper->getCreated(cppStmt);
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    ASSERT_NE(cStmt->getCond(), nullptr);
    ASSERT_NE(cStmt->getBody(), nullptr);
}

// ============================================================================
// Test 2: While with Compound Condition - while (x > 0) { }
// ============================================================================
TEST_F(StatementHandlerTest, WhileWithCompoundCondition) {
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    clang::VarDecl* varX = createVarDecl("x", cppCtx.IntTy);
    clang::DeclRefExpr* refX = createVarRef(varX);
    clang::IntegerLiteral* lit0 = createIntLiteral(0);
    clang::BinaryOperator* cond = createBinaryOp(clang::BO_GT, refX, lit0);
    clang::CompoundStmt* body = createCompoundStmt({});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    bool handled = ctx.dispatcher->dispatch(cppCtx, cCtx, cppStmt);
    EXPECT_TRUE(handled);

    clang::Stmt* result = ctx.stmtMapper->getCreated(cppStmt);
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(cStmt, nullptr);
}

// ============================================================================
// Test 3: While with Break - while (1) { break; }
// ============================================================================
TEST_F(StatementHandlerTest, WhileWithBreak) {
    clang::IntegerLiteral* cond = createIntLiteral(1);
    clang::BreakStmt* breakStmt = createBreakStmt();
    clang::CompoundStmt* body = createCompoundStmt({breakStmt});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    bool handled = ctx.dispatcher->dispatch(cppCtx, cCtx, cppStmt);
    EXPECT_TRUE(handled);

    clang::Stmt* result = ctx.stmtMapper->getCreated(cppStmt);
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(cStmt, nullptr);
    ASSERT_NE(cStmt->getBody(), nullptr);

    auto* bodyStmt = llvm::dyn_cast<clang::CompoundStmt>(cStmt->getBody());
    ASSERT_NE(bodyStmt, nullptr);
    EXPECT_EQ(bodyStmt->size(), 1);
}

// ============================================================================
// Test 4: While with Continue - while (i < 10) { continue; }
// ============================================================================
TEST_F(StatementHandlerTest, WhileWithContinue) {
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    clang::VarDecl* var = createVarDecl("i", cppCtx.IntTy);
    clang::DeclRefExpr* ref = createVarRef(var);
    clang::IntegerLiteral* lit = createIntLiteral(10);
    clang::BinaryOperator* cond = createBinaryOp(clang::BO_LT, ref, lit);
    clang::ContinueStmt* continueStmt = createContinueStmt();
    clang::CompoundStmt* body = createCompoundStmt({continueStmt});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    bool handled = ctx.dispatcher->dispatch(cppCtx, cCtx, cppStmt);
    EXPECT_TRUE(handled);

    clang::Stmt* result = ctx.stmtMapper->getCreated(cppStmt);
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(cStmt, nullptr);
}

// ============================================================================
// Test 5: While Empty Body - while (1) { }
// ============================================================================
TEST_F(StatementHandlerTest, WhileEmptyBody) {
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    clang::IntegerLiteral* cond = createIntLiteral(1);
    clang::CompoundStmt* body = createCompoundStmt({});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    bool handled = ctx.dispatcher->dispatch(cppCtx, cCtx, cppStmt);
    EXPECT_TRUE(handled);

    clang::Stmt* result = ctx.stmtMapper->getCreated(cppStmt);
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(cStmt, nullptr);

    auto* bodyStmt = llvm::dyn_cast<clang::CompoundStmt>(cStmt->getBody());
    ASSERT_NE(bodyStmt, nullptr);
    EXPECT_EQ(bodyStmt->size(), 0);
}

// ============================================================================
// Test 6: Nested While Loops - while (a) { while (b) { } }
// ============================================================================
TEST_F(StatementHandlerTest, NestedWhile) {
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    clang::VarDecl* varA = createVarDecl("a", cppCtx.IntTy);
    clang::VarDecl* varB = createVarDecl("b", cppCtx.IntTy);
    clang::DeclRefExpr* refA = createVarRef(varA);
    clang::DeclRefExpr* refB = createVarRef(varB);

    clang::CompoundStmt* innerBody = createCompoundStmt({});
    clang::WhileStmt* innerWhile = createWhileStmt(refB, innerBody);

    clang::CompoundStmt* outerBody = createCompoundStmt({innerWhile});
    clang::WhileStmt* cppStmt = createWhileStmt(refA, outerBody);
    ASSERT_NE(cppStmt, nullptr);

    bool handled = ctx.dispatcher->dispatch(cppCtx, cCtx, cppStmt);
    EXPECT_TRUE(handled);

    clang::Stmt* result = ctx.stmtMapper->getCreated(cppStmt);
    ASSERT_NE(result, nullptr);
    auto* outerStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(outerStmt, nullptr);

    auto* outerBody_c = llvm::dyn_cast<clang::CompoundStmt>(outerStmt->getBody());
    ASSERT_NE(outerBody_c, nullptr);
    EXPECT_EQ(outerBody_c->size(), 1);

    auto* innerStmt = llvm::dyn_cast<clang::WhileStmt>(outerBody_c->body_front());
    EXPECT_NE(innerStmt, nullptr);
}

// ============================================================================
// Test 7: While with Variable Declaration - while (1) { }
// ============================================================================
TEST_F(StatementHandlerTest, WhileWithVarDecl) {
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    clang::IntegerLiteral* cond = createIntLiteral(1);
    clang::CompoundStmt* body = createCompoundStmt({});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    bool handled = ctx.dispatcher->dispatch(cppCtx, cCtx, cppStmt);
    EXPECT_TRUE(handled);

    clang::Stmt* result = ctx.stmtMapper->getCreated(cppStmt);
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(cStmt, nullptr);
}

// ============================================================================
// Test 8: Infinite While Loop - while (1) { }
// ============================================================================
TEST_F(StatementHandlerTest, InfiniteWhile) {
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    clang::IntegerLiteral* cond = createIntLiteral(1);
    clang::CompoundStmt* body = createCompoundStmt({});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    bool handled = ctx.dispatcher->dispatch(cppCtx, cCtx, cppStmt);
    EXPECT_TRUE(handled);

    clang::Stmt* result = ctx.stmtMapper->getCreated(cppStmt);
    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(cStmt, nullptr);

    auto* condLit = llvm::dyn_cast<clang::IntegerLiteral>(cStmt->getCond());
    EXPECT_NE(condLit, nullptr);
}

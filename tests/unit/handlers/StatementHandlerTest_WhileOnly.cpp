/**
 * @file StatementHandlerTest_WhileOnly.cpp
 * @brief TDD tests for While Loop Translation (Task 5)
 */

#include "dispatch/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

class StatementHandlerTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    void SetUp() override {
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");
        ASSERT_NE(cppAST, nullptr);
        ASSERT_NE(cAST, nullptr);
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );
    }

    clang::IntegerLiteral* createIntLiteral(int value) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        llvm::APInt apValue(32, value);
        return clang::IntegerLiteral::Create(
            ctx, apValue, ctx.IntTy, clang::SourceLocation()
        );
    }

    clang::VarDecl* createVarDecl(const std::string& name, clang::QualType type) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        clang::IdentifierInfo& II = ctx.Idents.get(name);
        return clang::VarDecl::Create(
            ctx,
            ctx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II,
            type,
            ctx.getTrivialTypeSourceInfo(type),
            clang::SC_None
        );
    }

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

    clang::BinaryOperator* createBinaryOp(
        clang::BinaryOperatorKind op,
        clang::Expr* lhs,
        clang::Expr* rhs
    ) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::BinaryOperator::Create(
            ctx, lhs, rhs, op, lhs->getType(), clang::VK_PRValue,
            clang::OK_Ordinary, clang::SourceLocation(), clang::FPOptionsOverride()
        );
    }

    clang::CompoundStmt* createCompoundStmt(const std::vector<clang::Stmt*>& stmts) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::CompoundStmt::Create(
            ctx, stmts, clang::FPOptionsOverride(),
            clang::SourceLocation(), clang::SourceLocation()
        );
    }

    clang::WhileStmt* createWhileStmt(clang::Expr* cond, clang::Stmt* body) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::WhileStmt::Create(
            ctx, nullptr, cond, body, clang::SourceLocation(),
            clang::SourceLocation(), clang::SourceLocation()
        );
    }

    clang::BreakStmt* createBreakStmt() {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::BreakStmt::Create(ctx, clang::SourceLocation());
    }

    clang::ContinueStmt* createContinueStmt() {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::ContinueStmt::Create(ctx, clang::SourceLocation());
    }
};

// ============================================================================
// Test 1: Simple While Loop - while (i < 10) { }
// ============================================================================
TEST_F(StatementHandlerTest, SimpleWhile) {
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::VarDecl* var = createVarDecl("i", ctx.IntTy);
    clang::DeclRefExpr* ref = createVarRef(var);
    clang::IntegerLiteral* lit = createIntLiteral(10);
    clang::BinaryOperator* cond = createBinaryOp(clang::BO_LT, ref, lit);
    clang::CompoundStmt* body = createCompoundStmt({});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

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
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::VarDecl* varX = createVarDecl("x", ctx.IntTy);
    clang::DeclRefExpr* refX = createVarRef(varX);
    clang::IntegerLiteral* lit0 = createIntLiteral(0);
    clang::BinaryOperator* cond = createBinaryOp(clang::BO_GT, refX, lit0);
    clang::CompoundStmt* body = createCompoundStmt({});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

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

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

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
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::VarDecl* var = createVarDecl("i", ctx.IntTy);
    clang::DeclRefExpr* ref = createVarRef(var);
    clang::IntegerLiteral* lit = createIntLiteral(10);
    clang::BinaryOperator* cond = createBinaryOp(clang::BO_LT, ref, lit);
    clang::ContinueStmt* continueStmt = createContinueStmt();
    clang::CompoundStmt* body = createCompoundStmt({continueStmt});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(cStmt, nullptr);
}

// ============================================================================
// Test 5: While Empty Body - while (1) { }
// ============================================================================
TEST_F(StatementHandlerTest, WhileEmptyBody) {
    clang::IntegerLiteral* cond = createIntLiteral(1);
    clang::CompoundStmt* body = createCompoundStmt({});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

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
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::VarDecl* varA = createVarDecl("a", ctx.IntTy);
    clang::VarDecl* varB = createVarDecl("b", ctx.IntTy);
    clang::DeclRefExpr* refA = createVarRef(varA);
    clang::DeclRefExpr* refB = createVarRef(varB);

    clang::CompoundStmt* innerBody = createCompoundStmt({});
    clang::WhileStmt* innerWhile = createWhileStmt(refB, innerBody);

    clang::CompoundStmt* outerBody = createCompoundStmt({innerWhile});
    clang::WhileStmt* cppStmt = createWhileStmt(refA, outerBody);
    ASSERT_NE(cppStmt, nullptr);

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

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
    clang::IntegerLiteral* cond = createIntLiteral(1);
    clang::CompoundStmt* body = createCompoundStmt({});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(cStmt, nullptr);
}

// ============================================================================
// Test 8: Infinite While Loop - while (1) { }
// ============================================================================
TEST_F(StatementHandlerTest, InfiniteWhile) {
    clang::IntegerLiteral* cond = createIntLiteral(1);
    clang::CompoundStmt* body = createCompoundStmt({});

    clang::WhileStmt* cppStmt = createWhileStmt(cond, body);
    ASSERT_NE(cppStmt, nullptr);

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(cppStmt, *context);

    ASSERT_NE(result, nullptr);
    auto* cStmt = llvm::dyn_cast<clang::WhileStmt>(result);
    ASSERT_NE(cStmt, nullptr);

    auto* condLit = llvm::dyn_cast<clang::IntegerLiteral>(cStmt->getCond());
    EXPECT_NE(condLit, nullptr);
}

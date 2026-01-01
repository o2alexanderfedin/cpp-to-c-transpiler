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
        return new (ctx) clang::BreakStmt(clang::SourceLocation());
    }

    clang::ContinueStmt* createContinueStmt() {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return new (ctx) clang::ContinueStmt(clang::SourceLocation());
    }

    clang::LabelDecl* createLabelDecl(const std::string& name) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        clang::IdentifierInfo& II = ctx.Idents.get(name);
        return clang::LabelDecl::Create(
            ctx,
            ctx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            &II
        );
    }

    clang::LabelStmt* createLabelStmt(const std::string& name, clang::Stmt* subStmt) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        clang::LabelDecl* decl = createLabelDecl(name);
        return new (ctx) clang::LabelStmt(
            clang::SourceLocation(),
            decl,
            subStmt
        );
    }

    clang::GotoStmt* createGotoStmt(const std::string& labelName) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        clang::LabelDecl* decl = createLabelDecl(labelName);
        return new (ctx) clang::GotoStmt(
            decl,
            clang::SourceLocation(),
            clang::SourceLocation()
        );
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

// ============================================================================
// GOTO AND LABEL STATEMENT TESTS
// ============================================================================

// ============================================================================
// Test 9: Simple Goto - goto label; label: return;
// ============================================================================
TEST_F(StatementHandlerTest, SimpleGoto) {
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create: goto end;
    clang::GotoStmt* gotoStmt = createGotoStmt("end");

    // Create: end: return;
    clang::ReturnStmt* returnStmt = clang::ReturnStmt::Create(
        ctx, clang::SourceLocation(), nullptr, nullptr
    );
    clang::LabelStmt* labelStmt = createLabelStmt("end", returnStmt);

    // Test goto translation
    StatementHandler handler;
    clang::Stmt* gotoResult = handler.handleStmt(gotoStmt, *context);

    ASSERT_NE(gotoResult, nullptr);
    auto* cGoto = llvm::dyn_cast<clang::GotoStmt>(gotoResult);
    ASSERT_NE(cGoto, nullptr);
    ASSERT_NE(cGoto->getLabel(), nullptr);
    EXPECT_EQ(cGoto->getLabel()->getName(), "end");

    // Test label translation
    clang::Stmt* labelResult = handler.handleStmt(labelStmt, *context);

    ASSERT_NE(labelResult, nullptr);
    auto* cLabel = llvm::dyn_cast<clang::LabelStmt>(labelResult);
    ASSERT_NE(cLabel, nullptr);
    ASSERT_NE(cLabel->getDecl(), nullptr);
    EXPECT_EQ(cLabel->getDecl()->getName(), "end");
    ASSERT_NE(cLabel->getSubStmt(), nullptr);
}

// ============================================================================
// Test 10: Goto Forward Jump - goto later in code
// ============================================================================
TEST_F(StatementHandlerTest, GotoForwardJump) {
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create: goto skip;
    clang::GotoStmt* gotoStmt = createGotoStmt("skip");

    // Create some intermediate statement
    clang::IntegerLiteral* lit = createIntLiteral(42);

    // Create: skip: ;
    clang::NullStmt* nullStmt = new (ctx) clang::NullStmt(clang::SourceLocation());
    clang::LabelStmt* labelStmt = createLabelStmt("skip", nullStmt);

    // Create compound: { goto skip; x = 42; skip: ; }
    clang::CompoundStmt* compound = createCompoundStmt({gotoStmt, labelStmt});

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(compound, *context);

    ASSERT_NE(result, nullptr);
    auto* cCompound = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cCompound, nullptr);
    EXPECT_EQ(cCompound->size(), 2);

    // Verify goto was translated
    auto* cGoto = llvm::dyn_cast<clang::GotoStmt>(cCompound->body_front());
    ASSERT_NE(cGoto, nullptr);
}

// ============================================================================
// Test 11: Goto Backward Jump - goto earlier in code
// ============================================================================
TEST_F(StatementHandlerTest, GotoBackwardJump) {
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create: start: ;
    clang::NullStmt* nullStmt = new (ctx) clang::NullStmt(clang::SourceLocation());
    clang::LabelStmt* labelStmt = createLabelStmt("start", nullStmt);

    // Create: goto start;
    clang::GotoStmt* gotoStmt = createGotoStmt("start");

    // Create compound: { start: ; goto start; }
    clang::CompoundStmt* compound = createCompoundStmt({labelStmt, gotoStmt});

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(compound, *context);

    ASSERT_NE(result, nullptr);
    auto* cCompound = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cCompound, nullptr);
    EXPECT_EQ(cCompound->size(), 2);
}

// ============================================================================
// Test 12: Label With Statement - label: return 42;
// ============================================================================
TEST_F(StatementHandlerTest, LabelWithStatement) {
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create: return 42;
    clang::IntegerLiteral* lit = createIntLiteral(42);
    clang::ReturnStmt* returnStmt = clang::ReturnStmt::Create(
        ctx, clang::SourceLocation(), lit, nullptr
    );

    // Create: done: return 42;
    clang::LabelStmt* labelStmt = createLabelStmt("done", returnStmt);

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(labelStmt, *context);

    ASSERT_NE(result, nullptr);
    auto* cLabel = llvm::dyn_cast<clang::LabelStmt>(result);
    ASSERT_NE(cLabel, nullptr);
    EXPECT_EQ(cLabel->getDecl()->getName(), "done");

    // Verify sub-statement was translated
    auto* cReturn = llvm::dyn_cast<clang::ReturnStmt>(cLabel->getSubStmt());
    ASSERT_NE(cReturn, nullptr);
}

// ============================================================================
// Test 13: Goto In Loop (break-like behavior) - while(1) { goto end; } end:
// ============================================================================
TEST_F(StatementHandlerTest, GotoInLoop) {
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create: goto end;
    clang::GotoStmt* gotoStmt = createGotoStmt("end");
    clang::CompoundStmt* loopBody = createCompoundStmt({gotoStmt});

    // Create: while (1) { goto end; }
    clang::IntegerLiteral* cond = createIntLiteral(1);
    clang::WhileStmt* whileStmt = createWhileStmt(cond, loopBody);

    // Create: end: ;
    clang::NullStmt* nullStmt = new (ctx) clang::NullStmt(clang::SourceLocation());
    clang::LabelStmt* labelStmt = createLabelStmt("end", nullStmt);

    // Create compound: { while (1) { goto end; } end: ; }
    clang::CompoundStmt* compound = createCompoundStmt({whileStmt, labelStmt});

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(compound, *context);

    ASSERT_NE(result, nullptr);
    auto* cCompound = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cCompound, nullptr);
    EXPECT_EQ(cCompound->size(), 2);

    // Verify while loop contains goto
    auto* cWhile = llvm::dyn_cast<clang::WhileStmt>(cCompound->body_front());
    ASSERT_NE(cWhile, nullptr);
    auto* cWhileBody = llvm::dyn_cast<clang::CompoundStmt>(cWhile->getBody());
    ASSERT_NE(cWhileBody, nullptr);
}

// ============================================================================
// Test 14: Multiple Labels - multiple labels in same scope
// ============================================================================
TEST_F(StatementHandlerTest, MultipleLabels) {
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create: label1: ;
    clang::NullStmt* null1 = new (ctx) clang::NullStmt(clang::SourceLocation());
    clang::LabelStmt* label1 = createLabelStmt("label1", null1);

    // Create: label2: ;
    clang::NullStmt* null2 = new (ctx) clang::NullStmt(clang::SourceLocation());
    clang::LabelStmt* label2 = createLabelStmt("label2", null2);

    // Create: goto label1;
    clang::GotoStmt* goto1 = createGotoStmt("label1");

    // Create: goto label2;
    clang::GotoStmt* goto2 = createGotoStmt("label2");

    // Create compound with multiple labels
    clang::CompoundStmt* compound = createCompoundStmt({label1, goto2, label2, goto1});

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(compound, *context);

    ASSERT_NE(result, nullptr);
    auto* cCompound = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cCompound, nullptr);
    EXPECT_EQ(cCompound->size(), 4);
}

// ============================================================================
// Test 15: Goto In Switch - switch case with goto
// ============================================================================
TEST_F(StatementHandlerTest, GotoInSwitch) {
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create: goto default_case;
    clang::GotoStmt* gotoStmt = createGotoStmt("default_case");

    // Create: default_case: return;
    clang::ReturnStmt* returnStmt = clang::ReturnStmt::Create(
        ctx, clang::SourceLocation(), nullptr, nullptr
    );
    clang::LabelStmt* labelStmt = createLabelStmt("default_case", returnStmt);

    // Create compound: { goto default_case; default_case: return; }
    clang::CompoundStmt* compound = createCompoundStmt({gotoStmt, labelStmt});

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(compound, *context);

    ASSERT_NE(result, nullptr);
    auto* cCompound = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cCompound, nullptr);
    EXPECT_EQ(cCompound->size(), 2);
}

// ============================================================================
// Test 16: Nested Goto Scopes - goto across nested blocks
// ============================================================================
TEST_F(StatementHandlerTest, NestedGotoScopes) {
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create: goto outer;
    clang::GotoStmt* gotoOuter = createGotoStmt("outer");

    // Create inner block: { goto outer; }
    clang::CompoundStmt* innerBlock = createCompoundStmt({gotoOuter});

    // Create: outer: ;
    clang::NullStmt* nullStmt = new (ctx) clang::NullStmt(clang::SourceLocation());
    clang::LabelStmt* labelOuter = createLabelStmt("outer", nullStmt);

    // Create outer block: { { goto outer; } outer: ; }
    clang::CompoundStmt* outerBlock = createCompoundStmt({innerBlock, labelOuter});

    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(outerBlock, *context);

    ASSERT_NE(result, nullptr);
    auto* cOuter = llvm::dyn_cast<clang::CompoundStmt>(result);
    ASSERT_NE(cOuter, nullptr);
    EXPECT_EQ(cOuter->size(), 2);

    // Verify nested block structure
    auto* cInner = llvm::dyn_cast<clang::CompoundStmt>(cOuter->body_front());
    ASSERT_NE(cInner, nullptr);
    EXPECT_EQ(cInner->size(), 1);
}

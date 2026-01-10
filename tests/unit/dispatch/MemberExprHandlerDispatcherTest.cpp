/**
 * @file MemberExprHandlerDispatcherTest.cpp
 * @brief Unit tests for MemberExprHandler with recursive dispatch
 *
 * Verifies:
 * - Handler registration
 * - Recursive dispatch of base expression
 * - Direct member access (obj.field)
 * - Indirect member access (ptr->field)
 * - Nested member access (obj.inner.field)
 * - Integration with ExprMapper
 * - Arrow vs dot preservation
 * - Member access on complex base expressions
 */

#include "dispatch/MemberExprHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "mapping/FieldOffsetMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/Casting.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

template<typename T>
T* findNode(Stmt* root) {
    if (!root) return nullptr;
    if (auto* node = dyn_cast<T>(root)) return node;
    for (auto* child : root->children()) {
        if (auto* found = findNode<T>(child)) return found;
    }
    return nullptr;
}

template<typename T>
void findAllNodes(Stmt* root, std::vector<T*>& results) {
    if (!root) return;
    if (auto* node = dyn_cast<T>(root)) {
        results.push_back(node);
    }
    for (auto* child : root->children()) {
        findAllNodes<T>(child, results);
    }
}

// ============================================================================
// Test: MemberExprHandler Registration
// ============================================================================

TEST(MemberExprHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        struct Point { int x; };
        int test() {
            Point p;
            return p.x;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    MemberExpr* memberExpr = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                memberExpr = findNode<MemberExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(memberExpr, nullptr);
    EXPECT_FALSE(memberExpr->isArrow()) << "Should be dot access, not arrow";

    bool handled = dispatcher.dispatch(cppCtx, cCtx, memberExpr);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(memberExpr);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<MemberExpr>(cExpr));
}

// ============================================================================
// Test: Predicate Correctly Identifies MemberExpr
// ============================================================================

TEST(MemberExprHandlerDispatcherTest, PredicateCorrectness) {
    const char *cpp = R"(
        struct Point { int x; };
        int test() {
            Point p;
            return p.x;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();

    MemberExpr* memberExpr = nullptr;
    DeclRefExpr* declRefExpr = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                memberExpr = findNode<MemberExpr>(FD->getBody());
                declRefExpr = findNode<DeclRefExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(memberExpr, nullptr);
    ASSERT_NE(declRefExpr, nullptr);

    // Predicate should match MemberExpr
    EXPECT_TRUE(cpptoc::MemberExprHandler::canHandle(memberExpr));

    // Predicate should NOT match DeclRefExpr
    EXPECT_FALSE(cpptoc::MemberExprHandler::canHandle(declRefExpr));
}

// ============================================================================
// Test: Direct Member Access (obj.field)
// ============================================================================

TEST(MemberExprHandlerDispatcherTest, DirectMemberAccess) {
    const char *cpp = R"(
        struct Point { int x; int y; };
        int test() {
            Point p;
            return p.x;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    MemberExpr* memberExpr = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                memberExpr = findNode<MemberExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(memberExpr, nullptr);
    EXPECT_FALSE(memberExpr->isArrow());

    bool handled = dispatcher.dispatch(cppCtx, cCtx, memberExpr);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(memberExpr);
    ASSERT_NE(cExpr, nullptr);

    auto* cMemberExpr = dyn_cast<MemberExpr>(cExpr);
    ASSERT_NE(cMemberExpr, nullptr);
    EXPECT_FALSE(cMemberExpr->isArrow()) << "Should preserve dot access";
}

// ============================================================================
// Test: Indirect Member Access (ptr->field)
// ============================================================================

TEST(MemberExprHandlerDispatcherTest, IndirectMemberAccess) {
    const char *cpp = R"(
        struct Point { int x; int y; };
        int test(Point* p) {
            return p->x;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    MemberExpr* memberExpr = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                memberExpr = findNode<MemberExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(memberExpr, nullptr);
    EXPECT_TRUE(memberExpr->isArrow());

    bool handled = dispatcher.dispatch(cppCtx, cCtx, memberExpr);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(memberExpr);
    ASSERT_NE(cExpr, nullptr);

    auto* cMemberExpr = dyn_cast<MemberExpr>(cExpr);
    ASSERT_NE(cMemberExpr, nullptr);
    EXPECT_TRUE(cMemberExpr->isArrow()) << "Should preserve arrow access";
}

// ============================================================================
// Test: Nested Member Access (obj.inner.field)
// ============================================================================

TEST(MemberExprHandlerDispatcherTest, NestedMemberAccess) {
    const char *cpp = R"(
        struct Inner { int value; };
        struct Outer { Inner inner; };
        int test() {
            Outer o;
            return o.inner.value;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);

    // Find all MemberExpr nodes
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<MemberExpr*> memberExprs;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                findAllNodes<MemberExpr>(FD->getBody(), memberExprs);
                break;
            }
        }
    }

    ASSERT_EQ(memberExprs.size(), 2) << "Should find 2 MemberExpr nodes: o.inner and inner.value";

    // Find the outer MemberExpr (o.inner.value)
    MemberExpr* outerMemberExpr = nullptr;
    for (auto* me : memberExprs) {
        if (me->getMemberDecl()->getNameAsString() == "value") {
            outerMemberExpr = me;
            break;
        }
    }
    ASSERT_NE(outerMemberExpr, nullptr);

    // Verify the base is also a MemberExpr
    auto* innerMemberExpr = dyn_cast<MemberExpr>(outerMemberExpr->getBase());
    ASSERT_NE(innerMemberExpr, nullptr);
    EXPECT_EQ(innerMemberExpr->getMemberDecl()->getNameAsString(), "inner");

    // Dispatch outer (should recursively dispatch inner)
    bool handled = dispatcher.dispatch(cppCtx, cCtx, outerMemberExpr);
    ASSERT_TRUE(handled);

    // Verify both outer and inner were translated
    Expr* cOuterExpr = exprMapper.getCreated(outerMemberExpr);
    ASSERT_NE(cOuterExpr, nullptr);

    Expr* cInnerExpr = exprMapper.getCreated(innerMemberExpr);
    ASSERT_NE(cInnerExpr, nullptr);

    auto* cOuterMemberExpr = dyn_cast<MemberExpr>(cOuterExpr);
    ASSERT_NE(cOuterMemberExpr, nullptr);
    EXPECT_FALSE(cOuterMemberExpr->isArrow());
}

// ============================================================================
// Test: Mixed Arrow and Dot Access (ptr->inner.field)
// ============================================================================

TEST(MemberExprHandlerDispatcherTest, MixedArrowDotAccess) {
    const char *cpp = R"(
        struct Inner { int value; };
        struct Outer { Inner inner; };
        int test(Outer* ptr) {
            return ptr->inner.value;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<MemberExpr*> memberExprs;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                findAllNodes<MemberExpr>(FD->getBody(), memberExprs);
                break;
            }
        }
    }

    ASSERT_EQ(memberExprs.size(), 2) << "Should find 2 MemberExpr nodes";

    // Find outer (inner.value - dot) and inner (ptr->inner - arrow)
    MemberExpr* dotAccess = nullptr;
    MemberExpr* arrowAccess = nullptr;

    for (auto* me : memberExprs) {
        if (me->getMemberDecl()->getNameAsString() == "value") {
            dotAccess = me;
        } else if (me->getMemberDecl()->getNameAsString() == "inner") {
            arrowAccess = me;
        }
    }

    ASSERT_NE(dotAccess, nullptr);
    ASSERT_NE(arrowAccess, nullptr);
    EXPECT_FALSE(dotAccess->isArrow());
    EXPECT_TRUE(arrowAccess->isArrow());

    // Dispatch and verify
    bool handled = dispatcher.dispatch(cppCtx, cCtx, dotAccess);
    ASSERT_TRUE(handled);

    auto* cDotExpr = dyn_cast<MemberExpr>(exprMapper.getCreated(dotAccess));
    auto* cArrowExpr = dyn_cast<MemberExpr>(exprMapper.getCreated(arrowAccess));

    ASSERT_NE(cDotExpr, nullptr);
    ASSERT_NE(cArrowExpr, nullptr);
    EXPECT_FALSE(cDotExpr->isArrow()) << "Should preserve dot access";
    EXPECT_TRUE(cArrowExpr->isArrow()) << "Should preserve arrow access";
}

// ============================================================================
// Test: Multiple Field Accesses
// ============================================================================

TEST(MemberExprHandlerDispatcherTest, MultipleFieldAccesses) {
    const char *cpp = R"(
        struct Point { int x; int y; };
        int test() {
            Point p;
            return p.x + p.y;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<MemberExpr*> memberExprs;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                findAllNodes<MemberExpr>(FD->getBody(), memberExprs);
                break;
            }
        }
    }

    ASSERT_EQ(memberExprs.size(), 2) << "Should find 2 MemberExpr nodes: p.x and p.y";

    // Dispatch all
    for (auto* me : memberExprs) {
        dispatcher.dispatch(cppCtx, cCtx, me);
    }

    // Verify all translated
    for (auto* me : memberExprs) {
        Expr* cExpr = exprMapper.getCreated(me);
        EXPECT_NE(cExpr, nullptr);
        EXPECT_TRUE(isa<MemberExpr>(cExpr));
    }
}

// ============================================================================
// Test: ExprMapper Integration (no duplicate translation)
// ============================================================================

TEST(MemberExprHandlerDispatcherTest, ExprMapperIntegration) {
    const char *cpp = R"(
        struct Point { int x; };
        int test() {
            Point p;
            return p.x;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    MemberExpr* memberExpr = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                memberExpr = findNode<MemberExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(memberExpr, nullptr);

    // Should not be in mapper before dispatch
    EXPECT_FALSE(exprMapper.hasCreated(memberExpr));

    // First dispatch
    bool handled1 = dispatcher.dispatch(cppCtx, cCtx, memberExpr);
    EXPECT_TRUE(handled1);

    // Should be in mapper after dispatch
    EXPECT_TRUE(exprMapper.hasCreated(memberExpr));
    Expr* cExpr1 = exprMapper.getCreated(memberExpr);
    ASSERT_NE(cExpr1, nullptr);

    // Second dispatch should not create a new node
    bool handled2 = dispatcher.dispatch(cppCtx, cCtx, memberExpr);
    EXPECT_TRUE(handled2);

    Expr* cExpr2 = exprMapper.getCreated(memberExpr);
    EXPECT_EQ(cExpr1, cExpr2) << "Should return same C expression on second dispatch";
}

// ============================================================================
// Test: Base Expression Translation
// ============================================================================

TEST(MemberExprHandlerDispatcherTest, BaseExpressionTranslation) {
    const char *cpp = R"(
        struct Point { int x; };
        int test() {
            Point p;
            return p.x;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    MemberExpr* memberExpr = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                memberExpr = findNode<MemberExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(memberExpr, nullptr);

    // Get base expression (should be DeclRefExpr)
    const Expr* cppBase = memberExpr->getBase();
    ASSERT_NE(cppBase, nullptr);

    // Base should not be translated yet
    EXPECT_FALSE(exprMapper.hasCreated(cppBase));

    // Dispatch MemberExpr (should recursively dispatch base)
    bool handled = dispatcher.dispatch(cppCtx, cCtx, memberExpr);
    ASSERT_TRUE(handled);

    // Base should now be translated
    EXPECT_TRUE(exprMapper.hasCreated(cppBase));

    // Verify C MemberExpr uses translated base
    auto* cMemberExpr = dyn_cast<MemberExpr>(exprMapper.getCreated(memberExpr));
    ASSERT_NE(cMemberExpr, nullptr);

    Expr* cBase = cMemberExpr->getBase();
    ASSERT_NE(cBase, nullptr);

    // C base should be the same as what's in ExprMapper for C++ base
    Expr* mappedBase = exprMapper.getCreated(cppBase);
    EXPECT_EQ(cBase, mappedBase) << "C MemberExpr should use translated base from ExprMapper";
}

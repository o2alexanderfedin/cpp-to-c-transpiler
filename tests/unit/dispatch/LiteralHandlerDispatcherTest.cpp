/**
 * @file LiteralHandlerDispatcherTest.cpp
 * @brief Unit tests for LiteralHandler dispatcher integration
 *
 * Verifies:
 * - Handler registration with dispatcher
 * - canHandle predicate behavior (literals yes, non-literals no)
 * - All literal types: IntegerLiteral, FloatingLiteral, StringLiteral, CharacterLiteral, CXXBoolLiteralExpr
 * - Integration with ExprMapper
 * - Multiple literal translation
 */

#include "dispatch/LiteralHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/Casting.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

// Helper to build AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

// Helper to find IntegerLiteral in AST
IntegerLiteral* findIntegerLiteral(Stmt* root, int value) {
    if (!root) return nullptr;

    if (auto* intLit = dyn_cast<IntegerLiteral>(root)) {
        if (intLit->getValue() == value) {
            return intLit;
        }
    }

    for (auto* child : root->children()) {
        if (auto* found = findIntegerLiteral(child, value)) {
            return found;
        }
    }
    return nullptr;
}

// Helper to find first literal of specific type
template<typename T>
T* findLiteral(Stmt* root) {
    if (!root) return nullptr;

    if (auto* lit = dyn_cast<T>(root)) {
        return lit;
    }

    for (auto* child : root->children()) {
        if (auto* found = findLiteral<T>(child)) {
            return found;
        }
    }
    return nullptr;
}

// ============================================================================
// Test: LiteralHandler Registration
// ============================================================================

TEST(LiteralHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        int test() {
            return 42;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    // Setup components
    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    // Create mapping utilities
    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    // Create dispatcher
    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register LiteralHandler
    cpptoc::LiteralHandler::registerWith(dispatcher);

    // Find IntegerLiteral(42)
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    IntegerLiteral* intLit = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                intLit = findIntegerLiteral(FD->getBody(), 42);
                if (intLit) break;
            }
        }
    }

    ASSERT_NE(intLit, nullptr) << "Failed to find IntegerLiteral(42)";

    // Dispatch the literal
    bool handled = dispatcher.dispatch(cppCtx, cCtx, intLit);

    // Verify handler was invoked
    EXPECT_TRUE(handled) << "IntegerLiteral should be handled by LiteralHandler";

    // Verify expression was mapped
    Expr* translatedExpr = exprMapper.getCreated(intLit);
    EXPECT_NE(translatedExpr, nullptr) << "LiteralHandler should create mapping";
    EXPECT_TRUE(isa<IntegerLiteral>(translatedExpr)) << "Translated expression should be IntegerLiteral";
}

// ============================================================================
// Test: IntegerLiteral Translation
// ============================================================================

TEST(LiteralHandlerDispatcherTest, IntegerLiteralTranslation) {
    const char *cpp = R"(
        int test() { return 123; }
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);

    // Find IntegerLiteral
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    IntegerLiteral* cppIntLit = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                cppIntLit = findIntegerLiteral(FD->getBody(), 123);
                break;
            }
        }
    }

    ASSERT_NE(cppIntLit, nullptr);

    // Dispatch and translate
    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppIntLit);
    ASSERT_TRUE(handled);

    // Verify translation
    Expr* cExpr = exprMapper.getCreated(cppIntLit);
    ASSERT_NE(cExpr, nullptr);

    auto* cIntLit = dyn_cast<IntegerLiteral>(cExpr);
    ASSERT_NE(cIntLit, nullptr);
    EXPECT_EQ(cIntLit->getValue(), 123);
}

// ============================================================================
// Test: FloatingLiteral Translation
// ============================================================================

TEST(LiteralHandlerDispatcherTest, FloatingLiteralTranslation) {
    const char *cpp = R"(
        double test() { return 3.14; }
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);

    // Find FloatingLiteral
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    FloatingLiteral* cppFloatLit = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                cppFloatLit = findLiteral<FloatingLiteral>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(cppFloatLit, nullptr);

    // Dispatch and translate
    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppFloatLit);
    ASSERT_TRUE(handled);

    // Verify translation
    Expr* cExpr = exprMapper.getCreated(cppFloatLit);
    ASSERT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<FloatingLiteral>(cExpr));
}

// ============================================================================
// Test: StringLiteral Translation
// ============================================================================

TEST(LiteralHandlerDispatcherTest, StringLiteralTranslation) {
    const char *cpp = R"(
        const char* test() { return "hello"; }
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);

    // Find StringLiteral
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    StringLiteral* cppStrLit = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                cppStrLit = findLiteral<StringLiteral>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(cppStrLit, nullptr);

    // Dispatch and translate
    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppStrLit);
    ASSERT_TRUE(handled);

    // Verify translation
    Expr* cExpr = exprMapper.getCreated(cppStrLit);
    ASSERT_NE(cExpr, nullptr);

    auto* cStrLit = dyn_cast<StringLiteral>(cExpr);
    ASSERT_NE(cStrLit, nullptr);
    EXPECT_EQ(cStrLit->getString(), "hello");
}

// ============================================================================
// Test: CharacterLiteral Translation
// ============================================================================

TEST(LiteralHandlerDispatcherTest, CharacterLiteralTranslation) {
    const char *cpp = R"(
        char test() { return 'a'; }
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);

    // Find CharacterLiteral
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CharacterLiteral* cppCharLit = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                cppCharLit = findLiteral<CharacterLiteral>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(cppCharLit, nullptr);

    // Dispatch and translate
    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppCharLit);
    ASSERT_TRUE(handled);

    // Verify translation
    Expr* cExpr = exprMapper.getCreated(cppCharLit);
    ASSERT_NE(cExpr, nullptr);

    auto* cCharLit = dyn_cast<CharacterLiteral>(cExpr);
    ASSERT_NE(cCharLit, nullptr);
    EXPECT_EQ(cCharLit->getValue(), 'a');
}

// ============================================================================
// Test: CXXBoolLiteralExpr Translation (true/false → 1/0)
// ============================================================================

TEST(LiteralHandlerDispatcherTest, BoolLiteralTranslation) {
    const char *cpp = R"(
        bool test() { return true; }
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);

    // Find CXXBoolLiteralExpr
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXBoolLiteralExpr* cppBoolLit = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                cppBoolLit = findLiteral<CXXBoolLiteralExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(cppBoolLit, nullptr);
    EXPECT_TRUE(cppBoolLit->getValue()) << "Should be true";

    // Dispatch and translate
    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppBoolLit);
    ASSERT_TRUE(handled);

    // Verify translation: true → 1 (IntegerLiteral)
    Expr* cExpr = exprMapper.getCreated(cppBoolLit);
    ASSERT_NE(cExpr, nullptr);

    auto* cIntLit = dyn_cast<IntegerLiteral>(cExpr);
    ASSERT_NE(cIntLit, nullptr) << "Bool should be translated to IntegerLiteral in C";
    EXPECT_EQ(cIntLit->getValue(), 1) << "true should become 1";
}

// ============================================================================
// Test: Multiple Literal Translations
// ============================================================================

TEST(LiteralHandlerDispatcherTest, MultipleLiterals) {
    const char *cpp = R"(
        int test() {
            int a = 10;
            int b = 20;
            int c = 30;
            return a + b + c;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);

    // Find all IntegerLiterals
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<IntegerLiteral*> literals;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                for (int val : {10, 20, 30}) {
                    if (auto* lit = findIntegerLiteral(FD->getBody(), val)) {
                        literals.push_back(lit);
                    }
                }
                break;
            }
        }
    }

    ASSERT_EQ(literals.size(), 3) << "Should find 3 literals";

    // Dispatch all literals
    for (auto* lit : literals) {
        bool handled = dispatcher.dispatch(cppCtx, cCtx, lit);
        EXPECT_TRUE(handled);
    }

    // Verify all were translated
    for (auto* lit : literals) {
        Expr* cExpr = exprMapper.getCreated(lit);
        EXPECT_NE(cExpr, nullptr);
        EXPECT_TRUE(isa<IntegerLiteral>(cExpr));
    }
}

// ============================================================================
// Test: Non-Literal Should Not Be Handled
// ============================================================================

TEST(LiteralHandlerDispatcherTest, NonLiteralNotHandled) {
    const char *cpp = R"(
        int test(int x) { return x; }
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);

    // Find DeclRefExpr (not a literal)
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    DeclRefExpr* declRef = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                declRef = findLiteral<DeclRefExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(declRef, nullptr);

    // DeclRefExpr should NOT be handled by LiteralHandler
    bool handled = dispatcher.dispatch(cppCtx, cCtx, declRef);
    EXPECT_FALSE(handled) << "DeclRefExpr should not be handled by LiteralHandler";
}

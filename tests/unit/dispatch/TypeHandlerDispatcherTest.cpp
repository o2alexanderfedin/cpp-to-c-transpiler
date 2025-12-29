/**
 * @file TypeHandlerDispatcherTest.cpp
 * @brief Unit tests for TypeHandler dispatcher integration
 *
 * Verifies:
 * - Handler registration with dispatcher
 * - canHandle predicate behavior (reference types yes, other types no)
 * - Type translation (lvalue reference → pointer, rvalue reference → pointer)
 * - Integration with TypeMapper
 * - Pass-through behavior for non-reference types
 */

#include "dispatch/TypeHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Type.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/Casting.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

// Helper to build AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

// ============================================================================
// Test: TypeHandler Registration
// ============================================================================

TEST(TypeHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        void func(int& ref, int val) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    // Setup components
    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    // Create mapping utilities
    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    // Create dispatcher
    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register TypeHandler
    cpptoc::TypeHandler::registerWith(dispatcher);

    // Find the function parameter types
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    FunctionDecl* funcDecl = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "func") {
                funcDecl = FD;
                break;
            }
        }
    }

    ASSERT_NE(funcDecl, nullptr) << "Failed to find function 'func'";
    ASSERT_EQ(funcDecl->getNumParams(), 2) << "Function should have 2 parameters";

    // Get reference parameter type (int&)
    ParmVarDecl* refParam = funcDecl->getParamDecl(0);
    QualType refType = refParam->getType();
    const Type* refTypePtr = refType.getTypePtr();

    ASSERT_TRUE(isa<LValueReferenceType>(refTypePtr)) << "First param should be lvalue reference";

    // Dispatch the reference type
    bool handled = dispatcher.dispatch(cppCtx, cCtx, const_cast<Type*>(refTypePtr));

    // Verify handler was invoked
    EXPECT_TRUE(handled) << "LValueReferenceType should be handled by TypeHandler";

    // Verify type was mapped
    QualType translatedType = typeMapper.getCreatedType(refTypePtr);
    EXPECT_FALSE(translatedType.isNull()) << "TypeHandler should create mapping";
    EXPECT_TRUE(translatedType->isPointerType()) << "Reference should be translated to pointer";
}

// ============================================================================
// Test: LValue Reference Translation
// ============================================================================

TEST(TypeHandlerDispatcherTest, LValueReferenceTranslation) {
    const char *cpp = R"(
        void func(int& ref) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);

    // Find the function parameter type
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    FunctionDecl* funcDecl = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            funcDecl = FD;
            break;
        }
    }

    ASSERT_NE(funcDecl, nullptr);
    ParmVarDecl* refParam = funcDecl->getParamDecl(0);
    QualType refType = refParam->getType();
    const Type* refTypePtr = refType.getTypePtr();

    // Dispatch and translate
    bool handled = dispatcher.dispatch(cppCtx, cCtx, const_cast<Type*>(refTypePtr));
    ASSERT_TRUE(handled);

    // Verify translation: int& → int*
    QualType translatedType = typeMapper.getCreatedType(refTypePtr);
    ASSERT_FALSE(translatedType.isNull());
    EXPECT_TRUE(translatedType->isPointerType()) << "int& should become int*";

    // Verify pointee type is int
    const PointerType* ptrType = cast<PointerType>(translatedType.getTypePtr());
    QualType pointeeType = ptrType->getPointeeType();
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Pointee should be int";
}

// ============================================================================
// Test: RValue Reference Translation
// ============================================================================

TEST(TypeHandlerDispatcherTest, RValueReferenceTranslation) {
    const char *cpp = R"(
        void func(int&& rref) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);

    // Find the function parameter type
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    FunctionDecl* funcDecl = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            funcDecl = FD;
            break;
        }
    }

    ASSERT_NE(funcDecl, nullptr);
    ParmVarDecl* rrefParam = funcDecl->getParamDecl(0);
    QualType rrefType = rrefParam->getType();
    const Type* rrefTypePtr = rrefType.getTypePtr();

    ASSERT_TRUE(isa<RValueReferenceType>(rrefTypePtr));

    // Dispatch and translate
    bool handled = dispatcher.dispatch(cppCtx, cCtx, const_cast<Type*>(rrefTypePtr));
    ASSERT_TRUE(handled);

    // Verify translation: int&& → int*
    QualType translatedType = typeMapper.getCreatedType(rrefTypePtr);
    ASSERT_FALSE(translatedType.isNull());
    EXPECT_TRUE(translatedType->isPointerType()) << "int&& should become int*";

    // Verify pointee type is int
    const PointerType* ptrType = cast<PointerType>(translatedType.getTypePtr());
    QualType pointeeType = ptrType->getPointeeType();
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Pointee should be int";
}

// ============================================================================
// Test: Const Reference Translation
// ============================================================================

TEST(TypeHandlerDispatcherTest, ConstReferenceTranslation) {
    const char *cpp = R"(
        void func(const int& cref) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);

    // Find the function parameter type
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    FunctionDecl* funcDecl = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            funcDecl = FD;
            break;
        }
    }

    ASSERT_NE(funcDecl, nullptr);
    ParmVarDecl* crefParam = funcDecl->getParamDecl(0);
    QualType crefType = crefParam->getType();
    const Type* crefTypePtr = crefType.getTypePtr();

    // Dispatch and translate
    bool handled = dispatcher.dispatch(cppCtx, cCtx, const_cast<Type*>(crefTypePtr));
    ASSERT_TRUE(handled);

    // Verify translation: const int& → const int*
    QualType translatedType = typeMapper.getCreatedType(crefTypePtr);
    ASSERT_FALSE(translatedType.isNull());
    EXPECT_TRUE(translatedType->isPointerType()) << "const int& should become const int*";

    // Verify pointee type is const int
    const PointerType* ptrType = cast<PointerType>(translatedType.getTypePtr());
    QualType pointeeType = ptrType->getPointeeType();
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Pointee should be int";
    EXPECT_TRUE(pointeeType.isConstQualified()) << "Pointee should be const";
}

// ============================================================================
// Test: Pass-Through Non-Reference Types
// ============================================================================

TEST(TypeHandlerDispatcherTest, PassThroughNonReferenceTypes) {
    const char *cpp = R"(
        void func(int val) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);

    // Find the function parameter type
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    FunctionDecl* funcDecl = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            funcDecl = FD;
            break;
        }
    }

    ASSERT_NE(funcDecl, nullptr);
    ParmVarDecl* valParam = funcDecl->getParamDecl(0);
    QualType valType = valParam->getType();
    const Type* valTypePtr = valType.getTypePtr();

    ASSERT_FALSE(isa<LValueReferenceType>(valTypePtr)) << "Should not be reference";
    ASSERT_FALSE(isa<RValueReferenceType>(valTypePtr)) << "Should not be reference";

    // Non-reference types should NOT be handled by TypeHandler
    bool handled = dispatcher.dispatch(cppCtx, cCtx, const_cast<Type*>(valTypePtr));
    EXPECT_FALSE(handled) << "Non-reference types should not be handled by TypeHandler";
}

// ============================================================================
// Test: Multiple Type Translations
// ============================================================================

TEST(TypeHandlerDispatcherTest, MultipleTypeTranslations) {
    const char *cpp = R"(
        void func(int& ref1, const int& ref2, int&& rref, int val) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);

    // Find the function
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    FunctionDecl* funcDecl = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            funcDecl = FD;
            break;
        }
    }

    ASSERT_NE(funcDecl, nullptr);
    ASSERT_EQ(funcDecl->getNumParams(), 4);

    // Translate all parameter types
    for (unsigned i = 0; i < funcDecl->getNumParams(); ++i) {
        ParmVarDecl* param = funcDecl->getParamDecl(i);
        QualType paramType = param->getType();
        const Type* paramTypePtr = paramType.getTypePtr();

        dispatcher.dispatch(cppCtx, cCtx, const_cast<Type*>(paramTypePtr));
    }

    // Verify all reference types were translated
    // ref1: int& → int*
    const Type* ref1Type = funcDecl->getParamDecl(0)->getType().getTypePtr();
    QualType ref1Translated = typeMapper.getCreatedType(ref1Type);
    EXPECT_FALSE(ref1Translated.isNull());
    EXPECT_TRUE(ref1Translated->isPointerType());

    // ref2: const int& → const int*
    const Type* ref2Type = funcDecl->getParamDecl(1)->getType().getTypePtr();
    QualType ref2Translated = typeMapper.getCreatedType(ref2Type);
    EXPECT_FALSE(ref2Translated.isNull());
    EXPECT_TRUE(ref2Translated->isPointerType());

    // rref: int&& → int*
    const Type* rrefType = funcDecl->getParamDecl(2)->getType().getTypePtr();
    QualType rrefTranslated = typeMapper.getCreatedType(rrefType);
    EXPECT_FALSE(rrefTranslated.isNull());
    EXPECT_TRUE(rrefTranslated->isPointerType());

    // val: int (no translation, should not be in map)
    const Type* valType = funcDecl->getParamDecl(3)->getType().getTypePtr();
    QualType valTranslated = typeMapper.getCreatedType(valType);
    EXPECT_TRUE(valTranslated.isNull()) << "Non-reference types should not be mapped";
}

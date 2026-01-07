/**
 * @file FunctionHandlerTest.cpp
 * @brief TDD tests for FunctionHandler
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (20+ tests):
 * 1. EmptyFunction - void foo()
 * 2. FunctionWithIntReturn - int bar()
 * 3. FunctionWithOneParam - void baz(int x)
 * 4. FunctionWithTwoParams - int add(int a, int b)
 * 5. FunctionWithFloatReturn - float getValue()
 * ...and more
 */

#include "dispatch/FunctionHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/TypeHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "TargetContext.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class FunctionHandlerTest
 * @brief Test fixture for FunctionHandler
 *
 * Uses dispatcher pattern for testing handler integration.
 */
class FunctionHandlerTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Note: Mappers now use RAII pattern, no reset needed
        // Note: TargetContext is a singleton without reset method
        // Tests should handle TargetContext lifecycle appropriately
    }

    void TearDown() override {
        // Clean up after each test
        // Note: Mappers now use RAII pattern, no reset needed
    }

    /**
     * @brief Helper to create dispatcher with all necessary handlers registered
     */
    std::unique_ptr<CppToCVisitorDispatcher> createDispatcher(
        PathMapper& mapper,
        DeclLocationMapper& locMapper,
        DeclMapper& declMapper,
        TypeMapper& typeMapper,
        ExprMapper& exprMapper,
        StmtMapper& stmtMapper,
        TargetContext& targetCtx
    ) {
        auto dispatcher = std::make_unique<CppToCVisitorDispatcher>(
            mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper,
            targetCtx
        );

        // Register handlers in dependency order
        TypeHandler::registerWith(*dispatcher);
        ParameterHandler::registerWith(*dispatcher);
        FunctionHandler::registerWith(*dispatcher);

        return dispatcher;
    }

    /**
     * @brief Helper to dispatch and retrieve translated function
     */
    clang::FunctionDecl* dispatchAndGetFunction(
        const char* cpp,
        const std::string& funcName,
        clang::ASTContext*& cppCtx,
        clang::ASTContext*& cCtx
    ) {
        std::unique_ptr<clang::ASTUnit> AST = clang::tooling::buildASTFromCode(cpp);
        if (!AST) return nullptr;

        cppCtx = &AST->getASTContext();
        TargetContext targetCtx;
        cCtx = &targetCtx.getContext();

        PathMapper mapper(targetCtx, "/src", "/output");
        DeclLocationMapper locMapper(mapper);
        DeclMapper declMapper;
        TypeMapper typeMapper;
        ExprMapper exprMapper;
        StmtMapper stmtMapper;

        auto dispatcher = createDispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);

        // Find function
        clang::FunctionDecl* cppFunc = nullptr;
        for (auto* D : cppCtx->getTranslationUnitDecl()->decls()) {
            if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
                if (FD->getNameAsString() == funcName && !llvm::isa<clang::CXXMethodDecl>(FD)) {
                    cppFunc = FD;
                    break;
                }
            }
        }
        if (!cppFunc) return nullptr;

        // Dispatch
        dispatcher->dispatch(*cppCtx, *cCtx, cppFunc);

        // Find translated function
        std::string targetPath = dispatcher->getTargetPath(*cppCtx, cppFunc);
        clang::TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);
        if (!cTU) return nullptr;

        for (auto* D : cTU->decls()) {
            if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
                if (FD->getNameAsString() == funcName) {
                    return FD;
                }
            }
        }

        return nullptr;
    }
};

// ============================================================================
// TDD Test 1: Empty Function
// ============================================================================

/**
 * Test 1: Translate empty void function
 *
 * C++ Input:  void foo();
 * C Output:   void foo();
 *
 * This is the simplest possible function - no parameters, void return, no body.
 */
TEST_F(FunctionHandlerTest, EmptyFunction) {
    // Arrange: Build C++ AST with simple function
    const char* cpp = R"(
        void foo();
    )";

    std::unique_ptr<clang::ASTUnit> AST = clang::tooling::buildASTFromCode(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    clang::ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    clang::ASTContext& cCtx = targetCtx.getContext();

    // Create mapping utilities
    PathMapper mapper(targetCtx, "/src", "/output");
    DeclLocationMapper locMapper(mapper);
    DeclMapper declMapper;
    TypeMapper typeMapper;
    ExprMapper exprMapper;
    StmtMapper stmtMapper;

    // Create dispatcher and register handlers
    auto dispatcher = createDispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);

    // Find the function
    clang::TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
            if (FD->getNameAsString() == "foo") {
                cppFunc = FD;
                break;
            }
        }
    }
    ASSERT_NE(cppFunc, nullptr) << "Should find 'foo' function";

    // Act: Dispatch function through handler
    bool handled = dispatcher->dispatch(cppCtx, cCtx, cppFunc);

    // Assert: Verify handler processed the function
    EXPECT_TRUE(handled) << "FunctionDecl should be handled by FunctionHandler";

    // Find translated function in C TranslationUnit
    std::string targetPath = dispatcher->getTargetPath(cppCtx, cppFunc);
    clang::TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);
    ASSERT_NE(cTU, nullptr);

    clang::FunctionDecl* cFunc = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
            if (FD->getNameAsString() == "foo") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr) << "Should find translated function";
    EXPECT_EQ(cFunc->getNameAsString(), "foo") << "Function name mismatch";
    EXPECT_EQ(cFunc->getNumParams(), 0) << "Should have no parameters";
    EXPECT_TRUE(cFunc->getReturnType()->isVoidType()) << "Return type should be void";
}

/**
 * Test 2: Function with int return type
 *
 * C++ Input:  int bar();
 * C Output:   int bar();
 */
TEST_F(FunctionHandlerTest, FunctionWithIntReturn) {
    // Arrange
    const char* cpp = "int bar();";
    std::unique_ptr<clang::ASTUnit> AST = clang::tooling::buildASTFromCode(cpp);
    ASSERT_NE(AST, nullptr);

    clang::ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    clang::ASTContext& cCtx = targetCtx.getContext();

    PathMapper mapper(targetCtx, "/src", "/output");
    DeclLocationMapper locMapper(mapper);
    DeclMapper declMapper;
    TypeMapper typeMapper;
    ExprMapper exprMapper;
    StmtMapper stmtMapper;

    auto dispatcher = createDispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);

    // Find function
    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* D : cppCtx.getTranslationUnitDecl()->decls()) {
        if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
            if (FD->getNameAsString() == "bar") {
                cppFunc = FD;
                break;
            }
        }
    }
    ASSERT_NE(cppFunc, nullptr);

    // Act
    dispatcher->dispatch(cppCtx, cCtx, cppFunc);

    // Assert
    std::string targetPath = dispatcher->getTargetPath(cppCtx, cppFunc);
    clang::TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);
    clang::FunctionDecl* cFunc = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
            if (FD->getNameAsString() == "bar") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "bar");
    EXPECT_EQ(cFunc->getNumParams(), 0);
    EXPECT_TRUE(cFunc->getReturnType()->isIntegerType());
}

/**
 * Test 3: Function with float return type
 *
 * C++ Input:  float getValue();
 * C Output:   float getValue();
 */
TEST_F(FunctionHandlerTest, FunctionWithFloatReturn) {
    // Arrange
    const char* cpp = "float getValue();";
    std::unique_ptr<clang::ASTUnit> AST = clang::tooling::buildASTFromCode(cpp);
    ASSERT_NE(AST, nullptr);

    clang::ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    clang::ASTContext& cCtx = targetCtx.getContext();

    PathMapper mapper(targetCtx, "/src", "/output");
    DeclLocationMapper locMapper(mapper);
    DeclMapper declMapper;
    TypeMapper typeMapper;
    ExprMapper exprMapper;
    StmtMapper stmtMapper;

    auto dispatcher = createDispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);

    // Find function
    clang::FunctionDecl* cppFunc = nullptr;
    for (auto* D : cppCtx.getTranslationUnitDecl()->decls()) {
        if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
            if (FD->getNameAsString() == "getValue") {
                cppFunc = FD;
                break;
            }
        }
    }
    ASSERT_NE(cppFunc, nullptr);

    // Act
    dispatcher->dispatch(cppCtx, cCtx, cppFunc);

    // Assert
    std::string targetPath = dispatcher->getTargetPath(cppCtx, cppFunc);
    clang::TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);
    clang::FunctionDecl* cFunc = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
            if (FD->getNameAsString() == "getValue") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "getValue");
    EXPECT_EQ(cFunc->getNumParams(), 0);
    EXPECT_TRUE(cFunc->getReturnType()->isFloatingType());
}

// ============================================================================
// Phase 42 Tests: Reference Parameters (Task 2)
// ============================================================================

// TODO: Tests below need to be refactored to use dispatcher pattern with buildASTFromCode
// The old pattern of programmatic AST creation is incompatible with the dispatcher architecture
// These tests should be rewritten similar to FunctionHandlerDispatcherTest.cpp

/*
 * Test 4: Function with lvalue reference parameter
 *
 * C++ Input:  void func(int& x);
 * C Output:   void func(int* x);
 *
 * Tests reference parameter transformation to pointer parameter.
 */
TEST_F(FunctionHandlerTest, DISABLED_FunctionWithLValueReferenceParameter) {
    // NOTE: This test is disabled until refactored to use dispatcher pattern
    // See FunctionHandlerDispatcherTest::ReferenceToPointerTranslation for working example
    GTEST_SKIP() << "Test needs refactoring to use dispatcher pattern with buildASTFromCode";

    /* Original test code - kept for reference during refactoring
    // Arrange: Create void func(int& x)
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create parameter: int& x
    clang::QualType intRefType = ctx.getLValueReferenceType(ctx.IntTy);
    clang::IdentifierInfo& paramII = ctx.Idents.get("x");

    clang::ParmVarDecl* cppParam = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &paramII,
        intRefType,
        ctx.getTrivialTypeSourceInfo(intRefType),
        clang::SC_None,
        nullptr
    );

    // Create function: void func(int& x)
    clang::IdentifierInfo& funcII = ctx.Idents.get("func");
    clang::DeclarationName declName(&funcII);

    std::vector<clang::QualType> paramTypes = {intRefType};
    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(ctx.VoidTy, paramTypes, EPI);

    clang::FunctionDecl* cppFunc = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    cppFunc->setParams({cppParam});

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr) << "Result is not a FunctionDecl";

    EXPECT_EQ(cFunc->getNameAsString(), "func") << "Function name mismatch";
    EXPECT_TRUE(cFunc->getReturnType()->isVoidType()) << "Return type should be void";
    EXPECT_EQ(cFunc->getNumParams(), 1) << "Should have one parameter";

    // Check parameter type is pointer
    const auto* param = cFunc->getParamDecl(0);
    ASSERT_NE(param, nullptr);
    EXPECT_EQ(param->getNameAsString(), "x") << "Parameter name mismatch";
    EXPECT_TRUE(param->getType()->isPointerType()) << "Reference parameter should become pointer";

    // Verify pointee type is int
    clang::QualType pointeeType = param->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Pointee should be int";
    */
}

/**
 * Test 5: Function with const reference parameter
 *
 * C++ Input:  void func(const int& x);
 * C Output:   void func(const int* x);
 *
 * Tests const reference parameter transformation.
 */
TEST_F(FunctionHandlerTest, DISABLED_FunctionWithConstReferenceParameter) {
    GTEST_SKIP() << "Test needs refactoring to use dispatcher pattern with buildASTFromCode";
    /* Original test code - kept for reference during refactoring
    // Arrange: Create void func(const int& x)
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create parameter: const int& x
    clang::QualType constIntType = ctx.IntTy.withConst();
    clang::QualType constIntRefType = ctx.getLValueReferenceType(constIntType);
    clang::IdentifierInfo& paramII = ctx.Idents.get("x");

    clang::ParmVarDecl* cppParam = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &paramII,
        constIntRefType,
        ctx.getTrivialTypeSourceInfo(constIntRefType),
        clang::SC_None,
        nullptr
    );

    // Create function
    clang::IdentifierInfo& funcII = ctx.Idents.get("func");
    clang::DeclarationName declName(&funcII);

    std::vector<clang::QualType> paramTypes = {constIntRefType};
    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(ctx.VoidTy, paramTypes, EPI);

    clang::FunctionDecl* cppFunc = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    cppFunc->setParams({cppParam});

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNumParams(), 1);

    const auto* param = cFunc->getParamDecl(0);
    ASSERT_NE(param, nullptr);
    EXPECT_TRUE(param->getType()->isPointerType()) << "Reference parameter should become pointer";

    // Verify pointee is const int
    clang::QualType pointeeType = param->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified()) << "Pointee should be const";
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Pointee should be int";
    */
}

/**
 * Test 6: Function with multiple reference parameters
 *
 * C++ Input:  void swap(int& a, int& b);
 * C Output:   void swap(int* a, int* b);
 *
 * Tests multiple reference parameters.
 */
TEST_F(FunctionHandlerTest, DISABLED_FunctionWithMultipleReferenceParameters) {
    GTEST_SKIP() << "Test needs refactoring to use dispatcher pattern with buildASTFromCode";
    /* Original test code - kept for reference during refactoring
    // Arrange: Create void swap(int& a, int& b)
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create parameters
    clang::QualType intRefType = ctx.getLValueReferenceType(ctx.IntTy);

    clang::IdentifierInfo& aII = ctx.Idents.get("a");
    clang::ParmVarDecl* paramA = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &aII,
        intRefType,
        ctx.getTrivialTypeSourceInfo(intRefType),
        clang::SC_None,
        nullptr
    );

    clang::IdentifierInfo& bII = ctx.Idents.get("b");
    clang::ParmVarDecl* paramB = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &bII,
        intRefType,
        ctx.getTrivialTypeSourceInfo(intRefType),
        clang::SC_None,
        nullptr
    );

    // Create function
    clang::IdentifierInfo& funcII = ctx.Idents.get("swap");
    clang::DeclarationName declName(&funcII);

    std::vector<clang::QualType> paramTypes = {intRefType, intRefType};
    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(ctx.VoidTy, paramTypes, EPI);

    clang::FunctionDecl* cppFunc = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    cppFunc->setParams({paramA, paramB});

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "swap");
    EXPECT_EQ(cFunc->getNumParams(), 2) << "Should have two parameters";

    // Check first parameter
    const auto* param1 = cFunc->getParamDecl(0);
    ASSERT_NE(param1, nullptr);
    EXPECT_EQ(param1->getNameAsString(), "a");
    EXPECT_TRUE(param1->getType()->isPointerType()) << "First parameter should be pointer";

    // Check second parameter
    const auto* param2 = cFunc->getParamDecl(1);
    ASSERT_NE(param2, nullptr);
    EXPECT_EQ(param2->getNameAsString(), "b");
    EXPECT_TRUE(param2->getType()->isPointerType()) << "Second parameter should be pointer";
    */
}

/**
 * Test 7: Function with reference return type
 *
 * C++ Input:  int& getRef();
 * C Output:   int* getRef();
 *
 * Tests reference return type transformation.
 */
TEST_F(FunctionHandlerTest, DISABLED_FunctionWithReferenceReturnType) {
    GTEST_SKIP() << "Test needs refactoring to use dispatcher pattern with buildASTFromCode";
    /* Original test code - kept for reference during refactoring
    // Arrange: Create int& getRef()
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create return type: int&
    clang::QualType intRefType = ctx.getLValueReferenceType(ctx.IntTy);

    clang::IdentifierInfo& funcII = ctx.Idents.get("getRef");
    clang::DeclarationName declName(&funcII);

    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(intRefType, {}, EPI);

    clang::FunctionDecl* cppFunc = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "getRef");
    EXPECT_EQ(cFunc->getNumParams(), 0);
    EXPECT_TRUE(cFunc->getReturnType()->isPointerType()) << "Reference return should become pointer";

    // Verify return type pointee is int
    clang::QualType pointeeType = cFunc->getReturnType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Return pointee should be int";
    */
}

/**
 * Test 8: Function with mixed parameters (value and reference)
 *
 * C++ Input:  void process(int x, int& y, const int& z);
 * C Output:   void process(int x, int* y, const int* z);
 *
 * Tests mixed parameter types including references.
 */
TEST_F(FunctionHandlerTest, DISABLED_FunctionWithMixedParameters) {
    GTEST_SKIP() << "Test needs refactoring to use dispatcher pattern with buildASTFromCode";
    /* Original test code - kept for reference during refactoring
    // Arrange: Create void process(int x, int& y, const int& z)
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create parameters
    clang::IdentifierInfo& xII = ctx.Idents.get("x");
    clang::ParmVarDecl* paramX = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &xII,
        ctx.IntTy,
        ctx.getTrivialTypeSourceInfo(ctx.IntTy),
        clang::SC_None,
        nullptr
    );

    clang::QualType intRefType = ctx.getLValueReferenceType(ctx.IntTy);
    clang::IdentifierInfo& yII = ctx.Idents.get("y");
    clang::ParmVarDecl* paramY = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &yII,
        intRefType,
        ctx.getTrivialTypeSourceInfo(intRefType),
        clang::SC_None,
        nullptr
    );

    clang::QualType constIntType = ctx.IntTy.withConst();
    clang::QualType constIntRefType = ctx.getLValueReferenceType(constIntType);
    clang::IdentifierInfo& zII = ctx.Idents.get("z");
    clang::ParmVarDecl* paramZ = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &zII,
        constIntRefType,
        ctx.getTrivialTypeSourceInfo(constIntRefType),
        clang::SC_None,
        nullptr
    );

    // Create function
    clang::IdentifierInfo& funcII = ctx.Idents.get("process");
    clang::DeclarationName declName(&funcII);

    std::vector<clang::QualType> paramTypes = {ctx.IntTy, intRefType, constIntRefType};
    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(ctx.VoidTy, paramTypes, EPI);

    clang::FunctionDecl* cppFunc = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    cppFunc->setParams({paramX, paramY, paramZ});

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNumParams(), 3) << "Should have three parameters";

    // Check first parameter (value type)
    const auto* param1 = cFunc->getParamDecl(0);
    ASSERT_NE(param1, nullptr);
    EXPECT_EQ(param1->getNameAsString(), "x");
    EXPECT_TRUE(param1->getType()->isIntegerType()) << "Value parameter should remain as int";

    // Check second parameter (reference)
    const auto* param2 = cFunc->getParamDecl(1);
    ASSERT_NE(param2, nullptr);
    EXPECT_EQ(param2->getNameAsString(), "y");
    EXPECT_TRUE(param2->getType()->isPointerType()) << "Reference parameter should become pointer";

    // Check third parameter (const reference)
    const auto* param3 = cFunc->getParamDecl(2);
    ASSERT_NE(param3, nullptr);
    EXPECT_EQ(param3->getNameAsString(), "z");
    EXPECT_TRUE(param3->getType()->isPointerType()) << "Const reference should become pointer";
    EXPECT_TRUE(param3->getType()->getPointeeType().isConstQualified()) << "Pointee should be const";
    */
}

// ============================================================================
// Phase 43 Tests: Struct Parameters and Return Values (Task 6)
// ============================================================================

/**
 * Test 9: Function with struct parameter by value
 *
 * C++ Input:  void func(Point p);
 * C Output:   void func(struct Point p);
 *
 * Tests struct parameter translation with struct keyword insertion.
 */
TEST_F(FunctionHandlerTest, DISABLED_FunctionWithStructParameterByValue) {
    GTEST_SKIP() << "Test needs refactoring to use dispatcher pattern with buildASTFromCode";
    /* Original test code - kept for reference during refactoring
    // Arrange: First create a struct Point
    const char* structCode = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    auto structAST = clang::tooling::buildASTFromCode(structCode);
    ASSERT_NE(structAST, nullptr);

    clang::ASTContext& ctx = cppAST->getASTContext();

    // Get the RecordDecl for Point
    const clang::RecordDecl* pointRecord = nullptr;
    auto& structCtx = structAST->getASTContext();
    for (auto* decl : structCtx.getTranslationUnitDecl()->decls()) {
        if (auto* rd = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (rd->getNameAsString() == "Point") {
                pointRecord = rd;
                break;
            }
        }
    }
    ASSERT_NE(pointRecord, nullptr);

    // Create RecordType for Point
    clang::QualType pointType = ctx.getRecordType(pointRecord);

    // Create parameter with struct type
    clang::IdentifierInfo& paramII = ctx.Idents.get("p");
    clang::ParmVarDecl* cppParam = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &paramII,
        pointType,
        ctx.getTrivialTypeSourceInfo(pointType),
        clang::SC_None,
        nullptr
    );

    // Create function void func(Point p)
    clang::IdentifierInfo& funcII = ctx.Idents.get("func");
    clang::DeclarationName declName(&funcII);

    std::vector<clang::QualType> paramTypes = {pointType};
    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(ctx.VoidTy, paramTypes, EPI);

    clang::FunctionDecl* cppFunc = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    cppFunc->setParams({cppParam});

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "func");
    EXPECT_EQ(cFunc->getNumParams(), 1);

    const auto* param = cFunc->getParamDecl(0);
    ASSERT_NE(param, nullptr);
    EXPECT_EQ(param->getNameAsString(), "p");
    EXPECT_TRUE(param->getType()->isRecordType()) << "Parameter should have struct type";
    */
}

/**
 * Test 10: Function with struct parameter by pointer
 *
 * C++ Input:  void func(Point* p);
 * C Output:   void func(struct Point* p);
 *
 * Tests struct pointer parameter translation.
 */
TEST_F(FunctionHandlerTest, DISABLED_FunctionWithStructParameterByPointer) {
    GTEST_SKIP() << "Test needs refactoring to use dispatcher pattern with buildASTFromCode";
    /* Original test code - kept for reference during refactoring
    // Arrange: Create struct Point and function void func(Point* p)
    const char* structCode = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    auto structAST = clang::tooling::buildASTFromCode(structCode);
    ASSERT_NE(structAST, nullptr);

    clang::ASTContext& ctx = cppAST->getASTContext();

    // Get RecordDecl for Point
    const clang::RecordDecl* pointRecord = nullptr;
    auto& structCtx = structAST->getASTContext();
    for (auto* decl : structCtx.getTranslationUnitDecl()->decls()) {
        if (auto* rd = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (rd->getNameAsString() == "Point") {
                pointRecord = rd;
                break;
            }
        }
    }
    ASSERT_NE(pointRecord, nullptr);

    // Create RecordType for Point and then pointer to it
    clang::QualType pointType = ctx.getRecordType(pointRecord);
    clang::QualType pointPtrType = ctx.getPointerType(pointType);

    // Create parameter
    clang::IdentifierInfo& paramII = ctx.Idents.get("p");
    clang::ParmVarDecl* cppParam = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &paramII,
        pointPtrType,
        ctx.getTrivialTypeSourceInfo(pointPtrType),
        clang::SC_None,
        nullptr
    );

    // Create function
    clang::IdentifierInfo& funcII = ctx.Idents.get("func");
    clang::DeclarationName declName(&funcII);

    std::vector<clang::QualType> paramTypes = {pointPtrType};
    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(ctx.VoidTy, paramTypes, EPI);

    clang::FunctionDecl* cppFunc = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    cppFunc->setParams({cppParam});

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNumParams(), 1);

    const auto* param = cFunc->getParamDecl(0);
    ASSERT_NE(param, nullptr);
    EXPECT_TRUE(param->getType()->isPointerType()) << "Parameter should be pointer";
    EXPECT_TRUE(param->getType()->getPointeeType()->isRecordType()) << "Pointee should be struct";
    */
}

/**
 * Test 11: Function returning struct by value
 *
 * C++ Input:  Point createPoint();
 * C Output:   struct Point createPoint();
 *
 * Tests struct return type translation.
 */
TEST_F(FunctionHandlerTest, DISABLED_FunctionReturningStructByValue) {
    GTEST_SKIP() << "Test needs refactoring to use dispatcher pattern with buildASTFromCode";
    /* Original test code - kept for reference during refactoring
    // Arrange: Create struct Point and function Point createPoint()
    const char* structCode = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    auto structAST = clang::tooling::buildASTFromCode(structCode);
    ASSERT_NE(structAST, nullptr);

    clang::ASTContext& ctx = cppAST->getASTContext();

    // Get RecordDecl for Point
    const clang::RecordDecl* pointRecord = nullptr;
    auto& structCtx = structAST->getASTContext();
    for (auto* decl : structCtx.getTranslationUnitDecl()->decls()) {
        if (auto* rd = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (rd->getNameAsString() == "Point") {
                pointRecord = rd;
                break;
            }
        }
    }
    ASSERT_NE(pointRecord, nullptr);

    // Create RecordType for Point
    clang::QualType pointType = ctx.getRecordType(pointRecord);

    // Create function Point createPoint()
    clang::IdentifierInfo& funcII = ctx.Idents.get("createPoint");
    clang::DeclarationName declName(&funcII);

    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(pointType, {}, EPI);

    clang::FunctionDecl* cppFunc = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "createPoint");
    EXPECT_TRUE(cFunc->getReturnType()->isRecordType()) << "Return type should be struct";
    */
}

/**
 * Test 12: Function returning struct pointer
 *
 * C++ Input:  Point* getPointPtr();
 * C Output:   struct Point* getPointPtr();
 *
 * Tests struct pointer return type translation.
 */
TEST_F(FunctionHandlerTest, DISABLED_FunctionReturningStructPointer) {
    GTEST_SKIP() << "Test needs refactoring to use dispatcher pattern with buildASTFromCode";
    /* Original test code - kept for reference during refactoring
    // Arrange
    const char* structCode = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    auto structAST = clang::tooling::buildASTFromCode(structCode);
    ASSERT_NE(structAST, nullptr);

    clang::ASTContext& ctx = cppAST->getASTContext();

    // Get RecordDecl for Point
    const clang::RecordDecl* pointRecord = nullptr;
    auto& structCtx = structAST->getASTContext();
    for (auto* decl : structCtx.getTranslationUnitDecl()->decls()) {
        if (auto* rd = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (rd->getNameAsString() == "Point") {
                pointRecord = rd;
                break;
            }
        }
    }
    ASSERT_NE(pointRecord, nullptr);

    // Create pointer to struct
    clang::QualType pointType = ctx.getRecordType(pointRecord);
    clang::QualType pointPtrType = ctx.getPointerType(pointType);

    // Create function Point* getPointPtr()
    clang::IdentifierInfo& funcII = ctx.Idents.get("getPointPtr");
    clang::DeclarationName declName(&funcII);

    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(pointPtrType, {}, EPI);

    clang::FunctionDecl* cppFunc = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_TRUE(cFunc->getReturnType()->isPointerType()) << "Return type should be pointer";
    EXPECT_TRUE(cFunc->getReturnType()->getPointeeType()->isRecordType()) << "Pointee should be struct";
    */
}

/**
 * Test 13: Function with multiple struct parameters
 *
 * C++ Input:  void func(Point a, Point b, Point c);
 * C Output:   void func(struct Point a, struct Point b, struct Point c);
 *
 * Tests multiple struct parameters.
 */
TEST_F(FunctionHandlerTest, DISABLED_FunctionWithMultipleStructParameters) {
    GTEST_SKIP() << "Test needs refactoring to use dispatcher pattern with buildASTFromCode";
    /* Original test code - kept for reference during refactoring
    // Arrange
    const char* structCode = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    auto structAST = clang::tooling::buildASTFromCode(structCode);
    ASSERT_NE(structAST, nullptr);

    clang::ASTContext& ctx = cppAST->getASTContext();

    // Get RecordDecl for Point
    const clang::RecordDecl* pointRecord = nullptr;
    auto& structCtx = structAST->getASTContext();
    for (auto* decl : structCtx.getTranslationUnitDecl()->decls()) {
        if (auto* rd = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (rd->getNameAsString() == "Point") {
                pointRecord = rd;
                break;
            }
        }
    }
    ASSERT_NE(pointRecord, nullptr);

    clang::QualType pointType = ctx.getRecordType(pointRecord);

    // Create three parameters
    clang::IdentifierInfo& aII = ctx.Idents.get("a");
    clang::ParmVarDecl* paramA = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &aII,
        pointType,
        ctx.getTrivialTypeSourceInfo(pointType),
        clang::SC_None,
        nullptr
    );

    clang::IdentifierInfo& bII = ctx.Idents.get("b");
    clang::ParmVarDecl* paramB = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &bII,
        pointType,
        ctx.getTrivialTypeSourceInfo(pointType),
        clang::SC_None,
        nullptr
    );

    clang::IdentifierInfo& cII = ctx.Idents.get("c");
    clang::ParmVarDecl* paramC = clang::ParmVarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &cII,
        pointType,
        ctx.getTrivialTypeSourceInfo(pointType),
        clang::SC_None,
        nullptr
    );

    // Create function
    clang::IdentifierInfo& funcII = ctx.Idents.get("func");
    clang::DeclarationName declName(&funcII);

    std::vector<clang::QualType> paramTypes = {pointType, pointType, pointType};
    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(ctx.VoidTy, paramTypes, EPI);

    clang::FunctionDecl* cppFunc = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    cppFunc->setParams({paramA, paramB, paramC});

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNumParams(), 3) << "Should have three parameters";

    // Verify all three parameters are struct types
    for (unsigned i = 0; i < 3; ++i) {
        const auto* param = cFunc->getParamDecl(i);
        ASSERT_NE(param, nullptr);
        EXPECT_TRUE(param->getType()->isRecordType()) << "Parameter " << i << " should be struct type";
    }
    */
}

// TODO: Add more tests following TDD cycles
// NOTE: Tests 4-13 are currently DISABLED because they use the old handler API pattern
// They need to be refactored to use the dispatcher pattern as shown in tests 1-3
// See FunctionHandlerDispatcherTest.cpp for working examples of the correct pattern

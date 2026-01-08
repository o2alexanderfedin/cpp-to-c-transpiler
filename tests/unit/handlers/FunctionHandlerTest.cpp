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
TEST_F(FunctionHandlerTest, FunctionWithLValueReferenceParameter) {
    // Arrange
    const char* cpp = "void func(int& x);";
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
            if (FD->getNameAsString() == "func") {
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
            if (FD->getNameAsString() == "func") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr) << "Translation returned null";
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
}

/**
 * Test 5: Function with const reference parameter
 *
 * C++ Input:  void func(const int& x);
 * C Output:   void func(const int* x);
 *
 * Tests const reference parameter transformation.
 */
TEST_F(FunctionHandlerTest, FunctionWithConstReferenceParameter) {
    // Arrange
    const char* cpp = "void func(const int& x);";
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
            if (FD->getNameAsString() == "func") {
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
            if (FD->getNameAsString() == "func") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 1);

    const auto* param = cFunc->getParamDecl(0);
    ASSERT_NE(param, nullptr);
    EXPECT_TRUE(param->getType()->isPointerType()) << "Reference parameter should become pointer";

    // Verify pointee is const int
    clang::QualType pointeeType = param->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified()) << "Pointee should be const";
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Pointee should be int";
}

/**
 * Test 6: Function with multiple reference parameters
 *
 * C++ Input:  void swap(int& a, int& b);
 * C Output:   void swap(int* a, int* b);
 *
 * Tests multiple reference parameters.
 */
TEST_F(FunctionHandlerTest, FunctionWithMultipleReferenceParameters) {
    // Arrange
    const char* cpp = "void swap(int& a, int& b);";
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
            if (FD->getNameAsString() == "swap") {
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
            if (FD->getNameAsString() == "swap") {
                cFunc = FD;
                break;
            }
        }
    }

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
}

/**
 * Test 7: Function with reference return type
 *
 * C++ Input:  int& getRef();
 * C Output:   int* getRef();
 *
 * Tests reference return type transformation.
 */
TEST_F(FunctionHandlerTest, FunctionWithReferenceReturnType) {
    // Arrange
    const char* cpp = "int& getRef();";
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
            if (FD->getNameAsString() == "getRef") {
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
            if (FD->getNameAsString() == "getRef") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "getRef");
    EXPECT_EQ(cFunc->getNumParams(), 0);
    EXPECT_TRUE(cFunc->getReturnType()->isPointerType()) << "Reference return should become pointer";

    // Verify return type pointee is int
    clang::QualType pointeeType = cFunc->getReturnType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Return pointee should be int";
}

/**
 * Test 8: Function with mixed parameters (value and reference)
 *
 * C++ Input:  void process(int x, int& y, const int& z);
 * C Output:   void process(int x, int* y, const int* z);
 *
 * Tests mixed parameter types including references.
 */
TEST_F(FunctionHandlerTest, FunctionWithMixedParameters) {
    // Arrange
    const char* cpp = "void process(int x, int& y, const int& z);";
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
            if (FD->getNameAsString() == "process") {
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
            if (FD->getNameAsString() == "process") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "process");
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
TEST_F(FunctionHandlerTest, FunctionWithStructParameterByValue) {
    // Arrange
    const char* cpp = R"(
        struct Point {
            int x;
            int y;
        };
        void func(Point p);
    )";
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
            if (FD->getNameAsString() == "func") {
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
            if (FD->getNameAsString() == "func") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "func");
    EXPECT_EQ(cFunc->getNumParams(), 1);

    const auto* param = cFunc->getParamDecl(0);
    ASSERT_NE(param, nullptr);
    EXPECT_EQ(param->getNameAsString(), "p");
    EXPECT_TRUE(param->getType()->isRecordType()) << "Parameter should have struct type";
}

/**
 * Test 10: Function with struct parameter by pointer
 *
 * C++ Input:  void func(Point* p);
 * C Output:   void func(struct Point* p);
 *
 * Tests struct pointer parameter translation.
 */
TEST_F(FunctionHandlerTest, FunctionWithStructParameterByPointer) {
    // Arrange
    const char* cpp = R"(
        struct Point {
            int x;
            int y;
        };
        void func(Point* p);
    )";
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
            if (FD->getNameAsString() == "func") {
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
            if (FD->getNameAsString() == "func") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 1);

    const auto* param = cFunc->getParamDecl(0);
    ASSERT_NE(param, nullptr);
    EXPECT_TRUE(param->getType()->isPointerType()) << "Parameter should be pointer";
    EXPECT_TRUE(param->getType()->getPointeeType()->isRecordType()) << "Pointee should be struct";
}

/**
 * Test 11: Function returning struct by value
 *
 * C++ Input:  Point createPoint();
 * C Output:   struct Point createPoint();
 *
 * Tests struct return type translation.
 */
TEST_F(FunctionHandlerTest, FunctionReturningStructByValue) {
    // Arrange
    const char* cpp = R"(
        struct Point {
            int x;
            int y;
        };
        Point createPoint();
    )";
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
            if (FD->getNameAsString() == "createPoint") {
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
            if (FD->getNameAsString() == "createPoint") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "createPoint");
    EXPECT_TRUE(cFunc->getReturnType()->isRecordType()) << "Return type should be struct";
}

/**
 * Test 12: Function returning struct pointer
 *
 * C++ Input:  Point* getPointPtr();
 * C Output:   struct Point* getPointPtr();
 *
 * Tests struct pointer return type translation.
 */
TEST_F(FunctionHandlerTest, FunctionReturningStructPointer) {
    // Arrange
    const char* cpp = R"(
        struct Point {
            int x;
            int y;
        };
        Point* getPointPtr();
    )";
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
            if (FD->getNameAsString() == "getPointPtr") {
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
            if (FD->getNameAsString() == "getPointPtr") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr);
    EXPECT_TRUE(cFunc->getReturnType()->isPointerType()) << "Return type should be pointer";
    EXPECT_TRUE(cFunc->getReturnType()->getPointeeType()->isRecordType()) << "Pointee should be struct";
}

/**
 * Test 13: Function with multiple struct parameters
 *
 * C++ Input:  void func(Point a, Point b, Point c);
 * C Output:   void func(struct Point a, struct Point b, struct Point c);
 *
 * Tests multiple struct parameters.
 */
TEST_F(FunctionHandlerTest, FunctionWithMultipleStructParameters) {
    // Arrange
    const char* cpp = R"(
        struct Point {
            int x;
            int y;
        };
        void func(Point a, Point b, Point c);
    )";
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
            if (FD->getNameAsString() == "func") {
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
            if (FD->getNameAsString() == "func") {
                cFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 3) << "Should have three parameters";

    // Verify all three parameters are struct types
    for (unsigned i = 0; i < 3; ++i) {
        const auto* param = cFunc->getParamDecl(i);
        ASSERT_NE(param, nullptr);
        EXPECT_TRUE(param->getType()->isRecordType()) << "Parameter " << i << " should be struct type";
    }
}

// TODO: Add more tests following TDD cycles
// All tests now use the dispatcher pattern with buildASTFromCode

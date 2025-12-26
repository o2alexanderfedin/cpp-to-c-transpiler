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

#include "handlers/FunctionHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class FunctionHandlerTest
 * @brief Test fixture for FunctionHandler
 *
 * Uses clang::tooling::buildASTFromCode for real AST contexts.
 */
class FunctionHandlerTest : public ::testing::Test {
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
     * @brief Create a C++ function declaration programmatically
     */
    clang::FunctionDecl* createCppFunction(
        const std::string& returnType,
        const std::string& name,
        const std::vector<std::string>& params = {}
    ) {
        clang::ASTContext& ctx = cppAST->getASTContext();

        // Parse return type
        clang::QualType retType;
        if (returnType == "void") {
            retType = ctx.VoidTy;
        } else if (returnType == "int") {
            retType = ctx.IntTy;
        } else if (returnType == "float") {
            retType = ctx.FloatTy;
        } else {
            retType = ctx.IntTy; // default
        }

        // Create function declaration
        clang::IdentifierInfo& II = ctx.Idents.get(name);
        clang::DeclarationName declName(&II);

        // Create function type
        clang::FunctionProtoType::ExtProtoInfo EPI;
        clang::QualType funcType = ctx.getFunctionType(retType, {}, EPI);

        clang::FunctionDecl* func = clang::FunctionDecl::Create(
            ctx,
            ctx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            declName,
            funcType,
            ctx.getTrivialTypeSourceInfo(funcType),
            clang::SC_None
        );

        return func;
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
    // Arrange: Create C++ empty function
    clang::FunctionDecl* cppFunc = createCppFunction("void", "foo");
    ASSERT_NE(cppFunc, nullptr);

    // Act: Translate using FunctionHandler
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert: Verify C function created
    ASSERT_NE(result, nullptr) << "Translation returned null";

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr) << "Result is not a FunctionDecl";

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
    clang::FunctionDecl* cppFunc = createCppFunction("int", "bar");
    ASSERT_NE(cppFunc, nullptr);

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
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
    clang::FunctionDecl* cppFunc = createCppFunction("float", "getValue");
    ASSERT_NE(cppFunc, nullptr);

    // Act
    FunctionHandler handler;
    clang::Decl* result = handler.handleDecl(cppFunc, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "getValue");
    EXPECT_EQ(cFunc->getNumParams(), 0);
    EXPECT_TRUE(cFunc->getReturnType()->isFloatingType());
}

// ============================================================================
// Phase 42 Tests: Reference Parameters (Task 2)
// ============================================================================

/**
 * Test 4: Function with lvalue reference parameter
 *
 * C++ Input:  void func(int& x);
 * C Output:   void func(int* x);
 *
 * Tests reference parameter transformation to pointer parameter.
 */
TEST_F(FunctionHandlerTest, FunctionWithLValueReferenceParameter) {
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
}

// TODO: Add more tests following TDD cycles

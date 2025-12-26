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

// TODO: Add tests 4-20+ following TDD cycles

/**
 * @file VariableHandlerTest.cpp
 * @brief TDD tests for VariableHandler
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (15+ tests):
 * 1. LocalVariableNoInit - int x;
 * 2. LocalVariableWithIntInit - int x = 5;
 * 3. LocalVariableWithFloatInit - float y = 3.14;
 * 4. LocalVariableUsedInExpr - Variable used in arithmetic
 * 5. MultipleLocalVariables - Multiple vars in same scope
 * 6. VariableReassignment - x = 10;
 * 7. VariableWithComplexInit - int z = x + y;
 * 8. ConstVariable - const int c = 5;
 * 9. VariableShadowing - Inner scope shadowing outer
 * 10. VariableInCompoundStmt - Vars in {} blocks
 * 11. PointerVariable - int* ptr;
 * 12. PointerWithNullInit - int* ptr = nullptr;
 * 13. CharVariable - char c = 'A';
 * 14. StaticVariable - static int counter = 0;
 * 15. ExternVariable - extern int globalVar;
 * ... (additional edge cases)
 */

#include "handlers/VariableHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class VariableHandlerTest
 * @brief Test fixture for VariableHandler
 *
 * Uses clang::tooling::buildASTFromCode for real AST contexts.
 */
class VariableHandlerTest : public ::testing::Test {
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
     * @brief Create a C++ variable declaration programmatically
     */
    clang::VarDecl* createCppVariable(
        const std::string& type,
        const std::string& name,
        clang::Expr* init = nullptr,
        clang::StorageClass sc = clang::SC_None
    ) {
        clang::ASTContext& ctx = cppAST->getASTContext();

        // Parse type
        clang::QualType varType;
        if (type == "int") {
            varType = ctx.IntTy;
        } else if (type == "float") {
            varType = ctx.FloatTy;
        } else if (type == "char") {
            varType = ctx.CharTy;
        } else if (type == "int*") {
            varType = ctx.getPointerType(ctx.IntTy);
        } else if (type == "const int") {
            varType = ctx.IntTy.withConst();
        } else {
            varType = ctx.IntTy; // default
        }

        // Create variable declaration
        clang::IdentifierInfo& II = ctx.Idents.get(name);

        clang::VarDecl* var = clang::VarDecl::Create(
            ctx,
            ctx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II,
            varType,
            ctx.getTrivialTypeSourceInfo(varType),
            sc
        );

        if (init) {
            var->setInit(init);
        }

        return var;
    }

    /**
     * @brief Create integer literal
     */
    clang::IntegerLiteral* createIntLiteral(int value) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::IntegerLiteral::Create(
            ctx,
            llvm::APInt(32, value),
            ctx.IntTy,
            clang::SourceLocation()
        );
    }

    /**
     * @brief Create floating literal
     */
    clang::FloatingLiteral* createFloatLiteral(float value) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        llvm::APFloat apf(value);
        return clang::FloatingLiteral::Create(
            ctx,
            apf,
            false, // isExact
            ctx.FloatTy,
            clang::SourceLocation()
        );
    }

    /**
     * @brief Create character literal
     */
    clang::CharacterLiteral* createCharLiteral(char value) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return new (ctx) clang::CharacterLiteral(
            value,
            clang::CharacterLiteralKind::Ascii,
            ctx.CharTy,
            clang::SourceLocation()
        );
    }
};

// ============================================================================
// TDD Test 1: Local Variable No Init
// ============================================================================

/**
 * Test 1: Translate local variable without initializer
 *
 * C++ Input:  int x;
 * C Output:   int x;
 *
 * This is the simplest possible variable - no initializer, basic type.
 */
TEST_F(VariableHandlerTest, LocalVariableNoInit) {
    // Arrange: Create C++ variable without init
    clang::VarDecl* cppVar = createCppVariable("int", "x");
    ASSERT_NE(cppVar, nullptr);

    // Act: Translate using VariableHandler
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert: Verify C variable created
    ASSERT_NE(result, nullptr) << "Translation returned null";

    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr) << "Result is not a VarDecl";

    EXPECT_EQ(cVar->getNameAsString(), "x") << "Variable name mismatch";
    EXPECT_TRUE(cVar->getType()->isIntegerType()) << "Type should be int";
    EXPECT_FALSE(cVar->hasInit()) << "Should have no initializer";
}

/**
 * Test 2: Local variable with int initializer
 *
 * C++ Input:  int x = 5;
 * C Output:   int x = 5;
 */
TEST_F(VariableHandlerTest, LocalVariableWithIntInit) {
    // Arrange
    clang::IntegerLiteral* initExpr = createIntLiteral(5);
    clang::VarDecl* cppVar = createCppVariable("int", "x", initExpr);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "x");
    EXPECT_TRUE(cVar->getType()->isIntegerType());
    EXPECT_TRUE(cVar->hasInit()) << "Should have initializer";

    // Check initializer value
    auto* initLit = llvm::dyn_cast<clang::IntegerLiteral>(cVar->getInit());
    ASSERT_NE(initLit, nullptr) << "Initializer should be IntegerLiteral";
    EXPECT_EQ(initLit->getValue().getSExtValue(), 5) << "Initializer value mismatch";
}

/**
 * Test 3: Local variable with float initializer
 *
 * C++ Input:  float y = 3.14;
 * C Output:   float y = 3.14;
 */
TEST_F(VariableHandlerTest, LocalVariableWithFloatInit) {
    // Arrange
    clang::FloatingLiteral* initExpr = createFloatLiteral(3.14f);
    clang::VarDecl* cppVar = createCppVariable("float", "y", initExpr);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "y");
    EXPECT_TRUE(cVar->getType()->isFloatingType());
    EXPECT_TRUE(cVar->hasInit());

    auto* initLit = llvm::dyn_cast<clang::FloatingLiteral>(cVar->getInit());
    ASSERT_NE(initLit, nullptr);
    EXPECT_NEAR(initLit->getValue().convertToFloat(), 3.14f, 0.01f);
}

/**
 * Test 4: Char variable with initializer
 *
 * C++ Input:  char c = 'A';
 * C Output:   char c = 'A';
 */
TEST_F(VariableHandlerTest, CharVariableWithInit) {
    // Arrange
    clang::CharacterLiteral* initExpr = createCharLiteral('A');
    clang::VarDecl* cppVar = createCppVariable("char", "c", initExpr);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "c");
    EXPECT_TRUE(cVar->getType()->isCharType());
    EXPECT_TRUE(cVar->hasInit());
}

/**
 * Test 5: Pointer variable without init
 *
 * C++ Input:  int* ptr;
 * C Output:   int* ptr;
 */
TEST_F(VariableHandlerTest, PointerVariableNoInit) {
    // Arrange
    clang::VarDecl* cppVar = createCppVariable("int*", "ptr");
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ptr");
    EXPECT_TRUE(cVar->getType()->isPointerType());
    EXPECT_FALSE(cVar->hasInit());
}

/**
 * Test 6: Const variable
 *
 * C++ Input:  const int c = 5;
 * C Output:   const int c = 5;
 */
TEST_F(VariableHandlerTest, ConstVariable) {
    // Arrange
    clang::IntegerLiteral* initExpr = createIntLiteral(5);
    clang::VarDecl* cppVar = createCppVariable("const int", "c", initExpr);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "c");
    EXPECT_TRUE(cVar->getType().isConstQualified()) << "Should preserve const qualifier";
    EXPECT_TRUE(cVar->hasInit());
}

/**
 * Test 7: Static variable
 *
 * C++ Input:  static int counter = 0;
 * C Output:   static int counter = 0;
 */
TEST_F(VariableHandlerTest, StaticVariable) {
    // Arrange
    clang::IntegerLiteral* initExpr = createIntLiteral(0);
    clang::VarDecl* cppVar = createCppVariable("int", "counter", initExpr, clang::SC_Static);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "counter");
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static) << "Storage class should be static";
    EXPECT_TRUE(cVar->hasInit());
}

/**
 * Test 8: Extern variable
 *
 * C++ Input:  extern int globalVar;
 * C Output:   extern int globalVar;
 */
TEST_F(VariableHandlerTest, ExternVariable) {
    // Arrange
    clang::VarDecl* cppVar = createCppVariable("int", "globalVar", nullptr, clang::SC_Extern);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "globalVar");
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Extern);
    EXPECT_FALSE(cVar->hasInit()) << "Extern variable should not have initializer";
}

/**
 * Test 9: Variable name with underscores
 *
 * C++ Input:  int my_var_name = 10;
 * C Output:   int my_var_name = 10;
 */
TEST_F(VariableHandlerTest, VariableNameWithUnderscores) {
    // Arrange
    clang::IntegerLiteral* initExpr = createIntLiteral(10);
    clang::VarDecl* cppVar = createCppVariable("int", "my_var_name", initExpr);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "my_var_name");
}

/**
 * Test 10: Variable with zero init
 *
 * C++ Input:  int zero = 0;
 * C Output:   int zero = 0;
 */
TEST_F(VariableHandlerTest, VariableWithZeroInit) {
    // Arrange
    clang::IntegerLiteral* initExpr = createIntLiteral(0);
    clang::VarDecl* cppVar = createCppVariable("int", "zero", initExpr);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->hasInit());
    auto* initLit = llvm::dyn_cast<clang::IntegerLiteral>(cVar->getInit());
    ASSERT_NE(initLit, nullptr);
    EXPECT_EQ(initLit->getValue().getSExtValue(), 0);
}

/**
 * Test 11: Variable with negative init
 *
 * C++ Input:  int negative = -10;
 * C Output:   int negative = -10;
 */
TEST_F(VariableHandlerTest, VariableWithNegativeInit) {
    // Arrange
    clang::IntegerLiteral* initExpr = createIntLiteral(-10);
    clang::VarDecl* cppVar = createCppVariable("int", "negative", initExpr);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->hasInit());
}

/**
 * Test 12: Handler can identify VarDecl
 *
 * Tests the canHandle method
 */
TEST_F(VariableHandlerTest, CanHandleVarDecl) {
    // Arrange
    clang::VarDecl* cppVar = createCppVariable("int", "test");
    VariableHandler handler;

    // Act & Assert
    EXPECT_TRUE(handler.canHandle(cppVar)) << "Handler should be able to handle VarDecl";
}

/**
 * Test 13: Handler cannot identify non-VarDecl
 *
 * Tests that handler rejects non-variable declarations
 */
TEST_F(VariableHandlerTest, CannotHandleNonVarDecl) {
    // Arrange: Create a function declaration instead of variable
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::IdentifierInfo& II = ctx.Idents.get("foo");
    clang::DeclarationName declName(&II);

    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(ctx.VoidTy, {}, EPI);

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

    VariableHandler handler;

    // Act & Assert
    EXPECT_FALSE(handler.canHandle(func)) << "Handler should not handle FunctionDecl";
}

/**
 * Test 14: Multiple variables with same type
 *
 * Ensures each variable is translated independently
 */
TEST_F(VariableHandlerTest, MultipleVariablesSameType) {
    // Arrange
    clang::VarDecl* var1 = createCppVariable("int", "a", createIntLiteral(1));
    clang::VarDecl* var2 = createCppVariable("int", "b", createIntLiteral(2));
    clang::VarDecl* var3 = createCppVariable("int", "c", createIntLiteral(3));

    VariableHandler handler;

    // Act
    clang::Decl* result1 = handler.handleDecl(var1, *context);
    clang::Decl* result2 = handler.handleDecl(var2, *context);
    clang::Decl* result3 = handler.handleDecl(var3, *context);

    // Assert
    ASSERT_NE(result1, nullptr);
    ASSERT_NE(result2, nullptr);
    ASSERT_NE(result3, nullptr);

    auto* cVar1 = llvm::dyn_cast<clang::VarDecl>(result1);
    auto* cVar2 = llvm::dyn_cast<clang::VarDecl>(result2);
    auto* cVar3 = llvm::dyn_cast<clang::VarDecl>(result3);

    EXPECT_EQ(cVar1->getNameAsString(), "a");
    EXPECT_EQ(cVar2->getNameAsString(), "b");
    EXPECT_EQ(cVar3->getNameAsString(), "c");
}

/**
 * Test 15: Variable registration in context
 *
 * Ensures translated variables are registered in context
 */
TEST_F(VariableHandlerTest, VariableRegisteredInContext) {
    // Arrange
    clang::VarDecl* cppVar = createCppVariable("int", "x", createIntLiteral(42));
    VariableHandler handler;

    // Act
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);

    // Verify it was registered in context
    clang::Decl* lookedUp = context->lookupDecl(cppVar);
    EXPECT_EQ(lookedUp, result) << "Variable should be registered in context";
}

/**
 * Test 16: Long variable name
 *
 * C++ Input:  int very_long_variable_name_with_many_words = 123;
 * C Output:   int very_long_variable_name_with_many_words = 123;
 */
TEST_F(VariableHandlerTest, LongVariableName) {
    // Arrange
    std::string longName = "very_long_variable_name_with_many_words";
    clang::IntegerLiteral* initExpr = createIntLiteral(123);
    clang::VarDecl* cppVar = createCppVariable("int", longName, initExpr);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), longName);
}

/**
 * Test 17: Float with negative init
 *
 * C++ Input:  float negative = -2.5;
 * C Output:   float negative = -2.5;
 */
TEST_F(VariableHandlerTest, FloatVariableNegative) {
    // Arrange
    clang::FloatingLiteral* initExpr = createFloatLiteral(-2.5f);
    clang::VarDecl* cppVar = createCppVariable("float", "negative", initExpr);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "negative");
    EXPECT_TRUE(cVar->getType()->isFloatingType());
}

// TODO: Additional tests for Phase 2+:
// - Test 18: Reference variable (int& ref = x) → int* ref = &x
// - Test 19: Reference parameter translation
// - Test 20: Array variables
// - Test 21: Complex initialization expressions
// - Test 22: Variable with cast expression init

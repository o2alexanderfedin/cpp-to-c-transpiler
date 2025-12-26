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

// ============================================================================
// Phase 3 Tests: Array Declarations (Task 3)
// ============================================================================

/**
 * Test 18: Simple array declaration
 *
 * C++ Input:  int arr[10];
 * C Output:   int arr[10];
 */
TEST_F(VariableHandlerTest, SimpleArrayDeclaration) {
    // Arrange: Create int arr[10]
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create array type: int[10]
    llvm::APInt arraySize(32, 10);
    clang::QualType elementType = ctx.IntTy;
    clang::QualType arrayType = ctx.getConstantArrayType(
        elementType,
        arraySize,
        nullptr, // size expression
        clang::ArraySizeModifier::Normal,
        0 // index type qualifiers
    );

    clang::IdentifierInfo& II = ctx.Idents.get("arr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr) << "Result is not a VarDecl";

    EXPECT_EQ(cVar->getNameAsString(), "arr") << "Variable name mismatch";
    EXPECT_TRUE(cVar->getType()->isArrayType()) << "Type should be array";

    // Check array element type and size
    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr) << "Should be ConstantArrayType";
    EXPECT_TRUE(cArrayType->getElementType()->isIntegerType()) << "Element type should be int";
    EXPECT_EQ(cArrayType->getSize().getZExtValue(), 10) << "Array size should be 10";
}

/**
 * Test 19: Array with size expression
 *
 * C++ Input:  int arr[5+5];
 * C Output:   int arr[10];
 *
 * Note: Clang evaluates constant expressions at compile time,
 * so [5+5] becomes [10] in the AST.
 */
TEST_F(VariableHandlerTest, ArrayWithSizeExpression) {
    // Arrange: Create int arr[10] (represents arr[5+5] after constant evaluation)
    clang::ASTContext& ctx = cppAST->getASTContext();

    llvm::APInt arraySize(32, 10); // 5+5 = 10
    clang::QualType elementType = ctx.IntTy;
    clang::QualType arrayType = ctx.getConstantArrayType(
        elementType,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("arr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->getType()->isArrayType());
    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr);
    EXPECT_EQ(cArrayType->getSize().getZExtValue(), 10);
}

/**
 * Test 20: Multi-dimensional array (2D)
 *
 * C++ Input:  int matrix[3][4];
 * C Output:   int matrix[3][4];
 */
TEST_F(VariableHandlerTest, MultiDimensionalArray2D) {
    // Arrange: Create int matrix[3][4]
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Build from inner to outer: int -> int[4] -> int[3][4]
    llvm::APInt innerSize(32, 4);
    clang::QualType innerArrayType = ctx.getConstantArrayType(
        ctx.IntTy,
        innerSize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    llvm::APInt outerSize(32, 3);
    clang::QualType outerArrayType = ctx.getConstantArrayType(
        innerArrayType,
        outerSize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("matrix");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        outerArrayType,
        ctx.getTrivialTypeSourceInfo(outerArrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "matrix");
    EXPECT_TRUE(cVar->getType()->isArrayType());

    // Check outer dimension
    const auto* outerArray = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(outerArray, nullptr);
    EXPECT_EQ(outerArray->getSize().getZExtValue(), 3);

    // Check inner dimension
    const auto* innerArray = llvm::dyn_cast<clang::ConstantArrayType>(
        outerArray->getElementType().getTypePtr()
    );
    ASSERT_NE(innerArray, nullptr);
    EXPECT_EQ(innerArray->getSize().getZExtValue(), 4);
    EXPECT_TRUE(innerArray->getElementType()->isIntegerType());
}

/**
 * Test 21: Multi-dimensional array (3D)
 *
 * C++ Input:  int cube[2][3][4];
 * C Output:   int cube[2][3][4];
 */
TEST_F(VariableHandlerTest, MultiDimensionalArray3D) {
    // Arrange: Create int cube[2][3][4]
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Build from inner to outer: int -> int[4] -> int[3][4] -> int[2][3][4]
    llvm::APInt size4(32, 4);
    clang::QualType array4 = ctx.getConstantArrayType(
        ctx.IntTy,
        size4,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    llvm::APInt size3(32, 3);
    clang::QualType array3x4 = ctx.getConstantArrayType(
        array4,
        size3,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    llvm::APInt size2(32, 2);
    clang::QualType array2x3x4 = ctx.getConstantArrayType(
        array3x4,
        size2,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("cube");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        array2x3x4,
        ctx.getTrivialTypeSourceInfo(array2x3x4),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->getType()->isArrayType());

    // Verify dimensions: 2x3x4
    const auto* dim1 = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(dim1, nullptr);
    EXPECT_EQ(dim1->getSize().getZExtValue(), 2);

    const auto* dim2 = llvm::dyn_cast<clang::ConstantArrayType>(dim1->getElementType().getTypePtr());
    ASSERT_NE(dim2, nullptr);
    EXPECT_EQ(dim2->getSize().getZExtValue(), 3);

    const auto* dim3 = llvm::dyn_cast<clang::ConstantArrayType>(dim2->getElementType().getTypePtr());
    ASSERT_NE(dim3, nullptr);
    EXPECT_EQ(dim3->getSize().getZExtValue(), 4);
    EXPECT_TRUE(dim3->getElementType()->isIntegerType());
}

/**
 * Test 22: Const array
 *
 * C++ Input:  const int arr[5];
 * C Output:   const int arr[5];
 */
TEST_F(VariableHandlerTest, ConstArray) {
    // Arrange: Create const int arr[5]
    clang::ASTContext& ctx = cppAST->getASTContext();

    llvm::APInt arraySize(32, 5);
    clang::QualType elementType = ctx.IntTy.withConst();
    clang::QualType arrayType = ctx.getConstantArrayType(
        elementType,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("arr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->getType()->isArrayType());
    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr);
    EXPECT_TRUE(cArrayType->getElementType().isConstQualified()) << "Element type should be const";
}

/**
 * Test 23: Static array
 *
 * C++ Input:  static int arr[8];
 * C Output:   static int arr[8];
 */
TEST_F(VariableHandlerTest, StaticArray) {
    // Arrange: Create static int arr[8]
    clang::ASTContext& ctx = cppAST->getASTContext();

    llvm::APInt arraySize(32, 8);
    clang::QualType arrayType = ctx.getConstantArrayType(
        ctx.IntTy,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("arr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_Static
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->getType()->isArrayType());
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static);
}

/**
 * Test 24: Array of pointers
 *
 * C++ Input:  int* arr[5];
 * C Output:   int* arr[5];
 */
TEST_F(VariableHandlerTest, ArrayOfPointers) {
    // Arrange: Create int* arr[5]
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Element type is int*
    clang::QualType pointerType = ctx.getPointerType(ctx.IntTy);

    llvm::APInt arraySize(32, 5);
    clang::QualType arrayType = ctx.getConstantArrayType(
        pointerType,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("arr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->getType()->isArrayType());
    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr);
    EXPECT_TRUE(cArrayType->getElementType()->isPointerType()) << "Element type should be pointer";
}

/**
 * Test 25: Float array
 *
 * C++ Input:  float values[100];
 * C Output:   float values[100];
 */
TEST_F(VariableHandlerTest, FloatArray) {
    // Arrange: Create float values[100]
    clang::ASTContext& ctx = cppAST->getASTContext();

    llvm::APInt arraySize(32, 100);
    clang::QualType arrayType = ctx.getConstantArrayType(
        ctx.FloatTy,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("values");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->getType()->isArrayType());
    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr);
    EXPECT_TRUE(cArrayType->getElementType()->isFloatingType());
    EXPECT_EQ(cArrayType->getSize().getZExtValue(), 100);
}

/**
 * Test 26: Char array (string buffer)
 *
 * C++ Input:  char buffer[256];
 * C Output:   char buffer[256];
 */
TEST_F(VariableHandlerTest, CharArray) {
    // Arrange: Create char buffer[256]
    clang::ASTContext& ctx = cppAST->getASTContext();

    llvm::APInt arraySize(32, 256);
    clang::QualType arrayType = ctx.getConstantArrayType(
        ctx.CharTy,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("buffer");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->getType()->isArrayType());
    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr);
    EXPECT_TRUE(cArrayType->getElementType()->isCharType());
    EXPECT_EQ(cArrayType->getSize().getZExtValue(), 256);
}

/**
 * Test 27: Small array (size 1)
 *
 * C++ Input:  int single[1];
 * C Output:   int single[1];
 */
TEST_F(VariableHandlerTest, ArraySizeOne) {
    // Arrange: Create int single[1]
    clang::ASTContext& ctx = cppAST->getASTContext();

    llvm::APInt arraySize(32, 1);
    clang::QualType arrayType = ctx.getConstantArrayType(
        ctx.IntTy,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("single");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->getType()->isArrayType());
    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr);
    EXPECT_EQ(cArrayType->getSize().getZExtValue(), 1);
}

/**
 * Test 28: Array of const pointers
 *
 * C++ Input:  const int* arr[3];
 * C Output:   const int* arr[3];
 */
TEST_F(VariableHandlerTest, ArrayOfConstPointers) {
    // Arrange: Create const int* arr[3]
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Element type is const int*
    clang::QualType constIntType = ctx.IntTy.withConst();
    clang::QualType pointerType = ctx.getPointerType(constIntType);

    llvm::APInt arraySize(32, 3);
    clang::QualType arrayType = ctx.getConstantArrayType(
        pointerType,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("arr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->getType()->isArrayType());
    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr);
    EXPECT_TRUE(cArrayType->getElementType()->isPointerType());

    // Verify pointee is const int
    clang::QualType pointeeType = cArrayType->getElementType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified());
    EXPECT_TRUE(pointeeType->isIntegerType());
}

/**
 * Test 29: Large array (stress test)
 *
 * C++ Input:  int huge[10000];
 * C Output:   int huge[10000];
 */
TEST_F(VariableHandlerTest, LargeArray) {
    // Arrange: Create int huge[10000]
    clang::ASTContext& ctx = cppAST->getASTContext();

    llvm::APInt arraySize(32, 10000);
    clang::QualType arrayType = ctx.getConstantArrayType(
        ctx.IntTy,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("huge");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_TRUE(cVar->getType()->isArrayType());
    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr);
    EXPECT_EQ(cArrayType->getSize().getZExtValue(), 10000);
}

// ============================================================================
// Phase 3 Tests: Static Local Variables (Task 7)
// ============================================================================

/**
 * Test 30: Static local variable without initialization
 *
 * C++ Input:  static int counter;
 * C Output:   static int counter;
 */
TEST_F(VariableHandlerTest, StaticLocalVariableNoInit) {
    // Arrange: Create static int counter (no init)
    clang::VarDecl* cppVar = createCppVariable("int", "counter", nullptr, clang::SC_Static);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr) << "Result is not a VarDecl";

    EXPECT_EQ(cVar->getNameAsString(), "counter") << "Variable name mismatch";
    EXPECT_TRUE(cVar->getType()->isIntegerType()) << "Type should be int";
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static) << "Storage class should be static";
    EXPECT_FALSE(cVar->hasInit()) << "Should have no initializer";
}

/**
 * Test 31: Static local variable with zero initialization
 *
 * C++ Input:  static int counter = 0;
 * C Output:   static int counter = 0;
 */
TEST_F(VariableHandlerTest, StaticLocalVariableWithZeroInit) {
    // Arrange: Create static int counter = 0
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
    EXPECT_TRUE(cVar->getType()->isIntegerType());
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static) << "Storage class should be static";
    EXPECT_TRUE(cVar->hasInit()) << "Should have initializer";

    // Verify initializer
    auto* initLit = llvm::dyn_cast<clang::IntegerLiteral>(cVar->getInit());
    ASSERT_NE(initLit, nullptr) << "Initializer should be IntegerLiteral";
    EXPECT_EQ(initLit->getValue().getSExtValue(), 0) << "Initializer value should be 0";
}

/**
 * Test 32: Static local variable with non-zero initialization
 *
 * C++ Input:  static int next_id = 100;
 * C Output:   static int next_id = 100;
 */
TEST_F(VariableHandlerTest, StaticLocalVariableWithNonZeroInit) {
    // Arrange: Create static int next_id = 100
    clang::IntegerLiteral* initExpr = createIntLiteral(100);
    clang::VarDecl* cppVar = createCppVariable("int", "next_id", initExpr, clang::SC_Static);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "next_id");
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static);
    EXPECT_TRUE(cVar->hasInit());

    auto* initLit = llvm::dyn_cast<clang::IntegerLiteral>(cVar->getInit());
    ASSERT_NE(initLit, nullptr);
    EXPECT_EQ(initLit->getValue().getSExtValue(), 100);
}

/**
 * Test 33: Static float variable
 *
 * C++ Input:  static float value = 3.14f;
 * C Output:   static float value = 3.14f;
 */
TEST_F(VariableHandlerTest, StaticFloatVariable) {
    // Arrange: Create static float value = 3.14f
    clang::FloatingLiteral* initExpr = createFloatLiteral(3.14f);
    clang::VarDecl* cppVar = createCppVariable("float", "value", initExpr, clang::SC_Static);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "value");
    EXPECT_TRUE(cVar->getType()->isFloatingType());
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static);
    EXPECT_TRUE(cVar->hasInit());

    auto* initLit = llvm::dyn_cast<clang::FloatingLiteral>(cVar->getInit());
    ASSERT_NE(initLit, nullptr);
    EXPECT_NEAR(initLit->getValue().convertToFloat(), 3.14f, 0.01f);
}

/**
 * Test 34: Static array variable
 *
 * C++ Input:  static int cache[10];
 * C Output:   static int cache[10];
 */
TEST_F(VariableHandlerTest, StaticArrayVariable) {
    // Arrange: Create static int cache[10]
    clang::ASTContext& ctx = cppAST->getASTContext();

    llvm::APInt arraySize(32, 10);
    clang::QualType arrayType = ctx.getConstantArrayType(
        ctx.IntTy,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("cache");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        arrayType,
        ctx.getTrivialTypeSourceInfo(arrayType),
        clang::SC_Static
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "cache");
    EXPECT_TRUE(cVar->getType()->isArrayType());
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static) << "Storage class should be static";

    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr);
    EXPECT_EQ(cArrayType->getSize().getZExtValue(), 10);
}

/**
 * Test 35: Static const variable
 *
 * C++ Input:  static const int MAX_SIZE = 1024;
 * C Output:   static const int MAX_SIZE = 1024;
 */
TEST_F(VariableHandlerTest, StaticConstVariable) {
    // Arrange: Create static const int MAX_SIZE = 1024
    clang::IntegerLiteral* initExpr = createIntLiteral(1024);
    clang::VarDecl* cppVar = createCppVariable("const int", "MAX_SIZE", initExpr, clang::SC_Static);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "MAX_SIZE");
    EXPECT_TRUE(cVar->getType().isConstQualified()) << "Should preserve const qualifier";
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static) << "Storage class should be static";
    EXPECT_TRUE(cVar->hasInit());

    auto* initLit = llvm::dyn_cast<clang::IntegerLiteral>(cVar->getInit());
    ASSERT_NE(initLit, nullptr);
    EXPECT_EQ(initLit->getValue().getSExtValue(), 1024);
}

/**
 * Test 36: Static char variable
 *
 * C++ Input:  static char last_char = 'X';
 * C Output:   static char last_char = 'X';
 */
TEST_F(VariableHandlerTest, StaticCharVariable) {
    // Arrange: Create static char last_char = 'X'
    clang::CharacterLiteral* initExpr = createCharLiteral('X');
    clang::VarDecl* cppVar = createCppVariable("char", "last_char", initExpr, clang::SC_Static);
    ASSERT_NE(cppVar, nullptr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "last_char");
    EXPECT_TRUE(cVar->getType()->isCharType());
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static);
    EXPECT_TRUE(cVar->hasInit());

    auto* initLit = llvm::dyn_cast<clang::CharacterLiteral>(cVar->getInit());
    ASSERT_NE(initLit, nullptr);
    EXPECT_EQ(initLit->getValue(), 'X');
}

/**
 * Test 37: Static pointer variable
 *
 * C++ Input:  static int* ptr;
 * C Output:   static int* ptr;
 */
TEST_F(VariableHandlerTest, StaticPointerVariable) {
    // Arrange: Create static int* ptr (no init)
    clang::VarDecl* cppVar = createCppVariable("int*", "ptr", nullptr, clang::SC_Static);
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
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static);
    EXPECT_FALSE(cVar->hasInit());
}

// ============================================================================
// Phase 3 Tests: Const Qualifiers (Task 8)
// ============================================================================

/**
 * Test 38: Const local variable
 *
 * C++ Input:  const int MAX = 100;
 * C Output:   const int MAX = 100;
 */
TEST_F(VariableHandlerTest, ConstLocalVariable) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType constIntType = ctx.IntTy.withConst();
    clang::IntegerLiteral* initExpr = createIntLiteral(100);

    clang::IdentifierInfo& II = ctx.Idents.get("MAX");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        constIntType,
        ctx.getTrivialTypeSourceInfo(constIntType),
        clang::SC_None
    );
    cppVar->setInit(initExpr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "MAX");
    EXPECT_TRUE(cVar->getType().isConstQualified()) << "Should preserve const qualifier";
    EXPECT_TRUE(cVar->getType()->isIntegerType());
    EXPECT_TRUE(cVar->hasInit());
}

/**
 * Test 39: Const global variable
 *
 * C++ Input:  const char* MESSAGE = "Hello";
 * C Output:   const char* MESSAGE = "Hello";
 *
 * Note: We're testing the type preservation, not the string literal handling
 */
TEST_F(VariableHandlerTest, ConstGlobalVariable) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create const char* type
    clang::QualType constCharType = ctx.CharTy.withConst();
    clang::QualType constCharPtrType = ctx.getPointerType(constCharType);

    clang::IdentifierInfo& II = ctx.Idents.get("MESSAGE");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        constCharPtrType,
        ctx.getTrivialTypeSourceInfo(constCharPtrType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "MESSAGE");
    EXPECT_TRUE(cVar->getType()->isPointerType());

    // Verify pointee is const char
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified()) << "Pointee should be const qualified";
    EXPECT_TRUE(pointeeType->isCharType());
}

/**
 * Test 40: Const pointer vs pointer to const
 *
 * C++ Input:  int* const ptr = nullptr;  (const pointer to int)
 * C Output:   int* const ptr = 0;
 *
 * Tests top-level const on pointer itself
 */
TEST_F(VariableHandlerTest, ConstPointer) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create int* const type (const pointer to int)
    clang::QualType intPtrType = ctx.getPointerType(ctx.IntTy);
    clang::QualType constIntPtrType = intPtrType.withConst();

    clang::IdentifierInfo& II = ctx.Idents.get("ptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        constIntPtrType,
        ctx.getTrivialTypeSourceInfo(constIntPtrType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ptr");
    EXPECT_TRUE(cVar->getType().isConstQualified()) << "Pointer itself should be const";
    EXPECT_TRUE(cVar->getType()->isPointerType());

    // Pointee should NOT be const (only pointer is const)
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_FALSE(pointeeType.isConstQualified()) << "Pointee should not be const";
    EXPECT_TRUE(pointeeType->isIntegerType());
}

/**
 * Test 41: Pointer to const (not const pointer)
 *
 * C++ Input:  const int* ptr;  (pointer to const int)
 * C Output:   const int* ptr;
 *
 * Tests const on pointee, not pointer
 */
TEST_F(VariableHandlerTest, PointerToConst) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create const int* type (pointer to const int)
    clang::QualType constIntType = ctx.IntTy.withConst();
    clang::QualType ptrToConstIntType = ctx.getPointerType(constIntType);

    clang::IdentifierInfo& II = ctx.Idents.get("ptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ptrToConstIntType,
        ctx.getTrivialTypeSourceInfo(ptrToConstIntType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ptr");
    EXPECT_FALSE(cVar->getType().isConstQualified()) << "Pointer itself should not be const";
    EXPECT_TRUE(cVar->getType()->isPointerType());

    // Pointee SHOULD be const
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified()) << "Pointee should be const";
    EXPECT_TRUE(pointeeType->isIntegerType());
}

/**
 * Test 42: Const pointer to const
 *
 * C++ Input:  const int* const ptr;  (const pointer to const int)
 * C Output:   const int* const ptr;
 *
 * Tests both top-level and pointee const
 */
TEST_F(VariableHandlerTest, ConstPointerToConst) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create const int* const type
    clang::QualType constIntType = ctx.IntTy.withConst();
    clang::QualType ptrToConstIntType = ctx.getPointerType(constIntType);
    clang::QualType constPtrToConstIntType = ptrToConstIntType.withConst();

    clang::IdentifierInfo& II = ctx.Idents.get("ptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        constPtrToConstIntType,
        ctx.getTrivialTypeSourceInfo(constPtrToConstIntType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ptr");
    EXPECT_TRUE(cVar->getType().isConstQualified()) << "Pointer itself should be const";
    EXPECT_TRUE(cVar->getType()->isPointerType());

    // Pointee should also be const
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified()) << "Pointee should be const";
    EXPECT_TRUE(pointeeType->isIntegerType());
}

/**
 * Test 43: Const array elements
 *
 * C++ Input:  const int arr[5] = {1, 2, 3, 4, 5};
 * C Output:   const int arr[5] = {1, 2, 3, 4, 5};
 *
 * Tests const qualifier on array elements
 */
TEST_F(VariableHandlerTest, ConstArrayElements) {
    // Arrange: Create const int arr[5]
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create array type with const elements
    clang::QualType constIntType = ctx.IntTy.withConst();
    llvm::APInt arraySize(32, 5);
    clang::QualType constArrayType = ctx.getConstantArrayType(
        constIntType,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("arr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        constArrayType,
        ctx.getTrivialTypeSourceInfo(constArrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "arr");
    EXPECT_TRUE(cVar->getType()->isArrayType());

    // Verify array elements are const
    const auto* cArrayType = llvm::dyn_cast<clang::ConstantArrayType>(cVar->getType().getTypePtr());
    ASSERT_NE(cArrayType, nullptr);
    EXPECT_TRUE(cArrayType->getElementType().isConstQualified()) << "Array elements should be const";
    EXPECT_TRUE(cArrayType->getElementType()->isIntegerType());
    EXPECT_EQ(cArrayType->getSize().getZExtValue(), 5);
}

// ============================================================================
// Phase 42 Tests: Pointer Type Declarations (Task 1)
// ============================================================================

/**
 * Test 44: Simple pointer declaration
 *
 * C++ Input:  int* ptr;
 * C Output:   int* ptr;
 *
 * Basic pointer type - should work already via QualType abstraction
 */
TEST_F(VariableHandlerTest, SimplePointerDeclaration) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType ptrType = ctx.getPointerType(ctx.IntTy);

    clang::IdentifierInfo& II = ctx.Idents.get("ptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ptrType,
        ctx.getTrivialTypeSourceInfo(ptrType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr) << "Result is not a VarDecl";

    EXPECT_EQ(cVar->getNameAsString(), "ptr") << "Variable name mismatch";
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Type should be pointer";
    EXPECT_FALSE(cVar->hasInit()) << "Should have no initializer";

    // Verify pointee type
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Pointee should be int";
}

/**
 * Test 45: Pointer with initialization
 *
 * C++ Input:  int* ptr = nullptr;
 * C Output:   int* ptr = NULL;
 *
 * Note: For now we test pointer type preservation with simple init.
 * nullptr handling will be tested in Task 6.
 */
TEST_F(VariableHandlerTest, PointerWithInitialization) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType ptrType = ctx.getPointerType(ctx.IntTy);

    // Create a simple integer literal as placeholder init (0 for NULL)
    clang::IntegerLiteral* initExpr = createIntLiteral(0);

    clang::IdentifierInfo& II = ctx.Idents.get("ptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ptrType,
        ctx.getTrivialTypeSourceInfo(ptrType),
        clang::SC_None
    );
    cppVar->setInit(initExpr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ptr");
    EXPECT_TRUE(cVar->getType()->isPointerType());
    EXPECT_TRUE(cVar->hasInit()) << "Should have initializer";
}

/**
 * Test 46: Pointer-to-pointer (double pointer)
 *
 * C++ Input:  int** pp;
 * C Output:   int** pp;
 */
TEST_F(VariableHandlerTest, PointerToPointer) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType intPtrType = ctx.getPointerType(ctx.IntTy);
    clang::QualType ptrPtrType = ctx.getPointerType(intPtrType);

    clang::IdentifierInfo& II = ctx.Idents.get("pp");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ptrPtrType,
        ctx.getTrivialTypeSourceInfo(ptrPtrType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "pp");
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Top level should be pointer";

    // Verify it's pointer to pointer
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isPointerType()) << "Pointee should also be pointer";

    // Verify ultimate pointee is int
    clang::QualType ultimatePointee = pointeeType->getPointeeType();
    EXPECT_TRUE(ultimatePointee->isIntegerType()) << "Ultimate pointee should be int";
}

/**
 * Test 47: Const pointer (int* const ptr)
 *
 * C++ Input:  int* const ptr;
 * C Output:   int* const ptr;
 *
 * Const qualifier on pointer itself, not pointee
 */
TEST_F(VariableHandlerTest, ConstPointerDeclaration) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType intPtrType = ctx.getPointerType(ctx.IntTy);
    clang::QualType constIntPtrType = intPtrType.withConst();

    clang::IdentifierInfo& II = ctx.Idents.get("ptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        constIntPtrType,
        ctx.getTrivialTypeSourceInfo(constIntPtrType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ptr");
    EXPECT_TRUE(cVar->getType()->isPointerType());
    EXPECT_TRUE(cVar->getType().isConstQualified()) << "Pointer itself should be const";

    // Pointee should NOT be const
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_FALSE(pointeeType.isConstQualified()) << "Pointee should not be const";
    EXPECT_TRUE(pointeeType->isIntegerType());
}

/**
 * Test 48: Pointer to const (const int* ptr)
 *
 * C++ Input:  const int* ptr;
 * C Output:   const int* ptr;
 *
 * Const qualifier on pointee, not pointer
 */
TEST_F(VariableHandlerTest, PointerToConstDeclaration) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType constIntType = ctx.IntTy.withConst();
    clang::QualType ptrToConstIntType = ctx.getPointerType(constIntType);

    clang::IdentifierInfo& II = ctx.Idents.get("ptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ptrToConstIntType,
        ctx.getTrivialTypeSourceInfo(ptrToConstIntType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ptr");
    EXPECT_TRUE(cVar->getType()->isPointerType());
    EXPECT_FALSE(cVar->getType().isConstQualified()) << "Pointer itself should not be const";

    // Pointee SHOULD be const
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified()) << "Pointee should be const";
    EXPECT_TRUE(pointeeType->isIntegerType());
}

/**
 * Test 49: Const pointer to const (const int* const ptr)
 *
 * C++ Input:  const int* const ptr;
 * C Output:   const int* const ptr;
 *
 * Both pointer and pointee are const
 */
TEST_F(VariableHandlerTest, ConstPointerToConstDeclaration) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType constIntType = ctx.IntTy.withConst();
    clang::QualType ptrToConstIntType = ctx.getPointerType(constIntType);
    clang::QualType constPtrToConstIntType = ptrToConstIntType.withConst();

    clang::IdentifierInfo& II = ctx.Idents.get("ptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        constPtrToConstIntType,
        ctx.getTrivialTypeSourceInfo(constPtrToConstIntType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ptr");
    EXPECT_TRUE(cVar->getType()->isPointerType());
    EXPECT_TRUE(cVar->getType().isConstQualified()) << "Pointer itself should be const";

    // Pointee should also be const
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified()) << "Pointee should be const";
    EXPECT_TRUE(pointeeType->isIntegerType());
}

/**
 * Test 50: Void pointer
 *
 * C++ Input:  void* ptr;
 * C Output:   void* ptr;
 */
TEST_F(VariableHandlerTest, VoidPointer) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType voidPtrType = ctx.getPointerType(ctx.VoidTy);

    clang::IdentifierInfo& II = ctx.Idents.get("ptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        voidPtrType,
        ctx.getTrivialTypeSourceInfo(voidPtrType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ptr");
    EXPECT_TRUE(cVar->getType()->isPointerType());

    // Verify pointee is void
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isVoidType()) << "Pointee should be void";
}

/**
 * Test 51: Char pointer (common for strings)
 *
 * C++ Input:  char* str;
 * C Output:   char* str;
 */
TEST_F(VariableHandlerTest, CharPointer) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType charPtrType = ctx.getPointerType(ctx.CharTy);

    clang::IdentifierInfo& II = ctx.Idents.get("str");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        charPtrType,
        ctx.getTrivialTypeSourceInfo(charPtrType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "str");
    EXPECT_TRUE(cVar->getType()->isPointerType());

    // Verify pointee is char
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isCharType()) << "Pointee should be char";
}

/**
 * Test 52: Float pointer
 *
 * C++ Input:  float* fptr;
 * C Output:   float* fptr;
 */
TEST_F(VariableHandlerTest, FloatPointer) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType floatPtrType = ctx.getPointerType(ctx.FloatTy);

    clang::IdentifierInfo& II = ctx.Idents.get("fptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        floatPtrType,
        ctx.getTrivialTypeSourceInfo(floatPtrType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "fptr");
    EXPECT_TRUE(cVar->getType()->isPointerType());

    // Verify pointee is float
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isFloatingType()) << "Pointee should be float";
}

/**
 * Test 53: Global static pointer
 *
 * C++ Input:  static int* globalPtr;
 * C Output:   static int* globalPtr;
 */
TEST_F(VariableHandlerTest, GlobalStaticPointer) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType ptrType = ctx.getPointerType(ctx.IntTy);

    clang::IdentifierInfo& II = ctx.Idents.get("globalPtr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ptrType,
        ctx.getTrivialTypeSourceInfo(ptrType),
        clang::SC_Static
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "globalPtr");
    EXPECT_TRUE(cVar->getType()->isPointerType());
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static) << "Storage class should be static";
}

/**
 * Test 54: Triple pointer (int***)
 *
 * C++ Input:  int*** ppp;
 * C Output:   int*** ppp;
 *
 * Tests deep pointer nesting
 */
TEST_F(VariableHandlerTest, TriplePointer) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType intPtrType = ctx.getPointerType(ctx.IntTy);
    clang::QualType ptrPtrType = ctx.getPointerType(intPtrType);
    clang::QualType ptrPtrPtrType = ctx.getPointerType(ptrPtrType);

    clang::IdentifierInfo& II = ctx.Idents.get("ppp");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ptrPtrPtrType,
        ctx.getTrivialTypeSourceInfo(ptrPtrPtrType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ppp");
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Level 1 should be pointer";

    // Verify level 2
    clang::QualType level2 = cVar->getType()->getPointeeType();
    EXPECT_TRUE(level2->isPointerType()) << "Level 2 should be pointer";

    // Verify level 3
    clang::QualType level3 = level2->getPointeeType();
    EXPECT_TRUE(level3->isPointerType()) << "Level 3 should be pointer";

    // Verify ultimate pointee is int
    clang::QualType ultimatePointee = level3->getPointeeType();
    EXPECT_TRUE(ultimatePointee->isIntegerType()) << "Ultimate pointee should be int";
}

/**
 * Test 55: Pointer to array
 *
 * C++ Input:  int (*ptr)[10];
 * C Output:   int (*ptr)[10];
 *
 * Pointer to array (not array of pointers)
 */
TEST_F(VariableHandlerTest, PointerToArray) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create array type: int[10]
    llvm::APInt arraySize(32, 10);
    clang::QualType arrayType = ctx.getConstantArrayType(
        ctx.IntTy,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    // Create pointer to array: int (*)[10]
    clang::QualType ptrToArrayType = ctx.getPointerType(arrayType);

    clang::IdentifierInfo& II = ctx.Idents.get("ptr");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ptrToArrayType,
        ctx.getTrivialTypeSourceInfo(ptrToArrayType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ptr");
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Should be pointer";

    // Verify pointee is array
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isArrayType()) << "Pointee should be array";

    // Verify array dimensions
    const auto* arrType = llvm::dyn_cast<clang::ConstantArrayType>(pointeeType.getTypePtr());
    ASSERT_NE(arrType, nullptr);
    EXPECT_EQ(arrType->getSize().getZExtValue(), 10);
    EXPECT_TRUE(arrType->getElementType()->isIntegerType());
}

// ============================================================================
// Phase 42 Tests: Reference Type Translation (Task 2)
// ============================================================================

/**
 * Test 44: Lvalue reference local variable
 *
 * C++ Input:  int& ref = x;
 * C Output:   int* ref = &x;
 *
 * Tests basic lvalue reference transformation to pointer.
 * Note: This test focuses on TYPE translation only. The initialization
 * transformation (x → &x) will be handled in Task 7 (Reference Usage).
 */
TEST_F(VariableHandlerTest, LValueReferenceLocal) {
    // Arrange: Create int& ref
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create lvalue reference type: int&
    clang::QualType intRefType = ctx.getLValueReferenceType(ctx.IntTy);

    clang::IdentifierInfo& II = ctx.Idents.get("ref");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        intRefType,
        ctx.getTrivialTypeSourceInfo(intRefType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr) << "Result is not a VarDecl";

    EXPECT_EQ(cVar->getNameAsString(), "ref") << "Variable name mismatch";
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Reference should be translated to pointer";

    // Verify pointee type is int
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Pointee should be int";
}

/**
 * Test 45: Const lvalue reference
 *
 * C++ Input:  const int& ref = x;
 * C Output:   const int* ref = &x;
 *
 * Tests const lvalue reference transformation.
 */
TEST_F(VariableHandlerTest, ConstLValueReference) {
    // Arrange: Create const int& ref
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create const int& type
    clang::QualType constIntType = ctx.IntTy.withConst();
    clang::QualType constIntRefType = ctx.getLValueReferenceType(constIntType);

    clang::IdentifierInfo& II = ctx.Idents.get("ref");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        constIntRefType,
        ctx.getTrivialTypeSourceInfo(constIntRefType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ref");
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Reference should be translated to pointer";

    // Verify pointee is const int
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified()) << "Pointee should be const";
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Pointee should be int";
}

/**
 * Test 46: Reference to pointer
 *
 * C++ Input:  int*& ref = ptr;
 * C Output:   int** ref = &ptr;
 *
 * Tests reference to pointer transformation (becomes pointer-to-pointer).
 */
TEST_F(VariableHandlerTest, ReferenceToPointer) {
    // Arrange: Create int*& ref
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create int*& type
    clang::QualType intPtrType = ctx.getPointerType(ctx.IntTy);
    clang::QualType intPtrRefType = ctx.getLValueReferenceType(intPtrType);

    clang::IdentifierInfo& II = ctx.Idents.get("ref");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        intPtrRefType,
        ctx.getTrivialTypeSourceInfo(intPtrRefType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ref");
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Reference should be translated to pointer";

    // Verify it's pointer-to-pointer (int**)
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isPointerType()) << "Should be pointer-to-pointer";

    // Verify inner pointee is int
    clang::QualType innerPointeeType = pointeeType->getPointeeType();
    EXPECT_TRUE(innerPointeeType->isIntegerType()) << "Inner pointee should be int";
}

/**
 * Test 47: Float reference
 *
 * C++ Input:  float& ref = val;
 * C Output:   float* ref = &val;
 *
 * Tests reference to float type.
 */
TEST_F(VariableHandlerTest, FloatReference) {
    // Arrange: Create float& ref
    clang::ASTContext& ctx = cppAST->getASTContext();

    clang::QualType floatRefType = ctx.getLValueReferenceType(ctx.FloatTy);

    clang::IdentifierInfo& II = ctx.Idents.get("ref");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        floatRefType,
        ctx.getTrivialTypeSourceInfo(floatRefType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ref");
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Reference should be translated to pointer";

    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isFloatingType()) << "Pointee should be float";
}

/**
 * Test 48: Rvalue reference (move semantics)
 *
 * C++ Input:  int&& ref = std::move(x);
 * C Output:   int* ref = &x;  (or may be unsupported)
 *
 * Tests rvalue reference transformation. C has no equivalent for move semantics,
 * so we translate to pointer or may choose to error/warn.
 */
TEST_F(VariableHandlerTest, RValueReference) {
    // Arrange: Create int&& ref
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create rvalue reference type: int&&
    clang::QualType intRValueRefType = ctx.getRValueReferenceType(ctx.IntTy);

    clang::IdentifierInfo& II = ctx.Idents.get("ref");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        intRValueRefType,
        ctx.getTrivialTypeSourceInfo(intRValueRefType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ref");
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Rvalue reference should be translated to pointer";

    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isIntegerType()) << "Pointee should be int";
}

/**
 * Test 49: Static reference variable
 *
 * C++ Input:  static int& ref = global;
 * C Output:   static int* ref = &global;
 *
 * Tests static storage class with reference.
 */
TEST_F(VariableHandlerTest, StaticReference) {
    // Arrange: Create static int& ref
    clang::ASTContext& ctx = cppAST->getASTContext();

    clang::QualType intRefType = ctx.getLValueReferenceType(ctx.IntTy);

    clang::IdentifierInfo& II = ctx.Idents.get("ref");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        intRefType,
        ctx.getTrivialTypeSourceInfo(intRefType),
        clang::SC_Static
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ref");
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static) << "Storage class should be preserved";
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Reference should be translated to pointer";
}

/**
 * Test 50: Char reference
 *
 * C++ Input:  char& c = ch;
 * C Output:   char* c = &ch;
 *
 * Tests reference to char type.
 */
TEST_F(VariableHandlerTest, CharReference) {
    // Arrange: Create char& c
    clang::ASTContext& ctx = cppAST->getASTContext();

    clang::QualType charRefType = ctx.getLValueReferenceType(ctx.CharTy);

    clang::IdentifierInfo& II = ctx.Idents.get("c");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        charRefType,
        ctx.getTrivialTypeSourceInfo(charRefType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "c");
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Reference should be translated to pointer";

    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType->isCharType()) << "Pointee should be char";
}

/**
 * Test 51: Const reference to const
 *
 * C++ Input:  const int& const ref = x;  (unusual but valid in some contexts)
 * C Output:   const int* const ref = &x;
 *
 * Tests double const (const reference to const int).
 * Note: References are inherently const (can't be reseated), but we test
 * for completeness.
 */
TEST_F(VariableHandlerTest, ConstReferenceToConst) {
    // Arrange: Create const int& ref (with const reference type)
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Create const int& type
    clang::QualType constIntType = ctx.IntTy.withConst();
    clang::QualType constIntRefType = ctx.getLValueReferenceType(constIntType);
    // Add const to reference type itself (rare but possible in some contexts)
    clang::QualType constRefToConstInt = constIntRefType.withConst();

    clang::IdentifierInfo& II = ctx.Idents.get("ref");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        constRefToConstInt,
        ctx.getTrivialTypeSourceInfo(constRefToConstInt),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "ref");
    EXPECT_TRUE(cVar->getType()->isPointerType()) << "Reference should be translated to pointer";

    // May or may not preserve top-level const on pointer
    // At minimum, pointee should be const
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified()) << "Pointee should be const";
}

// TODO: Additional tests for Phase 42+:
// - Test 52: Array initialization with InitListExpr
// - Test 53: Complex initialization expressions
// - Test 54: Variable with cast expression init

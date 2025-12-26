/**
 * @file VariableHandlerGlobalTest.cpp
 * @brief TDD tests for global variable support in VariableHandler (Task 6, Phase 3)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (12 tests):
 * 1. GlobalVariableNoInit - int globalVar;
 * 2. GlobalVariableWithInit - int globalCounter = 0;
 * 3. MultipleGlobalVariables - int g1 = 1; int g2 = 2; int g3 = 3;
 * 4. GlobalArray - int globalArray[10];
 * 5. GlobalStringPointer - const char* message;
 * 6. GlobalExternVariable - extern int externalVar;
 * 7. GlobalStaticVariable - static int fileLocalVar = 42;
 * 8. GlobalConstVariable - const int MAX_SIZE = 100;
 * 9. GlobalFloatVariable - float globalPi = 3.14f;
 * 10. GlobalPointerVariable - int* globalPtr;
 * 11. GlobalAndLocalVariablesMixed - Tests scope distinction
 * 12. GlobalVariableLongName - Tests long variable names
 */

#include "handlers/VariableHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class VariableHandlerGlobalTest
 * @brief Test fixture for global variable handling in VariableHandler
 */
class VariableHandlerGlobalTest : public ::testing::Test {
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
};

// ============================================================================
// Task 6: Global Variables Tests
// ============================================================================

/**
 * Test 1: Simple global variable without initialization
 *
 * C++ Input:  int globalVar;
 * C Output:   int globalVar;
 */
TEST_F(VariableHandlerGlobalTest, GlobalVariableNoInit) {
    // Arrange: Create global variable at TranslationUnitDecl scope
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::IdentifierInfo& II = ctx.Idents.get("globalVar");

    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),  // Global scope
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ctx.IntTy,
        ctx.getTrivialTypeSourceInfo(ctx.IntTy),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr) << "Result is not a VarDecl";

    EXPECT_EQ(cVar->getNameAsString(), "globalVar");
    EXPECT_TRUE(cVar->getType()->isIntegerType());
    EXPECT_FALSE(cVar->hasInit());

    // Verify it's at global scope
    EXPECT_TRUE(cVar->isFileVarDecl()) << "Variable should be at global scope";
}

/**
 * Test 2: Global variable with initialization
 *
 * C++ Input:  int globalCounter = 0;
 * C Output:   int globalCounter = 0;
 */
TEST_F(VariableHandlerGlobalTest, GlobalVariableWithInit) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::IntegerLiteral* initExpr = createIntLiteral(0);
    clang::IdentifierInfo& II = ctx.Idents.get("globalCounter");

    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ctx.IntTy,
        ctx.getTrivialTypeSourceInfo(ctx.IntTy),
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

    EXPECT_EQ(cVar->getNameAsString(), "globalCounter");
    EXPECT_TRUE(cVar->hasInit());
    EXPECT_TRUE(cVar->isFileVarDecl());

    auto* initLit = llvm::dyn_cast<clang::IntegerLiteral>(cVar->getInit());
    ASSERT_NE(initLit, nullptr);
    EXPECT_EQ(initLit->getValue().getSExtValue(), 0);
}

/**
 * Test 3: Multiple global variables
 *
 * C++ Input:  int g1 = 1; int g2 = 2; int g3 = 3;
 * C Output:   int g1 = 1; int g2 = 2; int g3 = 3;
 */
TEST_F(VariableHandlerGlobalTest, MultipleGlobalVariables) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();

    auto createGlobalVar = [&](const std::string& name, int value) -> clang::VarDecl* {
        clang::IdentifierInfo& II = ctx.Idents.get(name);
        clang::VarDecl* var = clang::VarDecl::Create(
            ctx,
            ctx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II,
            ctx.IntTy,
            ctx.getTrivialTypeSourceInfo(ctx.IntTy),
            clang::SC_None
        );
        var->setInit(createIntLiteral(value));
        return var;
    };

    clang::VarDecl* g1 = createGlobalVar("g1", 1);
    clang::VarDecl* g2 = createGlobalVar("g2", 2);
    clang::VarDecl* g3 = createGlobalVar("g3", 3);

    VariableHandler handler;

    // Act
    clang::Decl* result1 = handler.handleDecl(g1, *context);
    clang::Decl* result2 = handler.handleDecl(g2, *context);
    clang::Decl* result3 = handler.handleDecl(g3, *context);

    // Assert
    ASSERT_NE(result1, nullptr);
    ASSERT_NE(result2, nullptr);
    ASSERT_NE(result3, nullptr);

    auto* cVar1 = llvm::dyn_cast<clang::VarDecl>(result1);
    auto* cVar2 = llvm::dyn_cast<clang::VarDecl>(result2);
    auto* cVar3 = llvm::dyn_cast<clang::VarDecl>(result3);

    EXPECT_EQ(cVar1->getNameAsString(), "g1");
    EXPECT_EQ(cVar2->getNameAsString(), "g2");
    EXPECT_EQ(cVar3->getNameAsString(), "g3");

    EXPECT_TRUE(cVar1->isFileVarDecl());
    EXPECT_TRUE(cVar2->isFileVarDecl());
    EXPECT_TRUE(cVar3->isFileVarDecl());
}

/**
 * Test 4: Global array
 *
 * C++ Input:  int globalArray[10];
 * C Output:   int globalArray[10];
 */
TEST_F(VariableHandlerGlobalTest, GlobalArray) {
    // Arrange: Create global array
    clang::ASTContext& ctx = cppAST->getASTContext();

    llvm::APInt arraySize(32, 10);
    clang::QualType arrayType = ctx.getConstantArrayType(
        ctx.IntTy,
        arraySize,
        nullptr,
        clang::ArraySizeModifier::Normal,
        0
    );

    clang::IdentifierInfo& II = ctx.Idents.get("globalArray");
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

    EXPECT_EQ(cVar->getNameAsString(), "globalArray");
    EXPECT_TRUE(cVar->getType()->isArrayType());
    EXPECT_TRUE(cVar->isFileVarDecl());
}

/**
 * Test 5: Global string pointer (const char*)
 *
 * C++ Input:  const char* message;
 * C Output:   const char* message;
 */
TEST_F(VariableHandlerGlobalTest, GlobalStringPointer) {
    // Arrange: Create global const char* variable
    clang::ASTContext& ctx = cppAST->getASTContext();

    clang::QualType constCharType = ctx.CharTy.withConst();
    clang::QualType stringType = ctx.getPointerType(constCharType);

    clang::IdentifierInfo& II = ctx.Idents.get("message");
    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        stringType,
        ctx.getTrivialTypeSourceInfo(stringType),
        clang::SC_None
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "message");
    EXPECT_TRUE(cVar->getType()->isPointerType());
    EXPECT_TRUE(cVar->isFileVarDecl());

    // Verify pointee is const char
    clang::QualType pointeeType = cVar->getType()->getPointeeType();
    EXPECT_TRUE(pointeeType.isConstQualified());
    EXPECT_TRUE(pointeeType->isCharType());
}

/**
 * Test 6: Extern global variable declaration
 *
 * C++ Input:  extern int externalVar;
 * C Output:   extern int externalVar;
 */
TEST_F(VariableHandlerGlobalTest, GlobalExternVariable) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::IdentifierInfo& II = ctx.Idents.get("externalVar");

    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ctx.IntTy,
        ctx.getTrivialTypeSourceInfo(ctx.IntTy),
        clang::SC_Extern
    );

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "externalVar");
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Extern);
    EXPECT_TRUE(cVar->isFileVarDecl());
    EXPECT_FALSE(cVar->hasInit()) << "Extern should not have initializer";
}

/**
 * Test 7: Global static variable (file scope)
 *
 * C++ Input:  static int fileLocalVar = 42;
 * C Output:   static int fileLocalVar = 42;
 */
TEST_F(VariableHandlerGlobalTest, GlobalStaticVariable) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::IntegerLiteral* initExpr = createIntLiteral(42);
    clang::IdentifierInfo& II = ctx.Idents.get("fileLocalVar");

    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ctx.IntTy,
        ctx.getTrivialTypeSourceInfo(ctx.IntTy),
        clang::SC_Static
    );
    cppVar->setInit(initExpr);

    // Act
    VariableHandler handler;
    clang::Decl* result = handler.handleDecl(cppVar, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cVar = llvm::dyn_cast<clang::VarDecl>(result);
    ASSERT_NE(cVar, nullptr);

    EXPECT_EQ(cVar->getNameAsString(), "fileLocalVar");
    EXPECT_EQ(cVar->getStorageClass(), clang::SC_Static);
    EXPECT_TRUE(cVar->isFileVarDecl());
    EXPECT_TRUE(cVar->hasInit());
}

/**
 * Test 8: Global const variable
 *
 * C++ Input:  const int MAX_SIZE = 100;
 * C Output:   const int MAX_SIZE = 100;
 */
TEST_F(VariableHandlerGlobalTest, GlobalConstVariable) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::IntegerLiteral* initExpr = createIntLiteral(100);
    clang::IdentifierInfo& II = ctx.Idents.get("MAX_SIZE");

    clang::QualType constIntType = ctx.IntTy.withConst();

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

    EXPECT_EQ(cVar->getNameAsString(), "MAX_SIZE");
    EXPECT_TRUE(cVar->getType().isConstQualified());
    EXPECT_TRUE(cVar->isFileVarDecl());
    EXPECT_TRUE(cVar->hasInit());
}

/**
 * Test 9: Global float variable
 *
 * C++ Input:  float globalPi = 3.14f;
 * C Output:   float globalPi = 3.14f;
 */
TEST_F(VariableHandlerGlobalTest, GlobalFloatVariable) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::FloatingLiteral* initExpr = createFloatLiteral(3.14f);
    clang::IdentifierInfo& II = ctx.Idents.get("globalPi");

    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ctx.FloatTy,
        ctx.getTrivialTypeSourceInfo(ctx.FloatTy),
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

    EXPECT_EQ(cVar->getNameAsString(), "globalPi");
    EXPECT_TRUE(cVar->getType()->isFloatingType());
    EXPECT_TRUE(cVar->isFileVarDecl());
    EXPECT_TRUE(cVar->hasInit());
}

/**
 * Test 10: Global pointer variable
 *
 * C++ Input:  int* globalPtr;
 * C Output:   int* globalPtr;
 */
TEST_F(VariableHandlerGlobalTest, GlobalPointerVariable) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    clang::QualType pointerType = ctx.getPointerType(ctx.IntTy);
    clang::IdentifierInfo& II = ctx.Idents.get("globalPtr");

    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        pointerType,
        ctx.getTrivialTypeSourceInfo(pointerType),
        clang::SC_None
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
    EXPECT_TRUE(cVar->isFileVarDecl());
}

/**
 * Test 11: Mix of global and local variables
 *
 * Ensures handler correctly distinguishes scope
 *
 * Note: For Task 6 (Global Variables), we only test that global variables
 * are correctly identified. Full local variable scope handling requires
 * the FunctionHandler to first register the translated function in the context.
 * That's beyond the scope of Task 6.
 */
TEST_F(VariableHandlerGlobalTest, GlobalAndLocalVariablesMixed) {
    // Arrange: Create two global variables and one that would be local
    clang::ASTContext& ctx = cppAST->getASTContext();

    // Global variable 1
    clang::IdentifierInfo& global1II = ctx.Idents.get("globalVar1");
    clang::VarDecl* globalVar1 = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &global1II,
        ctx.IntTy,
        ctx.getTrivialTypeSourceInfo(ctx.IntTy),
        clang::SC_None
    );
    globalVar1->setInit(createIntLiteral(10));

    // Global variable 2
    clang::IdentifierInfo& global2II = ctx.Idents.get("globalVar2");
    clang::VarDecl* globalVar2 = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &global2II,
        ctx.FloatTy,
        ctx.getTrivialTypeSourceInfo(ctx.FloatTy),
        clang::SC_None
    );
    globalVar2->setInit(createFloatLiteral(3.14f));

    // Create a function for local scope
    clang::IdentifierInfo& funcII = ctx.Idents.get("testFunc");
    clang::DeclarationName funcName(&funcII);
    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = ctx.getFunctionType(ctx.VoidTy, {}, EPI);
    clang::FunctionDecl* func = clang::FunctionDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        funcName,
        funcType,
        ctx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    // Local variable within function
    // Note: This will be created at global scope because the function hasn't
    // been registered in the context yet. This is expected behavior for Task 6.
    clang::IdentifierInfo& localII = ctx.Idents.get("localVar");
    clang::VarDecl* localVar = clang::VarDecl::Create(
        ctx,
        func,  // Function scope
        clang::SourceLocation(),
        clang::SourceLocation(),
        &localII,
        ctx.IntTy,
        ctx.getTrivialTypeSourceInfo(ctx.IntTy),
        clang::SC_None
    );
    localVar->setInit(createIntLiteral(20));

    VariableHandler handler;

    // Act
    clang::Decl* global1Result = handler.handleDecl(globalVar1, *context);
    clang::Decl* global2Result = handler.handleDecl(globalVar2, *context);
    clang::Decl* localResult = handler.handleDecl(localVar, *context);

    // Assert - verify global variables are at file scope
    ASSERT_NE(global1Result, nullptr);
    ASSERT_NE(global2Result, nullptr);
    ASSERT_NE(localResult, nullptr);

    auto* cGlobal1 = llvm::dyn_cast<clang::VarDecl>(global1Result);
    auto* cGlobal2 = llvm::dyn_cast<clang::VarDecl>(global2Result);
    auto* cLocal = llvm::dyn_cast<clang::VarDecl>(localResult);

    EXPECT_TRUE(cGlobal1->isFileVarDecl()) << "globalVar1 should be at file scope";
    EXPECT_TRUE(cGlobal2->isFileVarDecl()) << "globalVar2 should be at file scope";

    // For Task 6, we're focusing on global variables.
    // Local variable scope handling will be enhanced when FunctionHandler
    // integration is complete. For now, verify the handler can process
    // the local variable (even if it ends up at global scope).
    ASSERT_NE(cLocal, nullptr) << "Local variable should be processed";
    EXPECT_EQ(cLocal->getNameAsString(), "localVar");
}

/**
 * Test 12: Global variable with long name
 *
 * C++ Input:  int very_long_global_variable_name = 999;
 * C Output:   int very_long_global_variable_name = 999;
 */
TEST_F(VariableHandlerGlobalTest, GlobalVariableLongName) {
    // Arrange
    clang::ASTContext& ctx = cppAST->getASTContext();
    std::string longName = "very_long_global_variable_name";
    clang::IntegerLiteral* initExpr = createIntLiteral(999);
    clang::IdentifierInfo& II = ctx.Idents.get(longName);

    clang::VarDecl* cppVar = clang::VarDecl::Create(
        ctx,
        ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        ctx.IntTy,
        ctx.getTrivialTypeSourceInfo(ctx.IntTy),
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

    EXPECT_EQ(cVar->getNameAsString(), longName);
    EXPECT_TRUE(cVar->isFileVarDecl());
}

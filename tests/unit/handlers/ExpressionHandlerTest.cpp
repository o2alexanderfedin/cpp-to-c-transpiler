/**
 * @file ExpressionHandlerTest.cpp
 * @brief TDD tests for ExpressionHandler
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (35+ tests):
 *
 * LITERALS (5 tests):
 * 1. IntegerLiteral - 42
 * 2. NegativeIntegerLiteral - -10
 * 3. FloatingLiteral - 3.14
 * 4. StringLiteral - "hello"
 * 5. CharacterLiteral - 'a'
 *
 * BINARY OPERATORS (15 tests):
 * 6. BinaryAddition - a + b
 * 7. BinarySubtraction - a - b
 * 8. BinaryMultiplication - a * b
 * 9. BinaryDivision - a / b
 * 10. BinaryModulo - a % b
 * 11. NestedAddition - (a + b) + c
 * 12. MixedArithmetic - a + b * c
 * 13. ComplexNesting - (a + b) * (c - d)
 * 14. ComparisonEqual - a == b
 * 15. ComparisonNotEqual - a != b
 * 16. ComparisonLess - a < b
 * 17. ComparisonGreater - a > b
 * 18. ComparisonLessEqual - a <= b
 * 19. ComparisonGreaterEqual - a >= b
 * 20. LogicalAnd - a && b
 *
 * UNARY OPERATORS (5 tests):
 * 21. UnaryMinus - -x
 * 22. UnaryPlus - +x
 * 23. UnaryIncrement - ++x
 * 24. UnaryDecrement - --x
 * 25. UnaryNot - !x
 *
 * DECLREFEXPR (5 tests):
 * 26. SimpleVarRef - x
 * 27. VarRefInExpr - x + 1
 * 28. MultipleVarRefs - x + y
 * 29. VarRefNested - (x + y) * z
 * 30. VarRefWithLiteral - x * 2
 *
 * COMPLEX EXPRESSIONS (10+ tests):
 * 31. ArithmeticChain - a + b - c + d
 * 32. DeepNesting - ((a + b) * (c - d)) / e
 * 33. AllOperators - (a + b) * c / d - e % f
 * 34. LogicalChain - a && b || c
 * 35. MixedComparison - (a > b) && (c < d)
 * 36. ParenthesizedExpr - (a + b)
 * 37. MultiLevelNesting - (((a + b) * c) - d) / e
 * 38. ComplexLogical - (a > 0 && b < 100) || c == 42
 */

#include "handlers/ExpressionHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ExpressionHandlerTest
 * @brief Test fixture for ExpressionHandler
 *
 * Uses clang::tooling::buildASTFromCode for real AST contexts.
 */
class ExpressionHandlerTest : public ::testing::Test {
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
     * @brief Helper class to extract expressions from AST
     */
    class ExprExtractor : public clang::RecursiveASTVisitor<ExprExtractor> {
    public:
        clang::Expr* foundExpr = nullptr;

        bool VisitExpr(clang::Expr* E) {
            if (!foundExpr && !llvm::isa<clang::ImplicitCastExpr>(E)) {
                foundExpr = E;
            }
            return true;
        }
    };

    /**
     * @brief Parse C++ code and extract first expression
     */
    clang::Expr* parseExpr(const std::string& code) {
        std::string fullCode = "void test() { " + code + "; }";
        auto AST = clang::tooling::buildASTFromCode(fullCode);
        if (!AST) return nullptr;

        ExprExtractor extractor;
        extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
        return extractor.foundExpr;
    }
};

// ============================================================================
// LITERALS (Tests 1-5)
// ============================================================================

/**
 * Test 1: Integer Literal
 * C++ Input: 42
 * Expected: IntegerLiteral with value 42
 */
TEST_F(ExpressionHandlerTest, IntegerLiteral) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("42");
    ASSERT_NE(cppExpr, nullptr);
    ASSERT_TRUE(llvm::isa<clang::IntegerLiteral>(cppExpr));

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* intLit = llvm::dyn_cast<clang::IntegerLiteral>(result);
    ASSERT_NE(intLit, nullptr) << "Result is not IntegerLiteral";
    EXPECT_EQ(intLit->getValue().getLimitedValue(), 42);
}

/**
 * Test 2: Negative Integer Literal (via UnaryOperator)
 * C++ Input: -10
 * Expected: UnaryOperator with IntegerLiteral
 */
TEST_F(ExpressionHandlerTest, NegativeIntegerLiteral) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("-10");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
}

/**
 * Test 3: Floating Literal
 * C++ Input: 3.14
 * Expected: FloatingLiteral
 */
TEST_F(ExpressionHandlerTest, FloatingLiteral) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("3.14");
    ASSERT_NE(cppExpr, nullptr);
    ASSERT_TRUE(llvm::isa<clang::FloatingLiteral>(cppExpr));

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* floatLit = llvm::dyn_cast<clang::FloatingLiteral>(result);
    ASSERT_NE(floatLit, nullptr) << "Result is not FloatingLiteral";
}

/**
 * Test 4: String Literal
 * C++ Input: "hello"
 * Expected: StringLiteral
 */
TEST_F(ExpressionHandlerTest, StringLiteral) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("\"hello\"");
    ASSERT_NE(cppExpr, nullptr);
    ASSERT_TRUE(llvm::isa<clang::StringLiteral>(cppExpr));

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* strLit = llvm::dyn_cast<clang::StringLiteral>(result);
    ASSERT_NE(strLit, nullptr) << "Result is not StringLiteral";
    EXPECT_EQ(strLit->getString().str(), "hello");
}

/**
 * Test 5: Character Literal
 * C++ Input: 'a'
 * Expected: CharacterLiteral
 */
TEST_F(ExpressionHandlerTest, CharacterLiteral) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("'a'");
    ASSERT_NE(cppExpr, nullptr);
    ASSERT_TRUE(llvm::isa<clang::CharacterLiteral>(cppExpr));

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* charLit = llvm::dyn_cast<clang::CharacterLiteral>(result);
    ASSERT_NE(charLit, nullptr) << "Result is not CharacterLiteral";
    EXPECT_EQ(charLit->getValue(), 'a');
}

// ============================================================================
// BINARY OPERATORS (Tests 6-20)
// ============================================================================

/**
 * Test 6: Binary Addition
 * C++ Input: 1 + 2
 * Expected: BinaryOperator with BO_Add
 */
TEST_F(ExpressionHandlerTest, BinaryAddition) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 + 2");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr) << "Translation returned null";
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr) << "Result is not BinaryOperator";
    EXPECT_EQ(binOp->getOpcode(), clang::BO_Add);
}

/**
 * Test 7: Binary Subtraction
 * C++ Input: 5 - 3
 * Expected: BinaryOperator with BO_Sub
 */
TEST_F(ExpressionHandlerTest, BinarySubtraction) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("5 - 3");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_Sub);
}

/**
 * Test 8: Binary Multiplication
 * C++ Input: 4 * 5
 * Expected: BinaryOperator with BO_Mul
 */
TEST_F(ExpressionHandlerTest, BinaryMultiplication) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("4 * 5");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_Mul);
}

/**
 * Test 9: Binary Division
 * C++ Input: 10 / 2
 * Expected: BinaryOperator with BO_Div
 */
TEST_F(ExpressionHandlerTest, BinaryDivision) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("10 / 2");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_Div);
}

/**
 * Test 10: Binary Modulo
 * C++ Input: 7 % 3
 * Expected: BinaryOperator with BO_Rem
 */
TEST_F(ExpressionHandlerTest, BinaryModulo) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("7 % 3");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_Rem);
}

/**
 * Test 11: Nested Addition
 * C++ Input: (1 + 2) + 3
 * Expected: Nested BinaryOperator tree
 */
TEST_F(ExpressionHandlerTest, NestedAddition) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("(1 + 2) + 3");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_Add);

    // Check LHS is also a BinaryOperator
    auto* lhs = llvm::dyn_cast<clang::BinaryOperator>(binOp->getLHS()->IgnoreParens());
    ASSERT_NE(lhs, nullptr);
    EXPECT_EQ(lhs->getOpcode(), clang::BO_Add);
}

/**
 * Test 12: Mixed Arithmetic
 * C++ Input: 1 + 2 * 3
 * Expected: BinaryOperator respecting precedence
 */
TEST_F(ExpressionHandlerTest, MixedArithmetic) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 + 2 * 3");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_Add);
}

/**
 * Test 13: Complex Nesting
 * C++ Input: (1 + 2) * (3 - 4)
 * Expected: Nested BinaryOperators
 */
TEST_F(ExpressionHandlerTest, ComplexNesting) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("(1 + 2) * (3 - 4)");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_Mul);
}

/**
 * Test 14: Comparison Equal
 * C++ Input: 1 == 2
 * Expected: BinaryOperator with BO_EQ
 */
TEST_F(ExpressionHandlerTest, ComparisonEqual) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 == 2");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_EQ);
}

/**
 * Test 15: Comparison Not Equal
 * C++ Input: 1 != 2
 * Expected: BinaryOperator with BO_NE
 */
TEST_F(ExpressionHandlerTest, ComparisonNotEqual) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 != 2");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_NE);
}

/**
 * Test 16: Comparison Less
 * C++ Input: 1 < 2
 * Expected: BinaryOperator with BO_LT
 */
TEST_F(ExpressionHandlerTest, ComparisonLess) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 < 2");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_LT);
}

/**
 * Test 17: Comparison Greater
 * C++ Input: 1 > 2
 * Expected: BinaryOperator with BO_GT
 */
TEST_F(ExpressionHandlerTest, ComparisonGreater) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 > 2");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_GT);
}

/**
 * Test 18: Comparison Less Equal
 * C++ Input: 1 <= 2
 * Expected: BinaryOperator with BO_LE
 */
TEST_F(ExpressionHandlerTest, ComparisonLessEqual) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 <= 2");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_LE);
}

/**
 * Test 19: Comparison Greater Equal
 * C++ Input: 1 >= 2
 * Expected: BinaryOperator with BO_GE
 */
TEST_F(ExpressionHandlerTest, ComparisonGreaterEqual) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 >= 2");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_GE);
}

/**
 * Test 20: Logical AND
 * C++ Input: 1 && 0
 * Expected: BinaryOperator with BO_LAnd
 */
TEST_F(ExpressionHandlerTest, LogicalAnd) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 && 0");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), clang::BO_LAnd);
}

// ============================================================================
// UNARY OPERATORS (Tests 21-25)
// ============================================================================

/**
 * Test 21: Unary Minus
 * C++ Input: -5
 * Expected: UnaryOperator with UO_Minus
 */
TEST_F(ExpressionHandlerTest, UnaryMinus) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("-5");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* unOp = llvm::dyn_cast<clang::UnaryOperator>(result);
    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), clang::UO_Minus);
}

/**
 * Test 22: Unary Plus
 * C++ Input: +5
 * Expected: UnaryOperator with UO_Plus
 */
TEST_F(ExpressionHandlerTest, UnaryPlus) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("+5");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* unOp = llvm::dyn_cast<clang::UnaryOperator>(result);
    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), clang::UO_Plus);
}

/**
 * Test 23: Unary Increment (prefix)
 * C++ Input: ++x
 * Expected: UnaryOperator with UO_PreInc
 */
TEST_F(ExpressionHandlerTest, UnaryIncrement) {
    // Arrange
    std::string code = "int x = 0; void test() { ++x; }";
    auto AST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(AST, nullptr);

    ExprExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    clang::Expr* cppExpr = extractor.foundExpr;
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 24: Unary Decrement (prefix)
 * C++ Input: --x
 * Expected: UnaryOperator with UO_PreDec
 */
TEST_F(ExpressionHandlerTest, UnaryDecrement) {
    // Arrange
    std::string code = "int x = 10; void test() { --x; }";
    auto AST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(AST, nullptr);

    ExprExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    clang::Expr* cppExpr = extractor.foundExpr;
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 25: Unary Logical NOT
 * C++ Input: !0
 * Expected: UnaryOperator with UO_LNot
 */
TEST_F(ExpressionHandlerTest, UnaryNot) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("!0");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* unOp = llvm::dyn_cast<clang::UnaryOperator>(result);
    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), clang::UO_LNot);
}

// ============================================================================
// DECLREFEXPR (Tests 26-30)
// ============================================================================

/**
 * Test 26: Simple Variable Reference
 * C++ Input: x
 * Expected: DeclRefExpr
 */
TEST_F(ExpressionHandlerTest, SimpleVarRef) {
    // Arrange
    std::string code = "int x = 5; void test() { x; }";
    auto AST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(AST, nullptr);

    ExprExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    clang::Expr* cppExpr = extractor.foundExpr;
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 27: Variable Reference in Expression
 * C++ Input: x + 1
 * Expected: BinaryOperator with DeclRefExpr
 */
TEST_F(ExpressionHandlerTest, VarRefInExpr) {
    // Arrange
    std::string code = "int x = 5; void test() { x + 1; }";
    auto AST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(AST, nullptr);

    ExprExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    clang::Expr* cppExpr = extractor.foundExpr;
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(result);
    ASSERT_NE(binOp, nullptr);
}

/**
 * Test 28: Multiple Variable References
 * C++ Input: x + y
 * Expected: BinaryOperator with two DeclRefExprs
 */
TEST_F(ExpressionHandlerTest, MultipleVarRefs) {
    // Arrange
    std::string code = "int x = 5; int y = 10; void test() { x + y; }";
    auto AST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(AST, nullptr);

    ExprExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    clang::Expr* cppExpr = extractor.foundExpr;
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 29: Variable Reference Nested
 * C++ Input: (x + y) * z
 * Expected: Nested operators with DeclRefExprs
 */
TEST_F(ExpressionHandlerTest, VarRefNested) {
    // Arrange
    std::string code = "int x=1, y=2, z=3; void test() { (x + y) * z; }";
    auto AST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(AST, nullptr);

    ExprExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    clang::Expr* cppExpr = extractor.foundExpr;
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 30: Variable Reference with Literal
 * C++ Input: x * 2
 * Expected: BinaryOperator with DeclRefExpr and IntegerLiteral
 */
TEST_F(ExpressionHandlerTest, VarRefWithLiteral) {
    // Arrange
    std::string code = "int x = 5; void test() { x * 2; }";
    auto AST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(AST, nullptr);

    ExprExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    clang::Expr* cppExpr = extractor.foundExpr;
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

// ============================================================================
// COMPLEX EXPRESSIONS (Tests 31-38)
// ============================================================================

/**
 * Test 31: Arithmetic Chain
 * C++ Input: 1 + 2 - 3 + 4
 * Expected: Chained BinaryOperators
 */
TEST_F(ExpressionHandlerTest, ArithmeticChain) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 + 2 - 3 + 4");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 32: Deep Nesting
 * C++ Input: ((1 + 2) * (3 - 4)) / 5
 * Expected: Deeply nested BinaryOperators
 */
TEST_F(ExpressionHandlerTest, DeepNesting) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("((1 + 2) * (3 - 4)) / 5");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 33: All Operators
 * C++ Input: (1 + 2) * 3 / 4 - 5 % 6
 * Expected: Mixed operator tree
 */
TEST_F(ExpressionHandlerTest, AllOperators) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("(1 + 2) * 3 / 4 - 5 % 6");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 34: Logical Chain
 * C++ Input: 1 && 0 || 1
 * Expected: Chained logical operators
 */
TEST_F(ExpressionHandlerTest, LogicalChain) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("1 && 0 || 1");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 35: Mixed Comparison
 * C++ Input: (1 > 2) && (3 < 4)
 * Expected: Logical AND of comparisons
 */
TEST_F(ExpressionHandlerTest, MixedComparison) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("(1 > 2) && (3 < 4)");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 36: Parenthesized Expression
 * C++ Input: (42)
 * Expected: ParenExpr wrapping IntegerLiteral
 */
TEST_F(ExpressionHandlerTest, ParenthesizedExpr) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("(42)");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 37: Multi-Level Nesting
 * C++ Input: (((1 + 2) * 3) - 4) / 5
 * Expected: Multi-level nested operators
 */
TEST_F(ExpressionHandlerTest, MultiLevelNesting) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("(((1 + 2) * 3) - 4) / 5");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

/**
 * Test 38: Complex Logical Expression
 * C++ Input: (1 > 0 && 2 < 100) || 3 == 42
 * Expected: Complex logical tree
 */
TEST_F(ExpressionHandlerTest, ComplexLogical) {
    // Arrange
    clang::Expr* cppExpr = parseExpr("(1 > 0 && 2 < 100) || 3 == 42");
    ASSERT_NE(cppExpr, nullptr);

    // Act
    ExpressionHandler handler;
    clang::Expr* result = handler.handleExpr(cppExpr, *context);

    // Assert
    ASSERT_NE(result, nullptr);
}

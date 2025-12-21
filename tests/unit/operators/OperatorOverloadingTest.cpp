// Unit Tests for C++ Operator Overloading Detection
// Stream 4: Comprehensive operator overloading tests for C++ to C transpiler
//
// Tests ensure that C++ operator overloading is correctly detected in the AST.
// These tests validate operator detection, parameter types, const correctness,
// and operator classification - prerequisites for transpilation to C functions.

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"

using namespace clang;

// Test fixture base class with helper method
class OperatorOverloadingTestBase : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// ARITHMETIC OPERATORS (15 tests)
// ============================================================================

class ArithmeticOperatorTest : public OperatorOverloadingTestBase {};

// Test 1: Binary + operator
TEST_F(ArithmeticOperatorTest, BinaryPlusOperator) {
    const char *code = R"(
        class Vector2D {
        public:
            int x, y;
            Vector2D operator+(const Vector2D& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opPlus = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Vector2D") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Plus) {
                        opPlus = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opPlus, nullptr) << "operator+ not found";
    EXPECT_EQ(opPlus->getNumParams(), 1) << "operator+ should have 1 parameter";
    EXPECT_TRUE(opPlus->isConst()) << "operator+ should be const";
}

// Test 2: Binary - operator
TEST_F(ArithmeticOperatorTest, BinaryMinusOperator) {
    const char *code = R"(
        class Complex {
        public:
            double real, imag;
            Complex operator-(const Complex& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opMinus = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Complex") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Minus && M->getNumParams() == 1) {
                        opMinus = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opMinus, nullptr) << "operator- not found";
    EXPECT_EQ(opMinus->getNumParams(), 1) << "Binary operator- should have 1 parameter";
}

// Test 3: Binary * operator
TEST_F(ArithmeticOperatorTest, BinaryMultiplyOperator) {
    const char *code = R"(
        class Matrix {
        public:
            Matrix operator*(const Matrix& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opMul = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Matrix") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Star && M->getNumParams() == 1) {
                        opMul = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opMul, nullptr) << "operator* not found";
}

// Test 4: Binary / operator
TEST_F(ArithmeticOperatorTest, BinaryDivideOperator) {
    const char *code = R"(
        class Fraction {
        public:
            int numerator, denominator;
            Fraction operator/(const Fraction& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opDiv = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Fraction") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Slash) {
                        opDiv = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opDiv, nullptr) << "operator/ not found";
}

// Test 5: Binary % operator
TEST_F(ArithmeticOperatorTest, BinaryModuloOperator) {
    const char *code = R"(
        class Integer {
        public:
            int value;
            Integer operator%(const Integer& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opMod = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Integer") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Percent) {
                        opMod = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opMod, nullptr) << "operator% not found";
}

// Test 6: Unary - operator
TEST_F(ArithmeticOperatorTest, UnaryMinusOperator) {
    const char *code = R"(
        class Number {
        public:
            double value;
            Number operator-() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opUnaryMinus = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Number") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Minus && M->getNumParams() == 0) {
                        opUnaryMinus = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opUnaryMinus, nullptr) << "Unary operator- not found";
    EXPECT_EQ(opUnaryMinus->getNumParams(), 0) << "Unary operator- should have 0 parameters";
}

// Test 7: Unary + operator
TEST_F(ArithmeticOperatorTest, UnaryPlusOperator) {
    const char *code = R"(
        class SignedInt {
        public:
            int value;
            SignedInt operator+() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opUnaryPlus = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "SignedInt") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Plus && M->getNumParams() == 0) {
                        opUnaryPlus = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opUnaryPlus, nullptr) << "Unary operator+ not found";
    EXPECT_EQ(opUnaryPlus->getNumParams(), 0) << "Unary operator+ should have 0 parameters";
}

// Test 8: Prefix ++ operator
TEST_F(ArithmeticOperatorTest, PrefixIncrementOperator) {
    const char *code = R"(
        class Counter {
        public:
            int count;
            Counter& operator++();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opPrefixInc = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Counter") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_PlusPlus && M->getNumParams() == 0) {
                        opPrefixInc = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opPrefixInc, nullptr) << "Prefix operator++ not found";
    EXPECT_TRUE(opPrefixInc->getReturnType()->isReferenceType()) << "Prefix operator++ should return reference";
}

// Test 9: Postfix ++ operator
TEST_F(ArithmeticOperatorTest, PostfixIncrementOperator) {
    const char *code = R"(
        class Iterator {
        public:
            int position;
            Iterator operator++(int);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opPostfixInc = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Iterator") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_PlusPlus && M->getNumParams() == 1) {
                        opPostfixInc = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opPostfixInc, nullptr) << "Postfix operator++ not found";
    EXPECT_EQ(opPostfixInc->getNumParams(), 1) << "Postfix operator++ should have dummy int parameter";
}

// Test 10: Prefix -- operator
TEST_F(ArithmeticOperatorTest, PrefixDecrementOperator) {
    const char *code = R"(
        class Countdown {
        public:
            int value;
            Countdown& operator--();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opPrefixDec = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Countdown") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_MinusMinus && M->getNumParams() == 0) {
                        opPrefixDec = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opPrefixDec, nullptr) << "Prefix operator-- not found";
}

// Test 11: Postfix -- operator
TEST_F(ArithmeticOperatorTest, PostfixDecrementOperator) {
    const char *code = R"(
        class ReverseIterator {
        public:
            int position;
            ReverseIterator operator--(int);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opPostfixDec = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ReverseIterator") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_MinusMinus && M->getNumParams() == 1) {
                        opPostfixDec = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opPostfixDec, nullptr) << "Postfix operator-- not found";
}

// Test 12: Compound += operator
TEST_F(ArithmeticOperatorTest, CompoundPlusAssignOperator) {
    const char *code = R"(
        class Accumulator {
        public:
            int total;
            Accumulator& operator+=(const Accumulator& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opPlusAssign = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Accumulator") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_PlusEqual) {
                        opPlusAssign = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opPlusAssign, nullptr) << "operator+= not found";
}

// Test 13: Compound -= operator
TEST_F(ArithmeticOperatorTest, CompoundMinusAssignOperator) {
    const char *code = R"(
        class Balance {
        public:
            double amount;
            Balance& operator-=(const Balance& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opMinusAssign = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Balance") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_MinusEqual) {
                        opMinusAssign = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opMinusAssign, nullptr) << "operator-= not found";
}

// Test 14: Compound *= operator
TEST_F(ArithmeticOperatorTest, CompoundMultiplyAssignOperator) {
    const char *code = R"(
        class Scale {
        public:
            double factor;
            Scale& operator*=(const Scale& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opMulAssign = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Scale") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_StarEqual) {
                        opMulAssign = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opMulAssign, nullptr) << "operator*= not found";
}

// Test 15: Compound /= operator
TEST_F(ArithmeticOperatorTest, CompoundDivideAssignOperator) {
    const char *code = R"(
        class Ratio {
        public:
            double value;
            Ratio& operator/=(const Ratio& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opDivAssign = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Ratio") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_SlashEqual) {
                        opDivAssign = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opDivAssign, nullptr) << "operator/= not found";
}

// ============================================================================
// COMPARISON OPERATORS (10 tests)
// ============================================================================

class ComparisonOperatorTest : public OperatorOverloadingTestBase {};

// Test 16: operator==
TEST_F(ComparisonOperatorTest, EqualityOperator) {
    const char *code = R"(
        class Point {
        public:
            int x, y;
            bool operator==(const Point& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Point") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_EqualEqual) {
                        opEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opEqual, nullptr) << "operator== not found";
    EXPECT_TRUE(opEqual->getReturnType()->isBooleanType()) << "operator== should return bool";
}

// Test 17: operator!=
TEST_F(ComparisonOperatorTest, InequalityOperator) {
    const char *code = R"(
        class String {
        public:
            char* data;
            bool operator!=(const String& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opNotEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "String") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_ExclaimEqual) {
                        opNotEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opNotEqual, nullptr) << "operator!= not found";
}

// Test 18: operator<
TEST_F(ComparisonOperatorTest, LessThanOperator) {
    const char *code = R"(
        class ComparableInt {
        public:
            int value;
            bool operator<(const ComparableInt& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLess = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ComparableInt") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Less) {
                        opLess = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLess, nullptr) << "operator< not found";
}

// Test 19: operator>
TEST_F(ComparisonOperatorTest, GreaterThanOperator) {
    const char *code = R"(
        class Priority {
        public:
            int level;
            bool operator>(const Priority& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opGreater = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Priority") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Greater) {
                        opGreater = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opGreater, nullptr) << "operator> not found";
}

// Test 20: operator<=
TEST_F(ComparisonOperatorTest, LessOrEqualOperator) {
    const char *code = R"(
        class Version {
        public:
            int major, minor;
            bool operator<=(const Version& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLessEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Version") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_LessEqual) {
                        opLessEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLessEqual, nullptr) << "operator<= not found";
}

// Test 21: operator>=
TEST_F(ComparisonOperatorTest, GreaterOrEqualOperator) {
    const char *code = R"(
        class Score {
        public:
            double points;
            bool operator>=(const Score& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opGreaterEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Score") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_GreaterEqual) {
                        opGreaterEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opGreaterEqual, nullptr) << "operator>= not found";
}

// Test 22: Multiple comparison operators in same class
TEST_F(ComparisonOperatorTest, MultipleComparisonOperators) {
    const char *code = R"(
        class Comparable {
        public:
            int value;
            bool operator==(const Comparable& other) const;
            bool operator!=(const Comparable& other) const;
            bool operator<(const Comparable& other) const;
            bool operator>(const Comparable& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int operatorCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Comparable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        operatorCount++;
                    }
                }
            }
        }
    }

    EXPECT_EQ(operatorCount, 4) << "Expected 4 comparison operators";
}

// Test 23: Comparison with different parameter types
TEST_F(ComparisonOperatorTest, ComparisonWithDifferentTypes) {
    const char *code = R"(
        class Mixed {
        public:
            int value;
            bool operator==(int other) const;
            bool operator==(const Mixed& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqualInt = nullptr;
    CXXMethodDecl *opEqualMixed = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Mixed") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_EqualEqual) {
                        QualType paramType = M->getParamDecl(0)->getType();
                        if (paramType->isIntegerType()) {
                            opEqualInt = M;
                        } else {
                            opEqualMixed = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(opEqualInt, nullptr) << "operator==(int) not found";
    ASSERT_NE(opEqualMixed, nullptr) << "operator==(const Mixed&) not found";
}

// Test 24: Friend comparison operators
TEST_F(ComparisonOperatorTest, FriendComparisonOperators) {
    const char *code = R"(
        class Value {
        public:
            int data;
            friend bool operator==(const Value& a, const Value& b);
        };
        bool operator==(const Value& a, const Value& b);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *friendOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->isOverloadedOperator() && FD->getOverloadedOperator() == OO_EqualEqual) {
                friendOp = FD;
                break;
            }
        }
    }

    ASSERT_NE(friendOp, nullptr) << "Friend operator== not found";
    EXPECT_EQ(friendOp->getNumParams(), 2) << "Friend operator== should have 2 parameters";
}

// Test 25: Const correctness in comparison operators
TEST_F(ComparisonOperatorTest, ConstCorrectnessComparison) {
    const char *code = R"(
        class ConstTest {
        public:
            int value;
            bool operator<(const ConstTest& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLess = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ConstTest") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Less) {
                        opLess = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLess, nullptr) << "operator< not found";
    EXPECT_TRUE(opLess->isConst()) << "Comparison operator should be const";

    // For reference parameters, check if the referenced type is const-qualified
    QualType paramType = opLess->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType.isConstQualified()) << "Parameter should be const";
}

// ============================================================================
// SUBSCRIPT & CALL OPERATORS (12 tests)
// ============================================================================

class SubscriptCallOperatorTest : public OperatorOverloadingTestBase {};

// Test 26: operator[] - array subscript
TEST_F(SubscriptCallOperatorTest, SubscriptOperator) {
    const char *code = R"(
        class Array {
        public:
            int* data;
            int& operator[](int index);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opSubscript = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Array") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Subscript) {
                        opSubscript = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opSubscript, nullptr) << "operator[] not found";
    EXPECT_TRUE(opSubscript->getReturnType()->isReferenceType()) << "operator[] should return reference";
}

// Test 27: const operator[]
TEST_F(SubscriptCallOperatorTest, ConstSubscriptOperator) {
    const char *code = R"(
        class ConstArray {
        public:
            int* data;
            const int& operator[](int index) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opSubscript = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ConstArray") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Subscript) {
                        opSubscript = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opSubscript, nullptr) << "const operator[] not found";
    EXPECT_TRUE(opSubscript->isConst()) << "operator[] should be const";
}

// Test 28: operator[] with non-int parameter
TEST_F(SubscriptCallOperatorTest, SubscriptOperatorNonIntIndex) {
    const char *code = R"(
        class StringKey {
        public:
            int value;
        };
        class Map {
        public:
            int& operator[](const StringKey& key);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opSubscript = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Map") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Subscript) {
                        opSubscript = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opSubscript, nullptr) << "operator[] with non-int parameter not found";

    // For reference parameters, check if the referenced type is a record type
    QualType paramType = opSubscript->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType->isRecordType()) << "Parameter should be class type";
}

// Test 29: Overloaded operator[] with different parameter types
TEST_F(SubscriptCallOperatorTest, OverloadedSubscriptOperator) {
    const char *code = R"(
        class MultiArray {
        public:
            int& operator[](int index);
            int& operator[](unsigned int index);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int subscriptOpCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "MultiArray") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Subscript) {
                        subscriptOpCount++;
                    }
                }
            }
        }
    }

    EXPECT_EQ(subscriptOpCount, 2) << "Expected 2 overloaded operator[] methods";
}

// Test 30: operator() - function call operator with no parameters
TEST_F(SubscriptCallOperatorTest, CallOperatorNoParams) {
    const char *code = R"(
        class Functor {
        public:
            int operator()();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opCall = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Functor") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Call) {
                        opCall = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opCall, nullptr) << "operator() not found";
    EXPECT_EQ(opCall->getNumParams(), 0) << "operator() should have 0 parameters";
}

// Test 31: operator() with single parameter
TEST_F(SubscriptCallOperatorTest, CallOperatorSingleParam) {
    const char *code = R"(
        class UnaryFunction {
        public:
            int operator()(int x);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opCall = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "UnaryFunction") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Call) {
                        opCall = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opCall, nullptr) << "operator()(int) not found";
    EXPECT_EQ(opCall->getNumParams(), 1) << "Expected 1 parameter";
}

// Test 32: operator() with multiple parameters
TEST_F(SubscriptCallOperatorTest, CallOperatorMultipleParams) {
    const char *code = R"(
        class BinaryFunction {
        public:
            int operator()(int x, int y);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opCall = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "BinaryFunction") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Call) {
                        opCall = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opCall, nullptr) << "operator()(int, int) not found";
    EXPECT_EQ(opCall->getNumParams(), 2) << "Expected 2 parameters";
}

// Test 33: Overloaded operator() with different signatures
TEST_F(SubscriptCallOperatorTest, OverloadedCallOperator) {
    const char *code = R"(
        class PolyFunction {
        public:
            int operator()(int x);
            double operator()(double x);
            int operator()(int x, int y);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int callOpCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "PolyFunction") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Call) {
                        callOpCount++;
                    }
                }
            }
        }
    }

    EXPECT_EQ(callOpCount, 3) << "Expected 3 overloaded operator() methods";
}

// Test 34: const operator()
TEST_F(SubscriptCallOperatorTest, ConstCallOperator) {
    const char *code = R"(
        class ConstFunctor {
        public:
            int operator()(int x) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opCall = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ConstFunctor") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Call) {
                        opCall = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opCall, nullptr) << "const operator() not found";
    EXPECT_TRUE(opCall->isConst()) << "operator() should be const";
}

// Test 35: operator() for lambda-like behavior
TEST_F(SubscriptCallOperatorTest, LambdaLikeCallOperator) {
    const char *code = R"(
        class Lambda {
        private:
            int captured;
        public:
            Lambda(int x) : captured(x) {}
            int operator()(int y) const { return captured + y; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opCall = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Lambda") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Call) {
                        opCall = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opCall, nullptr) << "Lambda operator() not found";
    EXPECT_TRUE(opCall->hasBody()) << "Lambda operator() should have body";
}

// Test 36: operator() returning reference
TEST_F(SubscriptCallOperatorTest, CallOperatorReturningReference) {
    const char *code = R"(
        class RefReturner {
        public:
            int data;
            int& operator()();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opCall = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "RefReturner") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Call) {
                        opCall = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opCall, nullptr) << "operator() returning reference not found";
    EXPECT_TRUE(opCall->getReturnType()->isReferenceType()) << "Return type should be reference";
}

// Test 37: Both operator[] and operator() in same class
TEST_F(SubscriptCallOperatorTest, BothSubscriptAndCallOperators) {
    const char *code = R"(
        class DualOperator {
        public:
            int& operator[](int index);
            int operator()(int x, int y);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opSubscript = nullptr;
    CXXMethodDecl *opCall = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "DualOperator") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        if (M->getOverloadedOperator() == OO_Subscript) {
                            opSubscript = M;
                        } else if (M->getOverloadedOperator() == OO_Call) {
                            opCall = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(opSubscript, nullptr) << "operator[] not found";
    ASSERT_NE(opCall, nullptr) << "operator() not found";
}

// ============================================================================
// SPECIAL OPERATORS (12 tests)
// ============================================================================

class SpecialOperatorTest : public OperatorOverloadingTestBase {};

// Test 38: operator-> (arrow operator)
TEST_F(SpecialOperatorTest, ArrowOperator) {
    const char *code = R"(
        class Inner {
        public:
            int value;
        };
        class SmartPointer {
        public:
            Inner* ptr;
            Inner* operator->();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opArrow = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "SmartPointer") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Arrow) {
                        opArrow = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opArrow, nullptr) << "operator-> not found";
    EXPECT_TRUE(opArrow->getReturnType()->isPointerType()) << "operator-> should return pointer";
}

// Test 39: const operator->
TEST_F(SpecialOperatorTest, ConstArrowOperator) {
    const char *code = R"(
        class Data {
        public:
            int value;
        };
        class ConstSmartPointer {
        public:
            Data* ptr;
            const Data* operator->() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opArrow = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ConstSmartPointer") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Arrow) {
                        opArrow = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opArrow, nullptr) << "const operator-> not found";
    EXPECT_TRUE(opArrow->isConst()) << "operator-> should be const";
}

// Test 40: Unary operator* (dereference)
TEST_F(SpecialOperatorTest, DereferenceOperator) {
    const char *code = R"(
        class Value {
        public:
            int data;
        };
        class Wrapper {
        public:
            Value* ptr;
            Value& operator*();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opDeref = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Wrapper") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Star && M->getNumParams() == 0) {
                        opDeref = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opDeref, nullptr) << "Unary operator* not found";
    EXPECT_TRUE(opDeref->getReturnType()->isReferenceType()) << "operator* should return reference";
}

// Test 41: const operator*
TEST_F(SpecialOperatorTest, ConstDereferenceOperator) {
    const char *code = R"(
        class Element {
        public:
            int value;
        };
        class ConstWrapper {
        public:
            Element* ptr;
            const Element& operator*() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opDeref = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ConstWrapper") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Star && M->getNumParams() == 0) {
                        opDeref = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opDeref, nullptr) << "const operator* not found";
    EXPECT_TRUE(opDeref->isConst()) << "operator* should be const";
}

// Test 42: Both operator-> and operator* in smart pointer
TEST_F(SpecialOperatorTest, SmartPointerOperators) {
    const char *code = R"(
        class Object {
        public:
            int value;
        };
        class UniquePtr {
        public:
            Object* ptr;
            Object* operator->();
            Object& operator*();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opArrow = nullptr;
    CXXMethodDecl *opDeref = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "UniquePtr") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        if (M->getOverloadedOperator() == OO_Arrow) {
                            opArrow = M;
                        } else if (M->getOverloadedOperator() == OO_Star && M->getNumParams() == 0) {
                            opDeref = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(opArrow, nullptr) << "operator-> not found";
    ASSERT_NE(opDeref, nullptr) << "operator* not found";
}

// Test 43: operator& (address-of)
TEST_F(SpecialOperatorTest, AddressOfOperator) {
    const char *code = R"(
        class AddressWrapper {
        public:
            int* data;
            AddressWrapper* operator&();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opAddress = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "AddressWrapper") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Amp && M->getNumParams() == 0) {
                        opAddress = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opAddress, nullptr) << "operator& not found";
}

// Test 44: operator, (comma operator)
TEST_F(SpecialOperatorTest, CommaOperator) {
    const char *code = R"(
        class Sequence {
        public:
            int value;
            Sequence operator,(const Sequence& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opComma = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Sequence") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Comma) {
                        opComma = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opComma, nullptr) << "operator, not found";
}

// Test 45: Bitwise operators (~, &, |, ^)
TEST_F(SpecialOperatorTest, BitwiseOperators) {
    const char *code = R"(
        class Bits {
        public:
            unsigned int value;
            Bits operator~() const;
            Bits operator&(const Bits& other) const;
            Bits operator|(const Bits& other) const;
            Bits operator^(const Bits& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int bitwiseOpCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Bits") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        auto op = M->getOverloadedOperator();
                        if (op == OO_Tilde || op == OO_Amp || op == OO_Pipe || op == OO_Caret) {
                            bitwiseOpCount++;
                        }
                    }
                }
            }
        }
    }

    EXPECT_EQ(bitwiseOpCount, 4) << "Expected 4 bitwise operators";
}

// Test 46: Shift operators (<<, >>)
TEST_F(SpecialOperatorTest, ShiftOperators) {
    const char *code = R"(
        class ShiftValue {
        public:
            unsigned int value;
            ShiftValue operator<<(int shift) const;
            ShiftValue operator>>(int shift) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLeftShift = nullptr;
    CXXMethodDecl *opRightShift = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ShiftValue") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        if (M->getOverloadedOperator() == OO_LessLess) {
                            opLeftShift = M;
                        } else if (M->getOverloadedOperator() == OO_GreaterGreater) {
                            opRightShift = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(opLeftShift, nullptr) << "operator<< not found";
    ASSERT_NE(opRightShift, nullptr) << "operator>> not found";
}

// Test 47: Logical operators (&&, ||, !)
TEST_F(SpecialOperatorTest, LogicalOperators) {
    const char *code = R"(
        class Bool {
        public:
            bool value;
            bool operator!() const;
            bool operator&&(const Bool& other) const;
            bool operator||(const Bool& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int logicalOpCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Bool") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        auto op = M->getOverloadedOperator();
                        if (op == OO_Exclaim || op == OO_AmpAmp || op == OO_PipePipe) {
                            logicalOpCount++;
                        }
                    }
                }
            }
        }
    }

    EXPECT_EQ(logicalOpCount, 3) << "Expected 3 logical operators";
}

// Test 48: Assignment operator (operator=)
TEST_F(SpecialOperatorTest, AssignmentOperator) {
    const char *code = R"(
        class Assignable {
        public:
            int value;
            Assignable& operator=(const Assignable& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opAssign = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Assignable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Equal) {
                        opAssign = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opAssign, nullptr) << "operator= not found";
    EXPECT_TRUE(opAssign->getReturnType()->isReferenceType()) << "operator= should return reference";
}

// Test 49: Move assignment operator (operator= with rvalue reference)
TEST_F(SpecialOperatorTest, MoveAssignmentOperator) {
    const char *code = R"(
        class Movable {
        public:
            int* data;
            Movable& operator=(Movable&& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opMoveAssign = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Movable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Equal) {
                        if (M->getNumParams() == 1) {
                            QualType paramType = M->getParamDecl(0)->getType();
                            if (paramType->isRValueReferenceType()) {
                                opMoveAssign = M;
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(opMoveAssign, nullptr) << "Move operator= not found";
}

// ============================================================================
// CONVERSION OPERATORS (10 tests)
// ============================================================================

class ConversionOperatorTest : public OperatorOverloadingTestBase {};

// Test 50: Implicit conversion operator (operator int)
TEST_F(ConversionOperatorTest, ImplicitConversionOperator) {
    const char *code = R"(
        class Wrapper {
        public:
            int value;
            operator int() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXConversionDecl *convOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Wrapper") {
                for (auto *M : RD->methods()) {
                    if (auto *Conv = dyn_cast<CXXConversionDecl>(M)) {
                        convOp = Conv;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(convOp, nullptr) << "Conversion operator not found";
    EXPECT_FALSE(convOp->isExplicit()) << "Should be implicit conversion";
}

// Test 51: Explicit conversion operator
TEST_F(ConversionOperatorTest, ExplicitConversionOperator) {
    const char *code = R"(
        class SafeWrapper {
        public:
            int value;
            explicit operator int() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXConversionDecl *convOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "SafeWrapper") {
                for (auto *M : RD->methods()) {
                    if (auto *Conv = dyn_cast<CXXConversionDecl>(M)) {
                        convOp = Conv;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(convOp, nullptr) << "Explicit conversion operator not found";
    EXPECT_TRUE(convOp->isExplicit()) << "Conversion operator should be explicit";
}

// Test 52: Conversion to bool
TEST_F(ConversionOperatorTest, ConversionToBool) {
    const char *code = R"(
        class BoolConvertible {
        public:
            bool valid;
            explicit operator bool() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXConversionDecl *convOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "BoolConvertible") {
                for (auto *M : RD->methods()) {
                    if (auto *Conv = dyn_cast<CXXConversionDecl>(M)) {
                        convOp = Conv;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(convOp, nullptr) << "Conversion to bool not found";
    EXPECT_TRUE(convOp->getConversionType()->isBooleanType()) << "Should convert to bool";
}

// Test 53: Conversion to pointer type
TEST_F(ConversionOperatorTest, ConversionToPointer) {
    const char *code = R"(
        class PointerWrapper {
        public:
            int* data;
            operator int*() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXConversionDecl *convOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "PointerWrapper") {
                for (auto *M : RD->methods()) {
                    if (auto *Conv = dyn_cast<CXXConversionDecl>(M)) {
                        convOp = Conv;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(convOp, nullptr) << "Conversion to pointer not found";
    EXPECT_TRUE(convOp->getConversionType()->isPointerType()) << "Should convert to pointer";
}

// Test 54: Conversion to reference type
TEST_F(ConversionOperatorTest, ConversionToReference) {
    const char *code = R"(
        class RefWrapper {
        public:
            int data;
            operator int&();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXConversionDecl *convOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "RefWrapper") {
                for (auto *M : RD->methods()) {
                    if (auto *Conv = dyn_cast<CXXConversionDecl>(M)) {
                        convOp = Conv;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(convOp, nullptr) << "Conversion to reference not found";
    EXPECT_TRUE(convOp->getConversionType()->isReferenceType()) << "Should convert to reference";
}

// Test 55: Conversion to user-defined type
TEST_F(ConversionOperatorTest, ConversionToUserType) {
    const char *code = R"(
        class Target {
        public:
            int value;
        };
        class Source {
        public:
            int data;
            operator Target() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXConversionDecl *convOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Source") {
                for (auto *M : RD->methods()) {
                    if (auto *Conv = dyn_cast<CXXConversionDecl>(M)) {
                        convOp = Conv;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(convOp, nullptr) << "Conversion to user-defined type not found";
    EXPECT_TRUE(convOp->getConversionType()->isRecordType()) << "Should convert to class type";
}

// Test 56: Multiple conversion operators
TEST_F(ConversionOperatorTest, MultipleConversionOperators) {
    const char *code = R"(
        class MultiConvert {
        public:
            int value;
            operator int() const;
            operator double() const;
            explicit operator bool() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int convOpCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "MultiConvert") {
                for (auto *M : RD->methods()) {
                    if (isa<CXXConversionDecl>(M)) {
                        convOpCount++;
                    }
                }
            }
        }
    }

    EXPECT_EQ(convOpCount, 3) << "Expected 3 conversion operators";
}

// Test 57: Conversion with const correctness
TEST_F(ConversionOperatorTest, ConversionConstCorrectness) {
    const char *code = R"(
        class ConstConvert {
        public:
            int value;
            operator int() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXConversionDecl *convOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ConstConvert") {
                for (auto *M : RD->methods()) {
                    if (auto *Conv = dyn_cast<CXXConversionDecl>(M)) {
                        convOp = Conv;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(convOp, nullptr) << "Const conversion operator not found";
    EXPECT_TRUE(convOp->isConst()) << "Conversion operator should be const";
}

// Test 58: Conversion to const type
TEST_F(ConversionOperatorTest, ConversionToConstType) {
    const char *code = R"(
        class ConstTypeConvert {
        public:
            int* data;
            operator const int*() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXConversionDecl *convOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ConstTypeConvert") {
                for (auto *M : RD->methods()) {
                    if (auto *Conv = dyn_cast<CXXConversionDecl>(M)) {
                        convOp = Conv;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(convOp, nullptr) << "Conversion to const type not found";
    QualType convType = convOp->getConversionType();
    EXPECT_TRUE(convType->isPointerType() && convType->getPointeeType().isConstQualified())
        << "Should convert to const pointer";
}

// Test 59: Conversion operator with body
TEST_F(ConversionOperatorTest, ConversionOperatorWithBody) {
    const char *code = R"(
        class ComputedConversion {
        public:
            int value;
            operator int() const { return value * 2; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXConversionDecl *convOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ComputedConversion") {
                for (auto *M : RD->methods()) {
                    if (auto *Conv = dyn_cast<CXXConversionDecl>(M)) {
                        convOp = Conv;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(convOp, nullptr) << "Conversion operator with body not found";
    EXPECT_TRUE(convOp->hasBody()) << "Conversion operator should have body";
}

// ============================================================================
// STREAM OPERATORS (3 tests)
// ============================================================================

class StreamOperatorTest : public OperatorOverloadingTestBase {};

// Test 60: operator<< for output stream
TEST_F(StreamOperatorTest, OutputStreamOperator) {
    const char *code = R"(
        class OStream {
        public:
            OStream& operator<<(int value);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opOutput = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "OStream") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_LessLess) {
                        opOutput = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opOutput, nullptr) << "operator<< not found";
    EXPECT_TRUE(opOutput->getReturnType()->isReferenceType()) << "operator<< should return reference";
}

// Test 61: operator>> for input stream
TEST_F(StreamOperatorTest, InputStreamOperator) {
    const char *code = R"(
        class IStream {
        public:
            IStream& operator>>(int& value);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opInput = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "IStream") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_GreaterGreater) {
                        opInput = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opInput, nullptr) << "operator>> not found";
}

// Test 62: Friend stream operators
TEST_F(StreamOperatorTest, FriendStreamOperators) {
    const char *code = R"(
        class OStream {
        public:
            OStream& write(const char* s);
        };
        class Printable {
        public:
            int value;
            friend OStream& operator<<(OStream& os, const Printable& p);
        };
        OStream& operator<<(OStream& os, const Printable& p);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *friendOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->isOverloadedOperator() && FD->getOverloadedOperator() == OO_LessLess && FD->getNumParams() == 2) {
                friendOp = FD;
                break;
            }
        }
    }

    ASSERT_NE(friendOp, nullptr) << "Friend operator<< not found";
    EXPECT_EQ(friendOp->getNumParams(), 2) << "Friend operator<< should have 2 parameters";
}

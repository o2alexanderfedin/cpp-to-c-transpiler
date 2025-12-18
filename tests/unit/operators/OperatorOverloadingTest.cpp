// Unit Tests for C++ Operator Overloading Detection
// Stream 4: Comprehensive operator overloading tests for C++ to C transpiler
//
// Tests ensure that C++ operator overloading is correctly detected in the AST.
// These tests validate operator detection, parameter types, const correctness,
// and operator classification - prerequisites for transpilation to C functions.

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include <iostream>
#include <cassert>

using namespace clang;

// Test counter
static int tests_passed = 0;
static int tests_failed = 0;

// Test helper macros
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) { std::cout << "PASS" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "FAIL: " << msg << std::endl; tests_failed++; }
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        TEST_FAIL("", msg); \
        return; \
    }

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

// ============================================================================
// ARITHMETIC OPERATORS (15 tests)
// ============================================================================

// Test 1: Binary + operator
void test_BinaryPlusOperator() {
    TEST_START("BinaryPlusOperator");

    const char *code = R"(
        class Vector2D {
        public:
            int x, y;
            Vector2D operator+(const Vector2D& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opPlus != nullptr, "operator+ not found");
    ASSERT(opPlus->getNumParams() == 1, "operator+ should have 1 parameter");
    ASSERT(opPlus->isConst(), "operator+ should be const");

    TEST_PASS("BinaryPlusOperator");
}

// Test 2: Binary - operator
void test_BinaryMinusOperator() {
    TEST_START("BinaryMinusOperator");

    const char *code = R"(
        class Complex {
        public:
            double real, imag;
            Complex operator-(const Complex& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opMinus != nullptr, "operator- not found");
    ASSERT(opMinus->getNumParams() == 1, "Binary operator- should have 1 parameter");

    TEST_PASS("BinaryMinusOperator");
}

// Test 3: Binary * operator
void test_BinaryMultiplyOperator() {
    TEST_START("BinaryMultiplyOperator");

    const char *code = R"(
        class Matrix {
        public:
            Matrix operator*(const Matrix& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opMul != nullptr, "operator* not found");

    TEST_PASS("BinaryMultiplyOperator");
}

// Test 4: Binary / operator
void test_BinaryDivideOperator() {
    TEST_START("BinaryDivideOperator");

    const char *code = R"(
        class Fraction {
        public:
            int numerator, denominator;
            Fraction operator/(const Fraction& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opDiv != nullptr, "operator/ not found");

    TEST_PASS("BinaryDivideOperator");
}

// Test 5: Binary % operator
void test_BinaryModuloOperator() {
    TEST_START("BinaryModuloOperator");

    const char *code = R"(
        class Integer {
        public:
            int value;
            Integer operator%(const Integer& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opMod != nullptr, "operator% not found");

    TEST_PASS("BinaryModuloOperator");
}

// Test 6: Unary - operator
void test_UnaryMinusOperator() {
    TEST_START("UnaryMinusOperator");

    const char *code = R"(
        class Number {
        public:
            double value;
            Number operator-() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opUnaryMinus != nullptr, "Unary operator- not found");
    ASSERT(opUnaryMinus->getNumParams() == 0, "Unary operator- should have 0 parameters");

    TEST_PASS("UnaryMinusOperator");
}

// Test 7: Unary + operator
void test_UnaryPlusOperator() {
    TEST_START("UnaryPlusOperator");

    const char *code = R"(
        class SignedInt {
        public:
            int value;
            SignedInt operator+() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opUnaryPlus != nullptr, "Unary operator+ not found");
    ASSERT(opUnaryPlus->getNumParams() == 0, "Unary operator+ should have 0 parameters");

    TEST_PASS("UnaryPlusOperator");
}

// Test 8: Prefix ++ operator
void test_PrefixIncrementOperator() {
    TEST_START("PrefixIncrementOperator");

    const char *code = R"(
        class Counter {
        public:
            int count;
            Counter& operator++();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opPrefixInc != nullptr, "Prefix operator++ not found");
    ASSERT(opPrefixInc->getReturnType()->isReferenceType(), "Prefix operator++ should return reference");

    TEST_PASS("PrefixIncrementOperator");
}

// Test 9: Postfix ++ operator
void test_PostfixIncrementOperator() {
    TEST_START("PostfixIncrementOperator");

    const char *code = R"(
        class Iterator {
        public:
            int position;
            Iterator operator++(int);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opPostfixInc != nullptr, "Postfix operator++ not found");
    ASSERT(opPostfixInc->getNumParams() == 1, "Postfix operator++ should have dummy int parameter");

    TEST_PASS("PostfixIncrementOperator");
}

// Test 10: Prefix -- operator
void test_PrefixDecrementOperator() {
    TEST_START("PrefixDecrementOperator");

    const char *code = R"(
        class Countdown {
        public:
            int value;
            Countdown& operator--();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opPrefixDec != nullptr, "Prefix operator-- not found");

    TEST_PASS("PrefixDecrementOperator");
}

// Test 11: Postfix -- operator
void test_PostfixDecrementOperator() {
    TEST_START("PostfixDecrementOperator");

    const char *code = R"(
        class ReverseIterator {
        public:
            int position;
            ReverseIterator operator--(int);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opPostfixDec != nullptr, "Postfix operator-- not found");

    TEST_PASS("PostfixDecrementOperator");
}

// Test 12: Compound += operator
void test_CompoundPlusAssignOperator() {
    TEST_START("CompoundPlusAssignOperator");

    const char *code = R"(
        class Accumulator {
        public:
            int total;
            Accumulator& operator+=(const Accumulator& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opPlusAssign != nullptr, "operator+= not found");

    TEST_PASS("CompoundPlusAssignOperator");
}

// Test 13: Compound -= operator
void test_CompoundMinusAssignOperator() {
    TEST_START("CompoundMinusAssignOperator");

    const char *code = R"(
        class Balance {
        public:
            double amount;
            Balance& operator-=(const Balance& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opMinusAssign != nullptr, "operator-= not found");

    TEST_PASS("CompoundMinusAssignOperator");
}

// Test 14: Compound *= operator
void test_CompoundMultiplyAssignOperator() {
    TEST_START("CompoundMultiplyAssignOperator");

    const char *code = R"(
        class Scale {
        public:
            double factor;
            Scale& operator*=(const Scale& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opMulAssign != nullptr, "operator*= not found");

    TEST_PASS("CompoundMultiplyAssignOperator");
}

// Test 15: Compound /= operator
void test_CompoundDivideAssignOperator() {
    TEST_START("CompoundDivideAssignOperator");

    const char *code = R"(
        class Ratio {
        public:
            double value;
            Ratio& operator/=(const Ratio& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opDivAssign != nullptr, "operator/= not found");

    TEST_PASS("CompoundDivideAssignOperator");
}

// ============================================================================
// COMPARISON OPERATORS (10 tests)
// ============================================================================

// Test 16: operator==
void test_EqualityOperator() {
    TEST_START("EqualityOperator");

    const char *code = R"(
        class Point {
        public:
            int x, y;
            bool operator==(const Point& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opEqual != nullptr, "operator== not found");
    ASSERT(opEqual->getReturnType()->isBooleanType(), "operator== should return bool");

    TEST_PASS("EqualityOperator");
}

// Test 17: operator!=
void test_InequalityOperator() {
    TEST_START("InequalityOperator");

    const char *code = R"(
        class String {
        public:
            char* data;
            bool operator!=(const String& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opNotEqual != nullptr, "operator!= not found");

    TEST_PASS("InequalityOperator");
}

// Test 18: operator<
void test_LessThanOperator() {
    TEST_START("LessThanOperator");

    const char *code = R"(
        class ComparableInt {
        public:
            int value;
            bool operator<(const ComparableInt& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opLess != nullptr, "operator< not found");

    TEST_PASS("LessThanOperator");
}

// Test 19: operator>
void test_GreaterThanOperator() {
    TEST_START("GreaterThanOperator");

    const char *code = R"(
        class Priority {
        public:
            int level;
            bool operator>(const Priority& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opGreater != nullptr, "operator> not found");

    TEST_PASS("GreaterThanOperator");
}

// Test 20: operator<=
void test_LessOrEqualOperator() {
    TEST_START("LessOrEqualOperator");

    const char *code = R"(
        class Version {
        public:
            int major, minor;
            bool operator<=(const Version& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opLessEqual != nullptr, "operator<= not found");

    TEST_PASS("LessOrEqualOperator");
}

// Test 21: operator>=
void test_GreaterOrEqualOperator() {
    TEST_START("GreaterOrEqualOperator");

    const char *code = R"(
        class Score {
        public:
            double points;
            bool operator>=(const Score& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opGreaterEqual != nullptr, "operator>= not found");

    TEST_PASS("GreaterOrEqualOperator");
}

// Test 22: Multiple comparison operators in same class
void test_MultipleComparisonOperators() {
    TEST_START("MultipleComparisonOperators");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(operatorCount == 4, "Expected 4 comparison operators");

    TEST_PASS("MultipleComparisonOperators");
}

// Test 23: Comparison with different parameter types
void test_ComparisonWithDifferentTypes() {
    TEST_START("ComparisonWithDifferentTypes");

    const char *code = R"(
        class Mixed {
        public:
            int value;
            bool operator==(int other) const;
            bool operator==(const Mixed& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opEqualInt != nullptr, "operator==(int) not found");
    ASSERT(opEqualMixed != nullptr, "operator==(const Mixed&) not found");

    TEST_PASS("ComparisonWithDifferentTypes");
}

// Test 24: Friend comparison operators
void test_FriendComparisonOperators() {
    TEST_START("FriendComparisonOperators");

    const char *code = R"(
        class Value {
        public:
            int data;
            friend bool operator==(const Value& a, const Value& b);
        };
        bool operator==(const Value& a, const Value& b);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(friendOp != nullptr, "Friend operator== not found");
    ASSERT(friendOp->getNumParams() == 2, "Friend operator== should have 2 parameters");

    TEST_PASS("FriendComparisonOperators");
}

// Test 25: Const correctness in comparison operators
void test_ConstCorrectnessComparison() {
    TEST_START("ConstCorrectnessComparison");

    const char *code = R"(
        class ConstTest {
        public:
            int value;
            bool operator<(const ConstTest& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opLess != nullptr, "operator< not found");
    ASSERT(opLess->isConst(), "Comparison operator should be const");

    // For reference parameters, check if the referenced type is const-qualified
    QualType paramType = opLess->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    ASSERT(paramType.isConstQualified(), "Parameter should be const");

    TEST_PASS("ConstCorrectnessComparison");
}

// ============================================================================
// SUBSCRIPT & CALL OPERATORS (12 tests)
// ============================================================================

// Test 26: operator[] - array subscript
void test_SubscriptOperator() {
    TEST_START("SubscriptOperator");

    const char *code = R"(
        class Array {
        public:
            int* data;
            int& operator[](int index);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opSubscript != nullptr, "operator[] not found");
    ASSERT(opSubscript->getReturnType()->isReferenceType(), "operator[] should return reference");

    TEST_PASS("SubscriptOperator");
}

// Test 27: const operator[]
void test_ConstSubscriptOperator() {
    TEST_START("ConstSubscriptOperator");

    const char *code = R"(
        class ConstArray {
        public:
            int* data;
            const int& operator[](int index) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opSubscript != nullptr, "const operator[] not found");
    ASSERT(opSubscript->isConst(), "operator[] should be const");

    TEST_PASS("ConstSubscriptOperator");
}

// Test 28: operator[] with non-int parameter
void test_SubscriptOperatorNonIntIndex() {
    TEST_START("SubscriptOperatorNonIntIndex");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opSubscript != nullptr, "operator[] with non-int parameter not found");

    // For reference parameters, check if the referenced type is a record type
    QualType paramType = opSubscript->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    ASSERT(paramType->isRecordType(), "Parameter should be class type");

    TEST_PASS("SubscriptOperatorNonIntIndex");
}

// Test 29: Overloaded operator[] with different parameter types
void test_OverloadedSubscriptOperator() {
    TEST_START("OverloadedSubscriptOperator");

    const char *code = R"(
        class MultiArray {
        public:
            int& operator[](int index);
            int& operator[](unsigned int index);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(subscriptOpCount == 2, "Expected 2 overloaded operator[] methods");

    TEST_PASS("OverloadedSubscriptOperator");
}

// Test 30: operator() - function call operator with no parameters
void test_CallOperatorNoParams() {
    TEST_START("CallOperatorNoParams");

    const char *code = R"(
        class Functor {
        public:
            int operator()();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opCall != nullptr, "operator() not found");
    ASSERT(opCall->getNumParams() == 0, "operator() should have 0 parameters");

    TEST_PASS("CallOperatorNoParams");
}

// Test 31: operator() with single parameter
void test_CallOperatorSingleParam() {
    TEST_START("CallOperatorSingleParam");

    const char *code = R"(
        class UnaryFunction {
        public:
            int operator()(int x);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opCall != nullptr, "operator()(int) not found");
    ASSERT(opCall->getNumParams() == 1, "Expected 1 parameter");

    TEST_PASS("CallOperatorSingleParam");
}

// Test 32: operator() with multiple parameters
void test_CallOperatorMultipleParams() {
    TEST_START("CallOperatorMultipleParams");

    const char *code = R"(
        class BinaryFunction {
        public:
            int operator()(int x, int y);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opCall != nullptr, "operator()(int, int) not found");
    ASSERT(opCall->getNumParams() == 2, "Expected 2 parameters");

    TEST_PASS("CallOperatorMultipleParams");
}

// Test 33: Overloaded operator() with different signatures
void test_OverloadedCallOperator() {
    TEST_START("OverloadedCallOperator");

    const char *code = R"(
        class PolyFunction {
        public:
            int operator()(int x);
            double operator()(double x);
            int operator()(int x, int y);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(callOpCount == 3, "Expected 3 overloaded operator() methods");

    TEST_PASS("OverloadedCallOperator");
}

// Test 34: const operator()
void test_ConstCallOperator() {
    TEST_START("ConstCallOperator");

    const char *code = R"(
        class ConstFunctor {
        public:
            int operator()(int x) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opCall != nullptr, "const operator() not found");
    ASSERT(opCall->isConst(), "operator() should be const");

    TEST_PASS("ConstCallOperator");
}

// Test 35: operator() for lambda-like behavior
void test_LambdaLikeCallOperator() {
    TEST_START("LambdaLikeCallOperator");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opCall != nullptr, "Lambda operator() not found");
    ASSERT(opCall->hasBody(), "Lambda operator() should have body");

    TEST_PASS("LambdaLikeCallOperator");
}

// Test 36: operator() returning reference
void test_CallOperatorReturningReference() {
    TEST_START("CallOperatorReturningReference");

    const char *code = R"(
        class RefReturner {
        public:
            int data;
            int& operator()();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opCall != nullptr, "operator() returning reference not found");
    ASSERT(opCall->getReturnType()->isReferenceType(), "Return type should be reference");

    TEST_PASS("CallOperatorReturningReference");
}

// Test 37: Both operator[] and operator() in same class
void test_BothSubscriptAndCallOperators() {
    TEST_START("BothSubscriptAndCallOperators");

    const char *code = R"(
        class DualOperator {
        public:
            int& operator[](int index);
            int operator()(int x, int y);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opSubscript != nullptr, "operator[] not found");
    ASSERT(opCall != nullptr, "operator() not found");

    TEST_PASS("BothSubscriptAndCallOperators");
}

// ============================================================================
// SPECIAL OPERATORS (12 tests)
// ============================================================================

// Test 38: operator-> (arrow operator)
void test_ArrowOperator() {
    TEST_START("ArrowOperator");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opArrow != nullptr, "operator-> not found");
    ASSERT(opArrow->getReturnType()->isPointerType(), "operator-> should return pointer");

    TEST_PASS("ArrowOperator");
}

// Test 39: const operator->
void test_ConstArrowOperator() {
    TEST_START("ConstArrowOperator");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opArrow != nullptr, "const operator-> not found");
    ASSERT(opArrow->isConst(), "operator-> should be const");

    TEST_PASS("ConstArrowOperator");
}

// Test 40: Unary operator* (dereference)
void test_DereferenceOperator() {
    TEST_START("DereferenceOperator");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opDeref != nullptr, "Unary operator* not found");
    ASSERT(opDeref->getReturnType()->isReferenceType(), "operator* should return reference");

    TEST_PASS("DereferenceOperator");
}

// Test 41: const operator*
void test_ConstDereferenceOperator() {
    TEST_START("ConstDereferenceOperator");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opDeref != nullptr, "const operator* not found");
    ASSERT(opDeref->isConst(), "operator* should be const");

    TEST_PASS("ConstDereferenceOperator");
}

// Test 42: Both operator-> and operator* in smart pointer
void test_SmartPointerOperators() {
    TEST_START("SmartPointerOperators");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opArrow != nullptr, "operator-> not found");
    ASSERT(opDeref != nullptr, "operator* not found");

    TEST_PASS("SmartPointerOperators");
}

// Test 43: operator& (address-of)
void test_AddressOfOperator() {
    TEST_START("AddressOfOperator");

    const char *code = R"(
        class AddressWrapper {
        public:
            int* data;
            AddressWrapper* operator&();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opAddress != nullptr, "operator& not found");

    TEST_PASS("AddressOfOperator");
}

// Test 44: operator, (comma operator)
void test_CommaOperator() {
    TEST_START("CommaOperator");

    const char *code = R"(
        class Sequence {
        public:
            int value;
            Sequence operator,(const Sequence& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opComma != nullptr, "operator, not found");

    TEST_PASS("CommaOperator");
}

// Test 45: Bitwise operators (~, &, |, ^)
void test_BitwiseOperators() {
    TEST_START("BitwiseOperators");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(bitwiseOpCount == 4, "Expected 4 bitwise operators");

    TEST_PASS("BitwiseOperators");
}

// Test 46: Shift operators (<<, >>)
void test_ShiftOperators() {
    TEST_START("ShiftOperators");

    const char *code = R"(
        class ShiftValue {
        public:
            unsigned int value;
            ShiftValue operator<<(int shift) const;
            ShiftValue operator>>(int shift) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opLeftShift != nullptr, "operator<< not found");
    ASSERT(opRightShift != nullptr, "operator>> not found");

    TEST_PASS("ShiftOperators");
}

// Test 47: Logical operators (&&, ||, !)
void test_LogicalOperators() {
    TEST_START("LogicalOperators");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(logicalOpCount == 3, "Expected 3 logical operators");

    TEST_PASS("LogicalOperators");
}

// Test 48: Assignment operator (operator=)
void test_AssignmentOperator() {
    TEST_START("AssignmentOperator");

    const char *code = R"(
        class Assignable {
        public:
            int value;
            Assignable& operator=(const Assignable& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opAssign != nullptr, "operator= not found");
    ASSERT(opAssign->getReturnType()->isReferenceType(), "operator= should return reference");

    TEST_PASS("AssignmentOperator");
}

// Test 49: Move assignment operator (operator= with rvalue reference)
void test_MoveAssignmentOperator() {
    TEST_START("MoveAssignmentOperator");

    const char *code = R"(
        class Movable {
        public:
            int* data;
            Movable& operator=(Movable&& other);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opMoveAssign != nullptr, "Move operator= not found");

    TEST_PASS("MoveAssignmentOperator");
}

// ============================================================================
// CONVERSION OPERATORS (10 tests)
// ============================================================================

// Test 50: Implicit conversion operator (operator int)
void test_ImplicitConversionOperator() {
    TEST_START("ImplicitConversionOperator");

    const char *code = R"(
        class Wrapper {
        public:
            int value;
            operator int() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(convOp != nullptr, "Conversion operator not found");
    ASSERT(!convOp->isExplicit(), "Should be implicit conversion");

    TEST_PASS("ImplicitConversionOperator");
}

// Test 51: Explicit conversion operator
void test_ExplicitConversionOperator() {
    TEST_START("ExplicitConversionOperator");

    const char *code = R"(
        class SafeWrapper {
        public:
            int value;
            explicit operator int() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(convOp != nullptr, "Explicit conversion operator not found");
    ASSERT(convOp->isExplicit(), "Conversion operator should be explicit");

    TEST_PASS("ExplicitConversionOperator");
}

// Test 52: Conversion to bool
void test_ConversionToBool() {
    TEST_START("ConversionToBool");

    const char *code = R"(
        class BoolConvertible {
        public:
            bool valid;
            explicit operator bool() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(convOp != nullptr, "Conversion to bool not found");
    ASSERT(convOp->getConversionType()->isBooleanType(), "Should convert to bool");

    TEST_PASS("ConversionToBool");
}

// Test 53: Conversion to pointer type
void test_ConversionToPointer() {
    TEST_START("ConversionToPointer");

    const char *code = R"(
        class PointerWrapper {
        public:
            int* data;
            operator int*() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(convOp != nullptr, "Conversion to pointer not found");
    ASSERT(convOp->getConversionType()->isPointerType(), "Should convert to pointer");

    TEST_PASS("ConversionToPointer");
}

// Test 54: Conversion to reference type
void test_ConversionToReference() {
    TEST_START("ConversionToReference");

    const char *code = R"(
        class RefWrapper {
        public:
            int data;
            operator int&();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(convOp != nullptr, "Conversion to reference not found");
    ASSERT(convOp->getConversionType()->isReferenceType(), "Should convert to reference");

    TEST_PASS("ConversionToReference");
}

// Test 55: Conversion to user-defined type
void test_ConversionToUserType() {
    TEST_START("ConversionToUserType");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(convOp != nullptr, "Conversion to user-defined type not found");
    ASSERT(convOp->getConversionType()->isRecordType(), "Should convert to class type");

    TEST_PASS("ConversionToUserType");
}

// Test 56: Multiple conversion operators
void test_MultipleConversionOperators() {
    TEST_START("MultipleConversionOperators");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(convOpCount == 3, "Expected 3 conversion operators");

    TEST_PASS("MultipleConversionOperators");
}

// Test 57: Conversion with const correctness
void test_ConversionConstCorrectness() {
    TEST_START("ConversionConstCorrectness");

    const char *code = R"(
        class ConstConvert {
        public:
            int value;
            operator int() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(convOp != nullptr, "Const conversion operator not found");
    ASSERT(convOp->isConst(), "Conversion operator should be const");

    TEST_PASS("ConversionConstCorrectness");
}

// Test 58: Conversion to const type
void test_ConversionToConstType() {
    TEST_START("ConversionToConstType");

    const char *code = R"(
        class ConstTypeConvert {
        public:
            int* data;
            operator const int*() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(convOp != nullptr, "Conversion to const type not found");
    QualType convType = convOp->getConversionType();
    ASSERT(convType->isPointerType() && convType->getPointeeType().isConstQualified(),
           "Should convert to const pointer");

    TEST_PASS("ConversionToConstType");
}

// Test 59: Conversion operator with body
void test_ConversionOperatorWithBody() {
    TEST_START("ConversionOperatorWithBody");

    const char *code = R"(
        class ComputedConversion {
        public:
            int value;
            operator int() const { return value * 2; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(convOp != nullptr, "Conversion operator with body not found");
    ASSERT(convOp->hasBody(), "Conversion operator should have body");

    TEST_PASS("ConversionOperatorWithBody");
}

// ============================================================================
// STREAM OPERATORS (3 tests)
// ============================================================================

// Test 60: operator<< for output stream
void test_OutputStreamOperator() {
    TEST_START("OutputStreamOperator");

    const char *code = R"(
        class OStream {
        public:
            OStream& operator<<(int value);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opOutput != nullptr, "operator<< not found");
    ASSERT(opOutput->getReturnType()->isReferenceType(), "operator<< should return reference");

    TEST_PASS("OutputStreamOperator");
}

// Test 61: operator>> for input stream
void test_InputStreamOperator() {
    TEST_START("InputStreamOperator");

    const char *code = R"(
        class IStream {
        public:
            IStream& operator>>(int& value);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(opInput != nullptr, "operator>> not found");

    TEST_PASS("InputStreamOperator");
}

// Test 62: Friend stream operators
void test_FriendStreamOperators() {
    TEST_START("FriendStreamOperators");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(friendOp != nullptr, "Friend operator<< not found");
    ASSERT(friendOp->getNumParams() == 2, "Friend operator<< should have 2 parameters");

    TEST_PASS("FriendStreamOperators");
}

// ============================================================================
// MAIN TEST RUNNER
// ============================================================================

int main() {
    std::cout << "===============================================" << std::endl;
    std::cout << "C++ Operator Overloading Detection Test Suite" << std::endl;
    std::cout << "Stream 4: Comprehensive Operator Tests (62 tests)" << std::endl;
    std::cout << "===============================================" << std::endl;
    std::cout << std::endl;

    std::cout << "--- ARITHMETIC OPERATORS (15 tests) ---" << std::endl;
    test_BinaryPlusOperator();
    test_BinaryMinusOperator();
    test_BinaryMultiplyOperator();
    test_BinaryDivideOperator();
    test_BinaryModuloOperator();
    test_UnaryMinusOperator();
    test_UnaryPlusOperator();
    test_PrefixIncrementOperator();
    test_PostfixIncrementOperator();
    test_PrefixDecrementOperator();
    test_PostfixDecrementOperator();
    test_CompoundPlusAssignOperator();
    test_CompoundMinusAssignOperator();
    test_CompoundMultiplyAssignOperator();
    test_CompoundDivideAssignOperator();

    std::cout << std::endl;
    std::cout << "--- COMPARISON OPERATORS (10 tests) ---" << std::endl;
    test_EqualityOperator();
    test_InequalityOperator();
    test_LessThanOperator();
    test_GreaterThanOperator();
    test_LessOrEqualOperator();
    test_GreaterOrEqualOperator();
    test_MultipleComparisonOperators();
    test_ComparisonWithDifferentTypes();
    test_FriendComparisonOperators();
    test_ConstCorrectnessComparison();

    std::cout << std::endl;
    std::cout << "--- SUBSCRIPT & CALL OPERATORS (12 tests) ---" << std::endl;
    test_SubscriptOperator();
    test_ConstSubscriptOperator();
    test_SubscriptOperatorNonIntIndex();
    test_OverloadedSubscriptOperator();
    test_CallOperatorNoParams();
    test_CallOperatorSingleParam();
    test_CallOperatorMultipleParams();
    test_OverloadedCallOperator();
    test_ConstCallOperator();
    test_LambdaLikeCallOperator();
    test_CallOperatorReturningReference();
    test_BothSubscriptAndCallOperators();

    std::cout << std::endl;
    std::cout << "--- SPECIAL OPERATORS (12 tests) ---" << std::endl;
    test_ArrowOperator();
    test_ConstArrowOperator();
    test_DereferenceOperator();
    test_ConstDereferenceOperator();
    test_SmartPointerOperators();
    test_AddressOfOperator();
    test_CommaOperator();
    test_BitwiseOperators();
    test_ShiftOperators();
    test_LogicalOperators();
    test_AssignmentOperator();
    test_MoveAssignmentOperator();

    std::cout << std::endl;
    std::cout << "--- CONVERSION OPERATORS (10 tests) ---" << std::endl;
    test_ImplicitConversionOperator();
    test_ExplicitConversionOperator();
    test_ConversionToBool();
    test_ConversionToPointer();
    test_ConversionToReference();
    test_ConversionToUserType();
    test_MultipleConversionOperators();
    test_ConversionConstCorrectness();
    test_ConversionToConstType();
    test_ConversionOperatorWithBody();

    std::cout << std::endl;
    std::cout << "--- STREAM OPERATORS (3 tests) ---" << std::endl;
    test_OutputStreamOperator();
    test_InputStreamOperator();
    test_FriendStreamOperators();

    std::cout << std::endl;
    std::cout << "===============================================" << std::endl;
    std::cout << "Test Results:" << std::endl;
    std::cout << "  PASSED: " << tests_passed << std::endl;
    std::cout << "  FAILED: " << tests_failed << std::endl;
    std::cout << "  TOTAL:  " << (tests_passed + tests_failed) << std::endl;
    std::cout << "===============================================" << std::endl;

    return tests_failed > 0 ? 1 : 0;
}

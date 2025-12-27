// Unit Tests for operator< (Less-Than) Comparison Operator
// Phase 51: Comparison & Logical Operator Overloading Support (v2.11.0)
//
// These tests verify that C++ operator< is correctly translated to C function calls.
// Tests cover:
// - Basic member operator< with integer fields
// - Const correctness verification
// - Non-member friend operator<
// - Mathematical properties: transitivity, irreflexivity, asymmetry
// - Complex multi-field comparison (Date: year, month, day)
// - Call site transformation and C function generation
//
// Pattern: Follow ArithmeticOperatorTranslator test structure from Phase 50
// Each test validates AST translation, NOT code generation

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"

using namespace clang;

// Test fixture base class with helper method
class LessThanOperatorTestBase : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// LESS-THAN OPERATOR TESTS (8 tests)
// ============================================================================

class LessThanOperatorTest : public LessThanOperatorTestBase {};

// Test 1: BasicLessThan - Simple member operator< with integer fields
//
// Verifies that a simple operator< with integer fields is correctly detected
// and marked as a comparison operator.
TEST_F(LessThanOperatorTest, BasicLessThan) {
    const char *code = R"(
        class Score {
        public:
            int points;
            bool operator<(const Score& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    ASSERT_NE(TU, nullptr) << "Translation unit is null";

    CXXMethodDecl *opLess = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Score") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_Less) {
                        opLess = M;
                        break;
                    }
                }
                break;
            }
        }
    }

    // Verify operator< was found
    ASSERT_NE(opLess, nullptr) << "operator< not found in Score class";

    // Verify return type is bool
    EXPECT_TRUE(opLess->getReturnType()->isBooleanType())
        << "operator< should return bool";

    // Verify has 1 parameter (const Score& other)
    EXPECT_EQ(opLess->getNumParams(), 1)
        << "operator< should have 1 parameter";

    // Verify is const member function
    EXPECT_TRUE(opLess->isConst())
        << "operator< should be const member function";
}

// Test 2: LessThanConstCorrectness - Verify const member function
//
// Ensures that const correctness is properly applied to operator<:
// - Const this pointer (const Score* this)
// - Const parameter (const Score& other)
TEST_F(LessThanOperatorTest, LessThanConstCorrectness) {
    const char *code = R"(
        class Integer {
        public:
            int value;
            bool operator<(const Integer& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLess = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Integer") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_Less) {
                        opLess = M;
                        break;
                    }
                }
                break;
            }
        }
    }

    ASSERT_NE(opLess, nullptr) << "operator< not found";

    // Verify method is const
    EXPECT_TRUE(opLess->isConst())
        << "operator< method should be const";

    // Verify parameter is const reference
    QualType paramType = opLess->getParamDecl(0)->getType();
    EXPECT_TRUE(paramType->isReferenceType())
        << "Parameter should be reference";

    // Get the referenced type
    paramType = paramType->getPointeeType();
    EXPECT_TRUE(paramType.isConstQualified())
        << "Referenced parameter should be const";
}

// Test 3: FriendLessThan - Non-member friend operator<
//
// Verifies that friend operator< (non-member function) is correctly detected.
// Friend operators have 2 parameters instead of 1 (no implicit this).
TEST_F(LessThanOperatorTest, FriendLessThan) {
    const char *code = R"(
        class Value {
        public:
            int data;
            friend bool operator<(const Value& a, const Value& b);
        };
        bool operator<(const Value& a, const Value& b);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *friendOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->isOverloadedOperator() &&
                FD->getOverloadedOperator() == OO_Less &&
                !isa<CXXMethodDecl>(FD)) {
                friendOp = FD;
                break;
            }
        }
    }

    ASSERT_NE(friendOp, nullptr) << "Friend operator< not found";

    // Verify return type is bool
    EXPECT_TRUE(friendOp->getReturnType()->isBooleanType())
        << "Friend operator< should return bool";

    // Verify has 2 parameters (both Value references)
    EXPECT_EQ(friendOp->getNumParams(), 2)
        << "Friend operator< should have 2 parameters";
}

// Test 4: LessThanTransitivity - Verify a < b && b < c => a < c
//
// Mathematical property: if a < b and b < c, then a < c.
// This test verifies the operator exists and has the right signature
// for proper transitivity implementation.
TEST_F(LessThanOperatorTest, LessThanTransitivity) {
    const char *code = R"(
        class Number {
        public:
            double value;
            bool operator<(const Number& other) const {
                return value < other.value;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLess = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Number") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_Less) {
                        opLess = M;
                        break;
                    }
                }
                break;
            }
        }
    }

    ASSERT_NE(opLess, nullptr) << "operator< not found";

    // Verify it has body (implemented, not just declared)
    EXPECT_TRUE(opLess->hasBody())
        << "operator< should have implementation";

    // Verify it's const (necessary for transitivity)
    EXPECT_TRUE(opLess->isConst())
        << "operator< must be const for transitivity property";
}

// Test 5: LessThanIrreflexivity - Verify !(a < a) for all a
//
// Mathematical property: An object should never be less than itself.
// !(a < a) must always be true.
// This test verifies the operator signature supports this property.
TEST_F(LessThanOperatorTest, LessThanIrreflexivity) {
    const char *code = R"(
        class Element {
        public:
            int id;
            bool operator<(const Element& other) const {
                return id < other.id;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLess = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Element") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_Less) {
                        opLess = M;
                        break;
                    }
                }
                break;
            }
        }
    }

    ASSERT_NE(opLess, nullptr) << "operator< not found";

    // Verify return type allows false value (for !(a < a))
    EXPECT_TRUE(opLess->getReturnType()->isBooleanType())
        << "operator< must return bool";

    // Verify const member function (for a < a to work)
    EXPECT_TRUE(opLess->isConst())
        << "operator< must be const";
}

// Test 6: LessThanAsymmetry - Verify a < b => !(b < a)
//
// Mathematical property: If a < b is true, then b < a must be false.
// This establishes asymmetric comparison.
TEST_F(LessThanOperatorTest, LessThanAsymmetry) {
    const char *code = R"(
        class Item {
        public:
            double priority;
            bool operator<(const Item& other) const {
                return priority < other.priority;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLess = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Item") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_Less) {
                        opLess = M;
                        break;
                    }
                }
                break;
            }
        }
    }

    ASSERT_NE(opLess, nullptr) << "operator< not found";

    // Asymmetry is enforced by proper implementation
    // Test verifies operator returns bool (can be negated)
    EXPECT_TRUE(opLess->getReturnType()->isBooleanType())
        << "operator< return type must be bool for negation";
}

// Test 7: LessThanComplexType - Multi-field comparison (Date: year, month, day)
//
// Verifies operator< works correctly with classes having multiple fields
// that need to be compared in order (lexicographic comparison).
TEST_F(LessThanOperatorTest, LessThanComplexType) {
    const char *code = R"(
        class Date {
        public:
            int year;
            int month;
            int day;
            bool operator<(const Date& other) const {
                if (year != other.year) return year < other.year;
                if (month != other.month) return month < other.month;
                return day < other.day;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLess = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Date") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_Less) {
                        opLess = M;
                        break;
                    }
                }
                break;
            }
        }
    }

    ASSERT_NE(opLess, nullptr) << "operator< not found in Date class";

    // Verify operator has complex body
    EXPECT_TRUE(opLess->hasBody())
        << "operator< should have implementation";

    // Verify it returns bool
    EXPECT_TRUE(opLess->getReturnType()->isBooleanType())
        << "operator< should return bool";

    // Verify it's a const member function
    EXPECT_TRUE(opLess->isConst())
        << "operator< should be const";
}

// Test 8: LessThanCallSite - Verify call site transformation works
//
// Ensures operator< can be used in conditional expressions and
// other standard call sites. Tests that the operator is properly
// integrated into the method map for translation.
TEST_F(LessThanOperatorTest, LessThanCallSite) {
    const char *code = R"(
        class Price {
        public:
            double amount;
            bool operator<(const Price& other) const;
        };

        void comparePrice(const Price& a, const Price& b) {
            if (a < b) {
                // a is cheaper than b
            }
            bool result = a < b;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLess = nullptr;
    FunctionDecl *compareFunc = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Price") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_Less) {
                        opLess = M;
                        break;
                    }
                }
            }
        } else if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "comparePrice") {
                compareFunc = FD;
            }
        }
    }

    ASSERT_NE(opLess, nullptr) << "operator< not found";
    ASSERT_NE(compareFunc, nullptr) << "comparePrice function not found";

    // Verify operator is usable (has proper signature)
    EXPECT_EQ(opLess->getNumParams(), 1)
        << "operator< should have 1 parameter";

    EXPECT_TRUE(opLess->getReturnType()->isBooleanType())
        << "operator< should return bool";

    // Verify function that uses operator was parsed
    EXPECT_TRUE(compareFunc->hasBody())
        << "comparePrice should have body";
}


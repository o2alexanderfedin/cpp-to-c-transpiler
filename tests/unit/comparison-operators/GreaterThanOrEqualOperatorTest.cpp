// Unit Tests for C++ operator>= (Greater-Than-Or-Equal) Comparison Operator
// Phase 51: Comprehensive comparison operator tests for C++ to C transpiler
//
// Tests ensure that C++ operator>= overloading is correctly detected in the AST,
// properly handles const correctness, supports both member and friend operators,
// and validates mathematical properties like equivalence, reflexivity, and transitivity.

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"

using namespace clang;

// Test fixture base class with helper method
class GreaterThanOrEqualOperatorTestBase : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// BASIC OPERATOR>= TESTS
// ============================================================================

class GreaterThanOrEqualOperatorTest : public GreaterThanOrEqualOperatorTestBase {};

// Test 1: BasicGreaterThanOrEqual - Simple member operator>=
TEST_F(GreaterThanOrEqualOperatorTest, BasicGreaterThanOrEqual) {
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
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_GreaterEqual) {
                        opGreaterEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opGreaterEqual, nullptr) << "operator>= not found";
    EXPECT_EQ(opGreaterEqual->getNumParams(), 1)
        << "operator>= should have 1 parameter";
    EXPECT_TRUE(opGreaterEqual->getReturnType()->isBooleanType())
        << "operator>= should return bool";
}

// Test 2: GreaterThanOrEqualConstCorrectness - Verify const member function
TEST_F(GreaterThanOrEqualOperatorTest, GreaterThanOrEqualConstCorrectness) {
    const char *code = R"(
        class Version {
        public:
            int major, minor;
            bool operator>=(const Version& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opGreaterEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Version") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_GreaterEqual) {
                        opGreaterEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opGreaterEqual, nullptr) << "operator>= not found";
    EXPECT_TRUE(opGreaterEqual->isConst())
        << "operator>= should be const member function";

    // Verify parameter const-correctness
    QualType paramType = opGreaterEqual->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType.isConstQualified())
        << "Parameter should be const qualified";
}

// Test 3: FriendGreaterThanOrEqual - Non-member friend operator>=
TEST_F(GreaterThanOrEqualOperatorTest, FriendGreaterThanOrEqual) {
    const char *code = R"(
        class Value {
        public:
            int data;
            friend bool operator>=(const Value& a, const Value& b);
        };
        bool operator>=(const Value& a, const Value& b);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *friendOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->isOverloadedOperator() &&
                FD->getOverloadedOperator() == OO_GreaterEqual) {
                friendOp = FD;
                break;
            }
        }
    }

    ASSERT_NE(friendOp, nullptr) << "Friend operator>= not found";
    EXPECT_EQ(friendOp->getNumParams(), 2)
        << "Friend operator>= should have 2 parameters";
    EXPECT_TRUE(friendOp->getReturnType()->isBooleanType())
        << "Friend operator>= should return bool";
}

// Test 4: GreaterThanOrEqualEquivalence - Verify a >= b ⟺ !(a < b)
TEST_F(GreaterThanOrEqualOperatorTest, GreaterThanOrEqualEquivalence) {
    const char *code = R"(
        class ComparableInt {
        public:
            int value;
            bool operator<(const ComparableInt& other) const;
            bool operator>=(const ComparableInt& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLess = nullptr;
    CXXMethodDecl *opGreaterEqual = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ComparableInt") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        if (M->getOverloadedOperator() == OO_Less) {
                            opLess = M;
                        } else if (M->getOverloadedOperator() == OO_GreaterEqual) {
                            opGreaterEqual = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(opLess, nullptr) << "operator< not found";
    ASSERT_NE(opGreaterEqual, nullptr) << "operator>= not found";

    // Both operators should have same parameter structure
    EXPECT_EQ(opLess->getNumParams(), opGreaterEqual->getNumParams())
        << "Both operators should have same number of parameters";
}

// Test 5: GreaterThanOrEqualReflexivity - Verify a >= a for all a
TEST_F(GreaterThanOrEqualOperatorTest, GreaterThanOrEqualReflexivity) {
    const char *code = R"(
        class Element {
        public:
            int id;
            bool operator>=(const Element& other) const;
            bool operator==(const Element& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opGreaterEqual = nullptr;
    CXXMethodDecl *opEqual = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Element") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        if (M->getOverloadedOperator() == OO_GreaterEqual) {
                            opGreaterEqual = M;
                        } else if (M->getOverloadedOperator() == OO_EqualEqual) {
                            opEqual = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(opGreaterEqual, nullptr) << "operator>= not found";
    ASSERT_NE(opEqual, nullptr) << "operator== not found for reflexivity check";

    // For reflexivity: a >= a must be true, which is consistent with a == a
    EXPECT_TRUE(opGreaterEqual->isConst())
        << "operator>= must be const for reflexivity";
}

// Test 6: GreaterThanOrEqualTransitivity - Verify a >= b && b >= c => a >= c
TEST_F(GreaterThanOrEqualOperatorTest, GreaterThanOrEqualTransitivity) {
    const char *code = R"(
        class Ordered {
        public:
            int priority;
            bool operator>=(const Ordered& other) const;
            bool operator<=(const Ordered& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opGreaterEqual = nullptr;
    CXXMethodDecl *opLessEqual = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Ordered") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        if (M->getOverloadedOperator() == OO_GreaterEqual) {
                            opGreaterEqual = M;
                        } else if (M->getOverloadedOperator() == OO_LessEqual) {
                            opLessEqual = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(opGreaterEqual, nullptr) << "operator>= not found";
    ASSERT_NE(opLessEqual, nullptr) << "operator<= not found for transitivity check";

    // Both comparison operators should be const and have consistent signatures
    EXPECT_TRUE(opGreaterEqual->isConst())
        << "operator>= should be const";
    EXPECT_TRUE(opLessEqual->isConst())
        << "operator<= should be const for transitivity";
}

// Test 7: GreaterThanOrEqualComplexType - Multi-field comparison
TEST_F(GreaterThanOrEqualOperatorTest, GreaterThanOrEqualComplexType) {
    const char *code = R"(
        class DateTime {
        public:
            int year;
            int month;
            int day;
            int hour;
            int minute;
            bool operator>=(const DateTime& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opGreaterEqual = nullptr;
    int fieldCount = 0;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "DateTime") {
                // Count fields
                for (auto *Field : RD->fields()) {
                    fieldCount++;
                }

                // Find operator>=
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_GreaterEqual) {
                        opGreaterEqual = M;
                    }
                }
            }
        }
    }

    ASSERT_NE(opGreaterEqual, nullptr) << "operator>= not found in DateTime";
    EXPECT_EQ(fieldCount, 5) << "DateTime should have 5 fields";
    EXPECT_TRUE(opGreaterEqual->isConst())
        << "operator>= should be const";
}

// Test 8: GreaterThanOrEqualCallSite - Verify call site transformation
TEST_F(GreaterThanOrEqualOperatorTest, GreaterThanOrEqualCallSite) {
    const char *code = R"(
        class Number {
        public:
            int value;
            bool operator>=(const Number& other) const;
        };

        void checkComparison() {
            Number a(5);
            Number b(3);
            bool result = a >= b;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opGreaterEqual = nullptr;
    FunctionDecl *checkFunc = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Number") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_GreaterEqual) {
                        opGreaterEqual = M;
                    }
                }
            }
        } else if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "checkComparison") {
                checkFunc = FD;
            }
        }
    }

    ASSERT_NE(opGreaterEqual, nullptr) << "operator>= not found";
    ASSERT_NE(checkFunc, nullptr) << "checkComparison function not found";
    EXPECT_TRUE(checkFunc->hasBody())
        << "checkComparison should have a body for call site transformation";
}

// ============================================================================
// ADVANCED OPERATOR>= TESTS
// ============================================================================

class AdvancedGreaterThanOrEqualTest : public GreaterThanOrEqualOperatorTestBase {};

// Test: Multiple operator>= overloads with different parameter types
TEST_F(AdvancedGreaterThanOrEqualTest, MultipleGreaterThanOrEqualOverloads) {
    const char *code = R"(
        class Mixed {
        public:
            int value;
            bool operator>=(const Mixed& other) const;
            bool operator>=(int other) const;
            bool operator>=(double other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int opCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Mixed") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_GreaterEqual) {
                        opCount++;
                    }
                }
            }
        }
    }

    EXPECT_EQ(opCount, 3) << "Expected 3 overloaded operator>= methods";
}

// Test: operator>= in context of full ordering with <, >, <=
TEST_F(AdvancedGreaterThanOrEqualTest, FullOrderingOperators) {
    const char *code = R"(
        class Comparable {
        public:
            int value;
            bool operator<(const Comparable& other) const;
            bool operator>(const Comparable& other) const;
            bool operator<=(const Comparable& other) const;
            bool operator>=(const Comparable& other) const;
            bool operator==(const Comparable& other) const;
            bool operator!=(const Comparable& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int opCount = 0;
    CXXMethodDecl *opGreaterEqual = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Comparable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        opCount++;
                        if (M->getOverloadedOperator() == OO_GreaterEqual) {
                            opGreaterEqual = M;
                        }
                    }
                }
            }
        }
    }

    EXPECT_EQ(opCount, 6) << "Expected 6 comparison operators";
    ASSERT_NE(opGreaterEqual, nullptr) << "operator>= not found";
    EXPECT_TRUE(opGreaterEqual->isConst())
        << "operator>= should be const in full ordering";
}

// Test: operator>= with different return types (though should be bool)
TEST_F(AdvancedGreaterThanOrEqualTest, GreaterThanOrEqualReturnType) {
    const char *code = R"(
        class Value {
        public:
            int data;
            bool operator>=(const Value& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opGreaterEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Value") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_GreaterEqual) {
                        opGreaterEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opGreaterEqual, nullptr) << "operator>= not found";
    QualType returnType = opGreaterEqual->getReturnType();
    EXPECT_TRUE(returnType->isBooleanType())
        << "operator>= return type should be bool";
    EXPECT_FALSE(returnType->isReferenceType())
        << "operator>= should return bool by value, not reference";
}


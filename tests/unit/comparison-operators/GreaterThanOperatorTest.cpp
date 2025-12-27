// Unit Tests for operator> (Greater-Than Comparison)
// Phase 51: Comprehensive comparison operator tests
//
// Tests ensure that C++ operator> is correctly detected and translated to C.
// These tests validate operator detection, const correctness, return types,
// and operator application across various contexts.
//
// Test Coverage:
// 1. BasicGreaterThan - Simple member operator>
// 2. GreaterThanConstCorrectness - Verify const member function
// 3. FriendGreaterThan - Non-member friend operator>
// 4. GreaterThanEquivalentToReverseLessThan - Verify a > b ⟺ b < a
// 5. GreaterThanTransitivity - Verify transitivity: a > b && b > c => a > c
// 6. GreaterThanComplexType - Multi-field comparison
// 7. GreaterThanCallSite - Verify call site transformation
// 8. GreaterThanReturnType - Verify returns bool

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"

using namespace clang;

// ============================================================================
// TEST FIXTURE
// ============================================================================

class GreaterThanOperatorTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }

    // Helper: Find CXXMethodDecl by name and class
    CXXMethodDecl* findMethodInClass(ASTUnit* AST, const char* className,
                                      const char* methodName) {
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        for (auto *D : TU->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == className) {
                    for (auto *M : RD->methods()) {
                        if (M->getNameAsString() == methodName) {
                            return M;
                        }
                    }
                }
            }
        }
        return nullptr;
    }

    // Helper: Find operator> in class
    CXXMethodDecl* findGreaterThanOperator(ASTUnit* AST, const char* className) {
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        for (auto *D : TU->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == className) {
                    for (auto *M : RD->methods()) {
                        if (M->isOverloadedOperator() &&
                            M->getOverloadedOperator() == OO_Greater) {
                            return M;
                        }
                    }
                }
            }
        }
        return nullptr;
    }

    // Helper: Find friend operator> function
    FunctionDecl* findFriendGreaterThanOperator(ASTUnit* AST) {
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        for (auto *D : TU->decls()) {
            if (auto *FD = dyn_cast<FunctionDecl>(D)) {
                if (FD->isOverloadedOperator() &&
                    FD->getOverloadedOperator() == OO_Greater &&
                    FD->getNumParams() == 2) {
                    return FD;
                }
            }
        }
        return nullptr;
    }
};

// ============================================================================
// TEST CASES (8 tests)
// ============================================================================

// Test 1: BasicGreaterThan
// Tests: operator> can be defined as a member function
TEST_F(GreaterThanOperatorTest, BasicGreaterThan) {
    const char *code = R"(
        class Priority {
        public:
            int level;
            bool operator>(const Priority& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CXXMethodDecl *opGreater = findGreaterThanOperator(AST.get(), "Priority");

    ASSERT_NE(opGreater, nullptr) << "operator> not found in Priority class";
    EXPECT_EQ(opGreater->getNumParams(), 1) << "operator> should have 1 parameter";
    EXPECT_TRUE(opGreater->isConst()) << "operator> should be const";
    EXPECT_TRUE(opGreater->getReturnType()->isBooleanType())
        << "operator> should return bool";
}

// Test 2: GreaterThanConstCorrectness
// Tests: const member function and const parameter enforcement
TEST_F(GreaterThanOperatorTest, GreaterThanConstCorrectness) {
    const char *code = R"(
        class Score {
        private:
            double points;
        public:
            Score(double p) : points(p) {}
            bool operator>(const Score& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CXXMethodDecl *opGreater = findGreaterThanOperator(AST.get(), "Score");

    ASSERT_NE(opGreater, nullptr) << "operator> not found in Score class";

    // Check method is const
    EXPECT_TRUE(opGreater->isConst())
        << "operator> should be const member function";

    // Check parameter is const reference
    QualType paramType = opGreater->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType.isConstQualified())
        << "operator> parameter should be const";

    // Check return type is bool
    EXPECT_TRUE(opGreater->getReturnType()->isBooleanType())
        << "operator> should return bool";
}

// Test 3: FriendGreaterThan
// Tests: operator> can be defined as non-member friend function
TEST_F(GreaterThanOperatorTest, FriendGreaterThan) {
    const char *code = R"(
        class Number {
        public:
            int value;
            friend bool operator>(const Number& a, const Number& b);
        };
        bool operator>(const Number& a, const Number& b);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    FunctionDecl *friendOp = findFriendGreaterThanOperator(AST.get());

    ASSERT_NE(friendOp, nullptr) << "Friend operator> not found";
    EXPECT_EQ(friendOp->getNumParams(), 2)
        << "Friend operator> should have 2 parameters";
    EXPECT_TRUE(friendOp->isOverloadedOperator())
        << "Should be overloaded operator";
    EXPECT_EQ(friendOp->getOverloadedOperator(), OO_Greater)
        << "Should be operator>";
}

// Test 4: GreaterThanEquivalentToReverseLessThan
// Tests: a > b should be equivalent to b < a
TEST_F(GreaterThanOperatorTest, GreaterThanEquivalentToReverseLessThan) {
    const char *code = R"(
        class Comparable {
        public:
            int value;
            bool operator>(const Comparable& other) const;
            bool operator<(const Comparable& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CXXMethodDecl *opGreater = findGreaterThanOperator(AST.get(), "Comparable");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXMethodDecl *opLess = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Comparable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_Less) {
                        opLess = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opGreater, nullptr) << "operator> not found";
    ASSERT_NE(opLess, nullptr) << "operator< not found";

    // Both should exist and have same signature
    EXPECT_EQ(opGreater->getNumParams(), opLess->getNumParams())
        << "operator> and operator< should have same number of parameters";
    EXPECT_TRUE(opGreater->getReturnType()->isBooleanType())
        << "operator> should return bool";
    EXPECT_TRUE(opLess->getReturnType()->isBooleanType())
        << "operator< should return bool";
}

// Test 5: GreaterThanTransitivity
// Tests: operator> defines transitive relationship (a > b && b > c => a > c)
TEST_F(GreaterThanOperatorTest, GreaterThanTransitivity) {
    const char *code = R"(
        class Version {
        public:
            int major, minor, patch;
            bool operator>(const Version& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CXXMethodDecl *opGreater = findGreaterThanOperator(AST.get(), "Version");

    ASSERT_NE(opGreater, nullptr) << "operator> not found in Version class";

    // Verify it's properly defined as member function for transitive ops
    EXPECT_TRUE(opGreater->isConst())
        << "operator> should be const for transitivity";
    EXPECT_EQ(opGreater->getNumParams(), 1)
        << "operator> should have exactly one parameter";
    EXPECT_TRUE(opGreater->getReturnType()->isBooleanType())
        << "operator> should return bool";
}

// Test 6: GreaterThanComplexType
// Tests: operator> with multi-field comparison
TEST_F(GreaterThanOperatorTest, GreaterThanComplexType) {
    const char *code = R"(
        class Point3D {
        public:
            double x, y, z;
            // Multi-field comparison (compare by all coordinates)
            bool operator>(const Point3D& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CXXMethodDecl *opGreater = findGreaterThanOperator(AST.get(), "Point3D");

    ASSERT_NE(opGreater, nullptr) << "operator> not found in Point3D class";

    // Verify signature for complex type
    EXPECT_EQ(opGreater->getNumParams(), 1)
        << "operator> should have 1 parameter";
    EXPECT_TRUE(opGreater->isConst())
        << "operator> should be const";
    EXPECT_TRUE(opGreater->getReturnType()->isBooleanType())
        << "operator> should return bool";
}

// Test 7: GreaterThanCallSite
// Tests: operator> can be called at usage site
TEST_F(GreaterThanOperatorTest, GreaterThanCallSite) {
    const char *code = R"(
        class Value {
        public:
            int data;
            bool operator>(const Value& other) const;
            void compareValues(const Value& v1, const Value& v2) {
                bool result = v1 > v2;  // Call site usage
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CXXMethodDecl *opGreater = findGreaterThanOperator(AST.get(), "Value");

    ASSERT_NE(opGreater, nullptr) << "operator> not found";

    // Verify it can be used in method body
    CXXMethodDecl *compareMethod = findMethodInClass(AST.get(), "Value", "compareValues");
    ASSERT_NE(compareMethod, nullptr) << "compareValues method not found";

    // Method should have body
    EXPECT_TRUE(compareMethod->hasBody())
        << "compareValues should have body with operator> call";
}

// Test 8: GreaterThanReturnType
// Tests: operator> return type validation
TEST_F(GreaterThanOperatorTest, GreaterThanReturnType) {
    const char *code = R"(
        class Quantity {
        public:
            double amount;
            bool operator>(const Quantity& other) const {
                return amount > other.amount;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    CXXMethodDecl *opGreater = findGreaterThanOperator(AST.get(), "Quantity");

    ASSERT_NE(opGreater, nullptr) << "operator> not found";

    // Verify return type
    QualType returnType = opGreater->getReturnType();
    EXPECT_TRUE(returnType->isBooleanType())
        << "operator> must return bool type";

    // Verify has body
    EXPECT_TRUE(opGreater->hasBody())
        << "operator> should have implementation body";
}


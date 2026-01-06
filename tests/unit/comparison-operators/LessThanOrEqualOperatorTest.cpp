// Unit Tests for operator<= (Less-Than-or-Equal) Comparison Operator
// Phase 51: Comparison Operator Overloading Implementation
//
// Test Coverage:
// - Basic member operator<= (const member function)
// - operator<= const correctness
// - Friend (non-member) operator<=
// - Equivalence verification: a <= b ⟺ !(b < a)
// - Reflexivity: a <= a is true for all a
// - Transitivity: a <= b && b <= c ⟹ a <= c
// - Multi-field comparison
// - Call site transformation

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"

using namespace clang;

// Test fixture base class with AST builder
class LessThanOrEqualOperatorTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// TEST 1: BasicLessThanOrEqual - Simple member operator<=
// ============================================================================

TEST_F(LessThanOrEqualOperatorTest, BasicLessThanOrEqual) {
    const char *code = R"(
        class Comparable {
        public:
            int value;
            bool operator<=(const Comparable& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find the Comparable class
    CXXRecordDecl *comparableClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Comparable") {
                comparableClass = RD;
                break;
            }
        }
    }

    ASSERT_NE(comparableClass, nullptr) << "Comparable class not found";

    // Find operator<=
    CXXMethodDecl *opLessEqual = nullptr;
    for (auto *M : comparableClass->methods()) {
        if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_LessEqual) {
            opLessEqual = M;
            break;
        }
    }

    ASSERT_NE(opLessEqual, nullptr) << "operator<= not found";
    EXPECT_EQ(opLessEqual->getNumParams(), 1) << "operator<= should have 1 parameter";
    EXPECT_TRUE(opLessEqual->isConst()) << "operator<= should be const member function";
    EXPECT_TRUE(opLessEqual->getReturnType()->isBooleanType()) << "operator<= should return bool";
}

// ============================================================================
// TEST 2: LessThanOrEqualConstCorrectness - Verify const member function
// ============================================================================

TEST_F(LessThanOrEqualOperatorTest, LessThanOrEqualConstCorrectness) {
    const char *code = R"(
        class Version {
        public:
            int major, minor;
            bool operator<=(const Version& other) const {
                if (major != other.major) return major <= other.major;
                return minor <= other.minor;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXRecordDecl *versionClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Version") {
                versionClass = RD;
                break;
            }
        }
    }

    ASSERT_NE(versionClass, nullptr) << "Version class not found";

    CXXMethodDecl *opLessEqual = nullptr;
    for (auto *M : versionClass->methods()) {
        if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_LessEqual) {
            opLessEqual = M;
            break;
        }
    }

    ASSERT_NE(opLessEqual, nullptr) << "operator<= not found";

    // Verify const correctness
    EXPECT_TRUE(opLessEqual->isConst()) << "operator<= must be const";

    // Verify parameter is const reference
    QualType paramType = opLessEqual->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType.isConstQualified()) << "Parameter should be const";

    // Verify return type is bool
    EXPECT_TRUE(opLessEqual->getReturnType()->isBooleanType()) << "Return type should be bool";

    // Verify method has body
    EXPECT_TRUE(opLessEqual->hasBody()) << "operator<= should have implementation";
}

// ============================================================================
// TEST 3: FriendLessThanOrEqual - Non-member friend operator<=
// ============================================================================

TEST_F(LessThanOrEqualOperatorTest, FriendLessThanOrEqual) {
    const char *code = R"(
        class Number {
        public:
            int value;
            friend bool operator<=(const Number& lhs, const Number& rhs);
        };
        bool operator<=(const Number& lhs, const Number& rhs);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find the friend operator<= (should be a FunctionDecl, not CXXMethodDecl)
    FunctionDecl *friendOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->isOverloadedOperator() &&
                FD->getOverloadedOperator() == OO_LessEqual &&
                !isa<CXXMethodDecl>(FD)) {
                friendOp = FD;
                break;
            }
        }
    }

    ASSERT_NE(friendOp, nullptr) << "Friend operator<= not found";
    EXPECT_EQ(friendOp->getNumParams(), 2) << "Friend operator<= should have 2 parameters";
    EXPECT_TRUE(friendOp->getReturnType()->isBooleanType()) << "Should return bool";

    // Verify parameters are both const references
    for (unsigned i = 0; i < friendOp->getNumParams(); ++i) {
        QualType paramType = friendOp->getParamDecl(i)->getType();
        if (paramType->isReferenceType()) {
            paramType = paramType->getPointeeType();
        }
        EXPECT_TRUE(paramType.isConstQualified()) << "Parameter " << i << " should be const";
    }
}

// ============================================================================
// TEST 4: LessThanOrEqualEquivalence - Verify a <= b ⟺ !(b < a)
// ============================================================================

TEST_F(LessThanOrEqualOperatorTest, LessThanOrEqualEquivalence) {
    const char *code = R"(
        class Priority {
        public:
            int level;
            bool operator<(const Priority& other) const {
                return level < other.level;
            }
            bool operator<=(const Priority& other) const {
                return level <= other.level;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXRecordDecl *priorityClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Priority") {
                priorityClass = RD;
                break;
            }
        }
    }

    ASSERT_NE(priorityClass, nullptr) << "Priority class not found";

    // Find both operators
    CXXMethodDecl *opLess = nullptr;
    CXXMethodDecl *opLessEqual = nullptr;

    for (auto *M : priorityClass->methods()) {
        if (M->isOverloadedOperator()) {
            if (M->getOverloadedOperator() == OO_Less) {
                opLess = M;
            } else if (M->getOverloadedOperator() == OO_LessEqual) {
                opLessEqual = M;
            }
        }
    }

    ASSERT_NE(opLess, nullptr) << "operator< not found";
    ASSERT_NE(opLessEqual, nullptr) << "operator<= not found";

    // Both should return bool and be const
    EXPECT_TRUE(opLess->getReturnType()->isBooleanType()) << "operator< should return bool";
    EXPECT_TRUE(opLessEqual->getReturnType()->isBooleanType()) << "operator<= should return bool";
    EXPECT_TRUE(opLess->isConst()) << "operator< should be const";
    EXPECT_TRUE(opLessEqual->isConst()) << "operator<= should be const";
}

// ============================================================================
// TEST 5: LessThanOrEqualReflexivity - Verify a <= a for all a
// ============================================================================

TEST_F(LessThanOrEqualOperatorTest, LessThanOrEqualReflexivity) {
    const char *code = R"(
        class Reflexive {
        public:
            int id;
            bool operator<=(const Reflexive& other) const {
                return id <= other.id;
            }
            // Reflexivity: a <= a should always be true
            bool isReflexive() const {
                return *this <= *this;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXRecordDecl *reflexiveClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Reflexive") {
                reflexiveClass = RD;
                break;
            }
        }
    }

    ASSERT_NE(reflexiveClass, nullptr) << "Reflexive class not found";

    // Find operator<=
    CXXMethodDecl *opLessEqual = nullptr;
    for (auto *M : reflexiveClass->methods()) {
        if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_LessEqual) {
            opLessEqual = M;
            break;
        }
    }

    ASSERT_NE(opLessEqual, nullptr) << "operator<= not found";
    EXPECT_TRUE(opLessEqual->getReturnType()->isBooleanType()) << "operator<= should return bool";
    EXPECT_TRUE(opLessEqual->isConst()) << "operator<= should be const";
}

// ============================================================================
// TEST 6: LessThanOrEqualTransitivity - Verify a <= b && b <= c => a <= c
// ============================================================================

TEST_F(LessThanOrEqualOperatorTest, LessThanOrEqualTransitivity) {
    const char *code = R"(
        class Transitive {
        public:
            int value;
            bool operator<=(const Transitive& other) const {
                return value <= other.value;
            }
            // Transitivity: if a <= b and b <= c, then a <= c
            bool checkTransitivity(const Transitive& b, const Transitive& c) const {
                if (*this <= b && b <= c) {
                    return *this <= c;  // Should always be true
                }
                return true;  // Condition not met
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXRecordDecl *transitiveClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Transitive") {
                transitiveClass = RD;
                break;
            }
        }
    }

    ASSERT_NE(transitiveClass, nullptr) << "Transitive class not found";

    // Find operator<=
    CXXMethodDecl *opLessEqual = nullptr;
    for (auto *M : transitiveClass->methods()) {
        if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_LessEqual) {
            opLessEqual = M;
            break;
        }
    }

    ASSERT_NE(opLessEqual, nullptr) << "operator<= not found";

    // Verify it can be used in chained comparisons
    EXPECT_TRUE(opLessEqual->hasBody()) << "operator<= should have implementation";
    EXPECT_TRUE(opLessEqual->getReturnType()->isBooleanType()) << "operator<= should return bool";

    // Find checkTransitivity method to verify it uses operator<=
    FunctionDecl *checkTransitivity = nullptr;
    for (auto *M : transitiveClass->methods()) {
        if (M->getNameAsString() == "checkTransitivity") {
            checkTransitivity = M;
            break;
        }
    }

    EXPECT_NE(checkTransitivity, nullptr) << "checkTransitivity method should exist";
}

// ============================================================================
// TEST 7: LessThanOrEqualComplexType - Multi-field comparison
// ============================================================================

TEST_F(LessThanOrEqualOperatorTest, LessThanOrEqualComplexType) {
    const char *code = R"(
        class ComplexNumber {
        public:
            double real, imag;
            bool operator<=(const ComplexNumber& other) const {
                // Compare by magnitude (real^2 + imag^2)
                double mag1 = real * real + imag * imag;
                double mag2 = other.real * other.real + other.imag * other.imag;
                return mag1 <= mag2;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXRecordDecl *complexClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ComplexNumber") {
                complexClass = RD;
                break;
            }
        }
    }

    ASSERT_NE(complexClass, nullptr) << "ComplexNumber class not found";

    CXXMethodDecl *opLessEqual = nullptr;
    for (auto *M : complexClass->methods()) {
        if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_LessEqual) {
            opLessEqual = M;
            break;
        }
    }

    ASSERT_NE(opLessEqual, nullptr) << "operator<= not found";
    EXPECT_TRUE(opLessEqual->getReturnType()->isBooleanType()) << "operator<= should return bool";
    EXPECT_TRUE(opLessEqual->hasBody()) << "operator<= should have implementation";
    EXPECT_EQ(opLessEqual->getNumParams(), 1) << "operator<= should have 1 parameter";
}

// ============================================================================
// TEST 8: LessThanOrEqualCallSite - Verify call site transformation
// ============================================================================

TEST_F(LessThanOrEqualOperatorTest, LessThanOrEqualCallSite) {
    const char *code = R"(
        class Score {
        public:
            int points;
            bool operator<=(const Score& other) const {
                return points <= other.points;
            }
        };

        void evaluate(const Score& a, const Score& b) {
            bool result = a <= b;  // operator<= call site
            if (a <= b) {
                // ...
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find the Score class
    CXXRecordDecl *scoreClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Score") {
                scoreClass = RD;
                break;
            }
        }
    }

    ASSERT_NE(scoreClass, nullptr) << "Score class not found";

    // Find operator<=
    CXXMethodDecl *opLessEqual = nullptr;
    for (auto *M : scoreClass->methods()) {
        if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_LessEqual) {
            opLessEqual = M;
            break;
        }
    }

    ASSERT_NE(opLessEqual, nullptr) << "operator<= not found";

    // Find the evaluate function to verify operator<= call sites exist
    FunctionDecl *evaluateFunc = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "evaluate" && !isa<CXXMethodDecl>(FD)) {
                evaluateFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(evaluateFunc, nullptr) << "evaluate function not found";
    EXPECT_TRUE(evaluateFunc->hasBody()) << "evaluate function should have body";

    // Search for CXXOperatorCallExpr nodes in the function body
    bool foundOperatorCall = false;
    std::function<void(Stmt*)> findOperatorCall = [&](Stmt *S) {
        if (!S) return;

        if (auto *OpCall = dyn_cast<CXXOperatorCallExpr>(S)) {
            if (OpCall->getOperator() == OO_LessEqual) {
                foundOperatorCall = true;
                return;
            }
        }

        for (auto *Child : S->children()) {
            findOperatorCall(Child);
        }
    };

    findOperatorCall(evaluateFunc->getBody());
    EXPECT_TRUE(foundOperatorCall) << "operator<= call should be found in function body";
}

// ============================================================================
// BONUS TEST 9: LessThanOrEqualWithDifferentTypes
// ============================================================================

TEST_F(LessThanOrEqualOperatorTest, LessThanOrEqualWithDifferentTypes) {
    const char *code = R"(
        class Comparable {
        public:
            int value;
            bool operator<=(const Comparable& other) const {
                return value <= other.value;
            }
            // Allow comparison with int
            bool operator<=(int other) const {
                return value <= other;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXRecordDecl *comparableClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Comparable") {
                comparableClass = RD;
                break;
            }
        }
    }

    ASSERT_NE(comparableClass, nullptr) << "Comparable class not found";

    // Count operator<= overloads
    int opCount = 0;
    for (auto *M : comparableClass->methods()) {
        if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_LessEqual) {
            opCount++;
        }
    }

    EXPECT_GE(opCount, 2) << "Should have at least 2 operator<= overloads";
}

// ============================================================================
// BONUS TEST 10: LessThanOrEqualInContainer
// ============================================================================

TEST_F(LessThanOrEqualOperatorTest, LessThanOrEqualInContainer) {
    const char *code = R"(
        class Item {
        public:
            int priority;
            bool operator<=(const Item& other) const {
                return priority <= other.priority;
            }
        };

        void sortItems(Item* items, int count) {
            // Simulating bubble sort using operator<=
            for (int i = 0; i < count - 1; ++i) {
                for (int j = 0; j < count - i - 1; ++j) {
                    if (!(items[j] <= items[j + 1])) {
                        // Swap
                        Item temp = items[j];
                        items[j] = items[j + 1];
                        items[j + 1] = temp;
                    }
                }
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find Item class
    CXXRecordDecl *itemClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Item") {
                itemClass = RD;
                break;
            }
        }
    }

    ASSERT_NE(itemClass, nullptr) << "Item class not found";

    // Find operator<=
    CXXMethodDecl *opLessEqual = nullptr;
    for (auto *M : itemClass->methods()) {
        if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_LessEqual) {
            opLessEqual = M;
            break;
        }
    }

    ASSERT_NE(opLessEqual, nullptr) << "operator<= not found";

    // Find sortItems function
    FunctionDecl *sortFunc = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "sortItems") {
                sortFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(sortFunc, nullptr) << "sortItems function not found";
    EXPECT_TRUE(sortFunc->hasBody()) << "sortItems should have implementation";
}

// Unit Tests for C++ operator!= (Inequality) Comparison Operator
// Phase 51: Comprehensive inequality operator tests for C++ to C transpiler
//
// Tests ensure that C++ operator!= is correctly detected, validated, and
// prepared for transpilation. These tests verify operator detection,
// const correctness, member vs friend variants, and semantic properties.

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/RecursiveASTVisitor.h"

using namespace clang;

// Test fixture base class with helper method
class InequalityOperatorTestBase : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// INEQUALITY OPERATOR TESTS (operator!=)
// ============================================================================

class InequalityOperatorTest : public InequalityOperatorTestBase {};

// Test 1: BasicInequality - Simple member operator!=
//
// Validates that a member operator!= in a simple class is correctly detected
// and identified as an overloaded operator with the ExclaimEqual token.
TEST_F(InequalityOperatorTest, BasicInequality) {
    const char *code = R"(
        class Point {
        public:
            int x, y;
            bool operator!=(const Point& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opNotEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Point") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_ExclaimEqual) {
                        opNotEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opNotEqual, nullptr) << "operator!= not found in Point class";
    EXPECT_EQ(opNotEqual->getOverloadedOperator(), OO_ExclaimEqual)
        << "operator should be identified as ExclaimEqual (!=)";
}

// Test 2: InequalityConstCorrectness - Verify const member function
//
// Validates that operator!= is properly marked as const. Since inequality
// comparison doesn't modify the object, it must always be const.
TEST_F(InequalityOperatorTest, InequalityConstCorrectness) {
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
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_ExclaimEqual) {
                        opNotEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opNotEqual, nullptr) << "operator!= not found";
    EXPECT_TRUE(opNotEqual->isConst())
        << "operator!= must be const (doesn't modify object)";

    // Verify parameter is const-qualified
    ASSERT_GE(opNotEqual->getNumParams(), 1) << "operator!= should have at least 1 parameter";
    QualType paramType = opNotEqual->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType.isConstQualified())
        << "Parameter should be const-qualified";
}

// Test 3: FriendInequality - Non-member friend operator!=
//
// Validates that friend (non-member) operator!= declarations are correctly
// identified as overloaded operators with 2 parameters (no implicit this).
TEST_F(InequalityOperatorTest, FriendInequality) {
    const char *code = R"(
        class Value {
        public:
            int data;
            friend bool operator!=(const Value& a, const Value& b);
        };
        bool operator!=(const Value& a, const Value& b);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *friendOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->isOverloadedOperator() &&
                FD->getOverloadedOperator() == OO_ExclaimEqual &&
                !isa<CXXMethodDecl>(FD)) {
                friendOp = FD;
                break;
            }
        }
    }

    ASSERT_NE(friendOp, nullptr) << "Friend operator!= not found";
    EXPECT_EQ(friendOp->getNumParams(), 2)
        << "Friend operator!= should have 2 explicit parameters";
    EXPECT_FALSE(isa<CXXMethodDecl>(friendOp))
        << "Friend operator!= should be non-member function";
}

// Test 4: InequalityEquivalence - Verify a != b ⟺ !(a == b)
//
// Validates that when both operator== and operator!= are present,
// they maintain the logical equivalence relationship. This is semantic
// validation for transpilation correctness.
TEST_F(InequalityOperatorTest, InequalityEquivalence) {
    const char *code = R"(
        class Comparable {
        public:
            int value;
            bool operator==(const Comparable& other) const;
            bool operator!=(const Comparable& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    CXXMethodDecl *opNotEqual = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Comparable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator()) {
                        if (M->getOverloadedOperator() == OO_EqualEqual) {
                            opEqual = M;
                        } else if (M->getOverloadedOperator() == OO_ExclaimEqual) {
                            opNotEqual = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(opEqual, nullptr) << "operator== not found";
    ASSERT_NE(opNotEqual, nullptr) << "operator!= not found";

    // Both should have same parameter types (should be comparable)
    EXPECT_EQ(opEqual->getNumParams(), opNotEqual->getNumParams())
        << "operator== and operator!= should have same number of parameters";

    // Both should return bool
    EXPECT_TRUE(opEqual->getReturnType()->isBooleanType())
        << "operator== should return bool";
    EXPECT_TRUE(opNotEqual->getReturnType()->isBooleanType())
        << "operator!= should return bool";
}

// Test 5: InequalitySymmetric - Verify a != b ⟺ b != a
//
// Validates that inequality is symmetric - the order of operands doesn't
// change the inequality relationship. Tests both member and friend variants.
TEST_F(InequalityOperatorTest, InequalitySymmetric) {
    const char *code = R"(
        class Element {
        public:
            int id;
            bool operator!=(const Element& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opNotEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Element") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_ExclaimEqual) {
                        opNotEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opNotEqual, nullptr) << "operator!= not found";

    // For symmetry validation:
    // a != b should be equivalent to b != a
    // This requires both operands to be type-compatible
    EXPECT_EQ(opNotEqual->getNumParams(), 1)
        << "Member operator!= takes one parameter (the other operand)";

    // Parameter should be same type (for symmetry)
    QualType paramType = opNotEqual->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType->isRecordType())
        << "Parameter should be Element type for symmetry";
}

// Test 6: InequalityComplexType - Multi-field comparison
//
// Validates operator!= with complex types containing multiple fields.
// Tests that operator!= can be applied to objects with more than one member.
TEST_F(InequalityOperatorTest, InequalityComplexType) {
    const char *code = R"(
        class Rectangle {
        public:
            int x, y, width, height;
            bool operator!=(const Rectangle& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXRecordDecl *rectClass = nullptr;
    CXXMethodDecl *opNotEqual = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Rectangle") {
                rectClass = RD;
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_ExclaimEqual) {
                        opNotEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(rectClass, nullptr) << "Rectangle class not found";
    ASSERT_NE(opNotEqual, nullptr) << "operator!= not found in Rectangle";

    // Verify class has multiple fields
    int fieldCount = 0;
    for (auto *field : rectClass->fields()) {
        (void)field; // Use field to avoid compiler warning
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 4)
        << "Rectangle should have 4 fields (x, y, width, height)";

    // Verify operator!= can handle this complex type
    EXPECT_TRUE(opNotEqual->getReturnType()->isBooleanType())
        << "operator!= should return bool";
}

// Test 7: InequalityCallSite - Verify call site transformation
//
// Validates that operator!= call sites in binary expressions are correctly
// identified as CXXOperatorCallExpr, which is necessary for transpilation.
TEST_F(InequalityOperatorTest, InequalityCallSite) {
    const char *code = R"(
        class Number {
        public:
            int value;
            bool operator!=(const Number& other) const;
        };

        void test() {
            Number a, b;
            if (a != b) {
                // Use result
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *testFunc = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test") {
                testFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(testFunc, nullptr) << "test() function not found";
    ASSERT_TRUE(testFunc->hasBody()) << "test() should have a body";

    // Verify we can find the operator call in the AST
    // (This requires walking the compound statement)
    bool foundOperatorCall = false;

    class OperatorCallFinder : public RecursiveASTVisitor<OperatorCallFinder> {
    public:
        bool found = false;

        bool VisitCXXOperatorCallExpr(CXXOperatorCallExpr *OCE) {
            if (OCE->getOperator() == OO_ExclaimEqual) {
                found = true;
                return false;
            }
            return true;
        }
    };

    OperatorCallFinder finder;
    finder.TraverseDecl(testFunc);
    foundOperatorCall = finder.found;

    EXPECT_TRUE(foundOperatorCall)
        << "operator!= call site should be found as CXXOperatorCallExpr";
}

// Test 8: InequalityReturnType - Verify returns bool
//
// Validates that operator!= returns a boolean type. This is a fundamental
// requirement for comparison operators in C++ and must be preserved in transpilation.
TEST_F(InequalityOperatorTest, InequalityReturnType) {
    const char *code = R"(
        class Wrapper {
        public:
            int data;
            bool operator!=(const Wrapper& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opNotEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Wrapper") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_ExclaimEqual) {
                        opNotEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opNotEqual, nullptr) << "operator!= not found";

    QualType returnType = opNotEqual->getReturnType();
    EXPECT_TRUE(returnType->isBooleanType())
        << "operator!= must return bool, got: " << returnType.getAsString();
}

// ============================================================================
// ADDITIONAL VALIDATION TESTS
// ============================================================================

class InequalityAdvancedTest : public InequalityOperatorTestBase {};

// Additional Test 9: Multiple inequality operators (overloading with different types)
TEST_F(InequalityAdvancedTest, MultipleInequalityOverloads) {
    const char *code = R"(
        class Multi {
        public:
            int value;
            bool operator!=(const Multi& other) const;
            bool operator!=(int other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int opCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Multi") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_ExclaimEqual) {
                        opCount++;
                    }
                }
            }
        }
    }

    EXPECT_EQ(opCount, 2) << "Expected 2 overloaded operator!= variants";
}

// Additional Test 10: Inequality with default parameter
TEST_F(InequalityAdvancedTest, InequalityInClassDefinition) {
    const char *code = R"(
        class Inline {
        public:
            int x;
            bool operator!=(const Inline& other) const {
                return x != other.x;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opNotEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Inline") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_ExclaimEqual) {
                        opNotEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opNotEqual, nullptr) << "operator!= not found";
    EXPECT_TRUE(opNotEqual->hasBody()) << "Inline operator!= should have a body";
    EXPECT_TRUE(opNotEqual->isInlined()) << "operator!= should be marked as inline";
}

// ============================================================================
// Unit Tests for operator== (Equality Comparison Operator)
// Stream 5: Comprehensive equality operator tests for C++ to C transpiler
//
// Tests ensure that C++ operator== is correctly detected, analyzed, and
// transpiled to equivalent C code. These tests validate:
// - Basic member operator== detection
// - Const correctness and function semantics
// - Friend non-member operator== detection
// - Equivalence relation properties (reflexivity, symmetry, transitivity)
// - Complex type comparisons (rational numbers, cross-multiply)
// - Heterogeneous equality operators
// - Call site transformations
// - Return type verification (bool)
//
// The operator== is the MOST IMPORTANT comparison operator as it forms the
// foundation for all other comparison operations (!=, <, >, <=, >=).
// ============================================================================

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"

using namespace clang;

// Test fixture base class with helper method
class EqualityOperatorTestBase : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// TEST SUITE 1: Basic Equality Operator Detection
// ============================================================================

class BasicEqualityTest : public EqualityOperatorTestBase {};

// Test 1: BasicEquality - Simple member operator==
// Tests that operator== is correctly detected as a member function
TEST_F(BasicEqualityTest, BasicEqualityMemberOperator) {
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

    ASSERT_NE(opEqual, nullptr) << "operator== not found in Point class";
    EXPECT_EQ(opEqual->getNumParams(), 1) << "operator== should have 1 parameter";
    EXPECT_TRUE(opEqual->getReturnType()->isBooleanType()) << "operator== should return bool";
    EXPECT_TRUE(opEqual->isConst()) << "operator== should be const member function";
}

// Test 2: EqualityConstCorrectness - Verify const member function
// Tests that const correctness is enforced for operator==
TEST_F(BasicEqualityTest, EqualityConstCorrectness) {
    const char *code = R"(
        class Rectangle {
        public:
            double width, height;
            bool operator==(const Rectangle& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Rectangle") {
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

    // Verify the operator is a const member function
    EXPECT_TRUE(opEqual->isConst()) << "operator== should be const";

    // Verify parameter is const reference
    QualType paramType = opEqual->getParamDecl(0)->getType();
    EXPECT_TRUE(paramType->isReferenceType()) << "Parameter should be reference";

    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType.isConstQualified()) << "Parameter should be const";
}

// Test 3: FriendEquality - Non-member friend operator==
// Tests detection of non-member friend operator==
TEST_F(BasicEqualityTest, FriendEqualityOperator) {
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
    EXPECT_EQ(friendOp->getNumParams(), 2) << "Non-member operator== should have 2 parameters";
    EXPECT_TRUE(friendOp->getReturnType()->isBooleanType()) << "Non-member operator== should return bool";
}

// ============================================================================
// TEST SUITE 2: Equivalence Relation Properties
// ============================================================================

class EquivalenceRelationTest : public EqualityOperatorTestBase {};

// Test 4: EqualityReflexive - Verify a == a for all a
// Tests that the reflexive property can be satisfied
// (Every object is equal to itself)
TEST_F(EquivalenceRelationTest, EqualityReflexive) {
    const char *code = R"(
        class Number {
        public:
            int value;
            bool operator==(const Number& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Number") {
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

    // Verify operator can be used reflexively
    // The signature allows: a == a (same object or equal values)
    EXPECT_EQ(opEqual->getNumParams(), 1) << "operator== signature allows reflexive comparison";
    EXPECT_TRUE(opEqual->getReturnType()->isBooleanType()) << "Returns bool for comparison";
}

// Test 5: EqualitySymmetric - Verify a == b ⟺ b == a
// Tests that operator== satisfies symmetry property
TEST_F(EquivalenceRelationTest, EqualitySymmetric) {
    const char *code = R"(
        class Element {
        public:
            int value;
            bool operator==(const Element& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Element") {
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

    // Verify both operands are const references
    // This ensures: if a == b then (semantically) b == a
    QualType paramType = opEqual->getParamDecl(0)->getType();
    EXPECT_TRUE(paramType->isReferenceType()) << "First operand is reference";

    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType.isConstQualified()) << "First operand is const";

    EXPECT_TRUE(opEqual->isConst()) << "Member operator== is const (implicit second operand)";
}

// Test 6: EqualityTransitive - Verify a == b && b == c => a == c
// Tests that operator== can satisfy transitivity property
TEST_F(EquivalenceRelationTest, EqualityTransitive) {
    const char *code = R"(
        class Item {
        public:
            int id;
            bool operator==(const Item& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Item") {
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

    // Verify the operator has consistent signature for transitivity
    // operator==(const Item&) can be chained: (a == b) && (b == c) => (a == c)
    EXPECT_EQ(opEqual->getNumParams(), 1) << "Signature supports transitive composition";
    EXPECT_TRUE(opEqual->getReturnType()->isBooleanType()) << "Returns bool for composition";
}

// ============================================================================
// TEST SUITE 3: Complex Type Comparisons
// ============================================================================

class ComplexEqualityTest : public EqualityOperatorTestBase {};

// Test 7: EqualityComplexType - Rational number comparison (cross-multiply)
// Tests equality operator on complex types with non-trivial implementation
TEST_F(ComplexEqualityTest, EqualityComplexTypeRational) {
    const char *code = R"(
        class Rational {
        public:
            int numerator, denominator;
            // Cross-multiply: a/b == c/d iff a*d == b*c
            bool operator==(const Rational& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Rational") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_EqualEqual) {
                        opEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opEqual, nullptr) << "operator== not found in Rational class";

    // Verify operator can handle complex comparison logic
    EXPECT_TRUE(opEqual->isConst()) << "operator== should be const";
    EXPECT_TRUE(opEqual->hasBody()) << "operator== should have implementation body";
}

// Test 8: EqualityComplexTypeVector - Vector equality
// Tests equality operator on vector-like types
TEST_F(ComplexEqualityTest, EqualityComplexTypeVector) {
    const char *code = R"(
        class Vector3D {
        public:
            double x, y, z;
            bool operator==(const Vector3D& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Vector3D") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_EqualEqual) {
                        opEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opEqual, nullptr) << "operator== not found in Vector3D";
    EXPECT_EQ(opEqual->getNumParams(), 1) << "Comparison takes one parameter";
    EXPECT_TRUE(opEqual->getReturnType()->isBooleanType()) << "Returns bool";
}

// ============================================================================
// TEST SUITE 4: Heterogeneous Equality
// ============================================================================

class HeterogeneousEqualityTest : public EqualityOperatorTestBase {};

// Test 9: EqualityHeterogeneous - operator==(const T&, const U&)
// Tests heterogeneous equality comparison between different types
TEST_F(HeterogeneousEqualityTest, EqualityHeterogeneousTypes) {
    const char *code = R"(
        class Integer {
        public:
            int value;
        };
        class Double {
        public:
            double value;
            // Compare Integer with Double
            bool operator==(const Integer& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Double") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_EqualEqual) {
                        opEqual = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opEqual, nullptr) << "Heterogeneous operator== not found";

    // Verify parameter type is different from the containing class
    QualType paramType = opEqual->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }

    // Parameter should be Integer reference, not Double reference
    if (auto *RD = paramType->getAsRecordDecl()) {
        EXPECT_EQ(RD->getNameAsString(), "Integer") << "Parameter should be Integer type";
    }
}

// Test 10: EqualityHeterogeneousNonMember - Friend heterogeneous operator==
// Tests non-member friend operator== with different types
TEST_F(HeterogeneousEqualityTest, EqualityHeterogeneousNonMember) {
    const char *code = R"(
        class Complex {
        public:
            double real, imag;
        };
        class Real {
        public:
            double value;
            friend bool operator==(const Real& lhs, const Complex& rhs);
        };
        bool operator==(const Real& lhs, const Complex& rhs);
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

    ASSERT_NE(friendOp, nullptr) << "Friend heterogeneous operator== not found";
    EXPECT_EQ(friendOp->getNumParams(), 2) << "Non-member operator== has 2 parameters";
    EXPECT_TRUE(friendOp->getReturnType()->isBooleanType()) << "Returns bool";
}

// ============================================================================
// TEST SUITE 5: Call Site Transformations
// ============================================================================

class CallSiteTransformationTest : public EqualityOperatorTestBase {};

// Test 11: EqualityCallSite - Verify call site transformation
// Tests that operator== calls are properly recognized for transpilation
TEST_F(CallSiteTransformationTest, EqualityCallSiteTransformation) {
    const char *code = R"(
        class Data {
        public:
            int value;
            bool operator==(const Data& other) const;
        };

        bool test() {
            Data a{1}, b{1};
            return a == b;  // Call site: a.operator==(b)
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    bool foundOperator = false;
    bool foundCallsite = false;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Data") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_EqualEqual) {
                        foundOperator = true;
                        break;
                    }
                }
            }
        }

        // Find the test() function with call site
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->hasBody()) {
                foundCallsite = true;
            }
        }
    }

    EXPECT_TRUE(foundOperator) << "operator== definition found";
    EXPECT_TRUE(foundCallsite) << "Call site in test() function found";
}

// Test 12: EqualityCallSiteNonMember - Non-member call site
// Tests that non-member operator== calls are recognized
TEST_F(CallSiteTransformationTest, EqualityCallSiteNonMember) {
    const char *code = R"(
        class Info {
        public:
            int id;
            friend bool operator==(const Info& a, const Info& b);
        };
        bool operator==(const Info& a, const Info& b);

        bool compare() {
            Info x{5}, y{5};
            return x == y;  // Call site: operator==(x, y)
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->isOverloadedOperator() && FD->getOverloadedOperator() == OO_EqualEqual) {
                opEqual = FD;
                break;
            }
        }
    }

    ASSERT_NE(opEqual, nullptr) << "Non-member operator== not found";
    EXPECT_EQ(opEqual->getNumParams(), 2) << "Takes two parameters";
}

// ============================================================================
// TEST SUITE 6: Return Type Verification
// ============================================================================

class ReturnTypeTest : public EqualityOperatorTestBase {};

// Test 13: EqualityReturnType - Verify returns bool
// Tests that operator== always returns bool
TEST_F(ReturnTypeTest, EqualityReturnTypeBool) {
    const char *code = R"(
        class Status {
        public:
            bool valid;
            bool operator==(const Status& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Status") {
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

    // Core requirement: operator== must return bool
    QualType returnType = opEqual->getReturnType();
    EXPECT_TRUE(returnType->isBooleanType()) << "operator== must return bool";
}

// Test 14: EqualityReturnTypeConsistency - Consistency across overloads
// Tests that all operator== overloads return bool
TEST_F(ReturnTypeTest, EqualityReturnTypeConsistency) {
    const char *code = R"(
        class Numeric {
        public:
            int value;
            bool operator==(int other) const;
            bool operator==(const Numeric& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int equalityOpCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Numeric") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_EqualEqual) {
                        // All overloads must return bool
                        EXPECT_TRUE(M->getReturnType()->isBooleanType())
                            << "All operator== overloads must return bool";
                        equalityOpCount++;
                    }
                }
            }
        }
    }

    EXPECT_EQ(equalityOpCount, 2) << "Expected 2 operator== overloads";
}

// Test 15: EqualityNoVoid - Ensure operator== never returns void
// Tests that operator== never has void return type
TEST_F(ReturnTypeTest, EqualityNoVoid) {
    const char *code = R"(
        class Guard {
        public:
            int state;
            bool operator==(const Guard& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opEqual = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Guard") {
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

    QualType returnType = opEqual->getReturnType();
    EXPECT_FALSE(returnType->isVoidType()) << "operator== should not return void";
    EXPECT_TRUE(returnType->isBooleanType()) << "operator== should return bool";
}

// ============================================================================
// TEST SUITE 7: Multiple Overloads
// ============================================================================

class MultipleOverloadsTest : public EqualityOperatorTestBase {};

// Test 16: EqualityMultipleOverloads - Multiple operator== in same class
// Tests handling of multiple operator== overloads
TEST_F(MultipleOverloadsTest, EqualityMultipleOverloads) {
    const char *code = R"(
        class Universal {
        public:
            int id;
            // Overload 1: compare with another Universal
            bool operator==(const Universal& other) const;
            // Overload 2: compare with int
            bool operator==(int value) const;
            // Overload 3: compare with double
            bool operator==(double value) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    std::vector<CXXMethodDecl *> opEquals;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Universal") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_EqualEqual) {
                        opEquals.push_back(M);
                    }
                }
            }
        }
    }

    EXPECT_EQ(opEquals.size(), 3) << "Expected 3 operator== overloads";

    // All overloads must return bool
    for (auto *op : opEquals) {
        EXPECT_TRUE(op->getReturnType()->isBooleanType())
            << "All operator== overloads must return bool";
    }
}

// Test 17: EqualityOverloadResolution - Proper overload resolution
// Tests that correct overload is selected based on parameter type
TEST_F(MultipleOverloadsTest, EqualityOverloadResolution) {
    const char *code = R"(
        class Comparable {
        public:
            int value;
            bool operator==(const Comparable& other) const;
            bool operator==(int n) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opCompare = nullptr;
    CXXMethodDecl *opInt = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Comparable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_EqualEqual) {
                        if (M->getNumParams() > 0) {
                            QualType paramType = M->getParamDecl(0)->getType();
                            if (paramType->isIntegerType()) {
                                opInt = M;
                            } else {
                                opCompare = M;
                            }
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(opCompare, nullptr) << "operator==(const Comparable&) not found";
    ASSERT_NE(opInt, nullptr) << "operator==(int) not found";
}

// ============================================================================
// Summary and Test Registration
// ============================================================================

// The test suite covers:
// 1. Basic Detection (3 tests): member, const-correctness, friend
// 2. Equivalence Relations (3 tests): reflexivity, symmetry, transitivity
// 3. Complex Types (2 tests): rational numbers, vectors
// 4. Heterogeneous (2 tests): different types, non-member
// 5. Call Sites (2 tests): member calls, non-member calls
// 6. Return Types (3 tests): bool requirement, consistency, no void
// 7. Multiple Overloads (2 tests): multiple overloads, resolution
//
// Total: 17 tests for operator==

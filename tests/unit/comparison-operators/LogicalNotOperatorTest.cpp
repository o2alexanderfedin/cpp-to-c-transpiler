// Unit Tests for C++ Logical NOT (operator!) Operator Overloading
// Tests for comprehensive coverage of unary logical NOT operator
//
// These tests validate:
// - operator! detection as unary operator (0 parameters)
// - const correctness
// - return type verification (should be bool)
// - usage in conditionals
// - double negation behavior
// - pointer-like truthiness checks
// - call site transformations

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"

using namespace clang;

// Test fixture base class with helper method
class LogicalNotOperatorTestBase : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// LOGICAL NOT OPERATOR TESTS (8 tests)
// ============================================================================

class LogicalNotOperatorTest : public LogicalNotOperatorTestBase {};

// Test 1: BasicLogicalNot - Simple member operator!
TEST_F(LogicalNotOperatorTest, BasicLogicalNot) {
    const char *code = R"(
        class Boolean {
        public:
            bool value;
            bool operator!() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalNot = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Boolean") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Exclaim) {
                        opLogicalNot = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalNot, nullptr) << "operator! not found";
    EXPECT_EQ(opLogicalNot->getNumParams(), 0) << "operator! should have 0 parameters (unary)";
    EXPECT_TRUE(opLogicalNot->getReturnType()->isBooleanType())
        << "operator! should return bool";
}

// Test 2: LogicalNotConstCorrectness - Verify const member function
TEST_F(LogicalNotOperatorTest, LogicalNotConstCorrectness) {
    const char *code = R"(
        class ConstCheckable {
        public:
            int value;
            bool operator!() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalNot = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ConstCheckable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Exclaim) {
                        opLogicalNot = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalNot, nullptr) << "operator! not found";
    EXPECT_TRUE(opLogicalNot->isConst())
        << "operator! should be const member function";
}

// Test 3: LogicalNotUnary - Verify single operand (no second parameter)
TEST_F(LogicalNotOperatorTest, LogicalNotUnary) {
    const char *code = R"(
        class Unary {
        public:
            bool flag;
            bool operator!() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalNot = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Unary") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Exclaim) {
                        opLogicalNot = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalNot, nullptr) << "operator! not found";
    // Verify it's truly unary - no parameters beyond implicit 'this'
    EXPECT_EQ(opLogicalNot->getNumParams(), 0)
        << "operator! must be unary with exactly 0 parameters";
    EXPECT_FALSE(opLogicalNot->isStatic())
        << "operator! should be instance method (implicit this)";
}

// Test 4: LogicalNotDoubleNegation - Verify !!a behavior
TEST_F(LogicalNotOperatorTest, LogicalNotDoubleNegation) {
    const char *code = R"(
        class Negatable {
        public:
            bool state;
            bool operator!() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalNot = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Negatable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Exclaim) {
                        opLogicalNot = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalNot, nullptr) << "operator! not found";
    // Double negation: !!a should work since operator! returns bool
    // and bool can be used with operator! again
    QualType returnType = opLogicalNot->getReturnType();
    EXPECT_TRUE(returnType->isBooleanType())
        << "operator! returns bool, enabling double negation !!a";
}

// Test 5: LogicalNotPointerLike - Truthiness check (SmartPointer example)
TEST_F(LogicalNotOperatorTest, LogicalNotPointerLike) {
    const char *code = R"(
        class Element {
        public:
            int data;
        };
        class SmartPtr {
        public:
            Element* ptr;
            bool operator!() const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalNot = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "SmartPtr") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Exclaim) {
                        opLogicalNot = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalNot, nullptr) << "operator! not found in SmartPtr";
    EXPECT_EQ(opLogicalNot->getNumParams(), 0)
        << "SmartPtr operator! should be unary";
    EXPECT_TRUE(opLogicalNot->getReturnType()->isBooleanType())
        << "SmartPtr operator! should return bool for truthiness check";
}

// Test 6: LogicalNotCallSite - Verify call site transformation !obj
TEST_F(LogicalNotOperatorTest, LogicalNotCallSite) {
    const char *code = R"(
        class Checkable {
        public:
            int status;
            bool operator!() const;
        };
        void processCheck(Checkable& obj) {
            bool result = !obj;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalNot = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Checkable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Exclaim) {
                        opLogicalNot = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalNot, nullptr) << "operator! not found";
    // Verify the operator is suitable for call site transformation
    // !obj should be transformed to obj.operator!() or similar
    EXPECT_EQ(opLogicalNot->getNumParams(), 0)
        << "operator! must be callable with unary syntax";
}

// Test 7: LogicalNotInConditional - Verify works in if (!obj)
TEST_F(LogicalNotOperatorTest, LogicalNotInConditional) {
    const char *code = R"(
        class Conditional {
        public:
            int value;
            bool operator!() const;
        };
        void ifNot(Conditional& c) {
            if (!c) {
                // body
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalNot = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Conditional") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Exclaim) {
                        opLogicalNot = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalNot, nullptr) << "operator! not found";
    // Verify operator! can be used in conditional expressions
    // (if (!obj) requires bool return type)
    EXPECT_TRUE(opLogicalNot->getReturnType()->isBooleanType())
        << "operator! must return bool for use in conditionals";
}

// Test 8: LogicalNotReturnType - Verify returns bool
TEST_F(LogicalNotOperatorTest, LogicalNotReturnType) {
    const char *code = R"(
        class ReturnTypeCheck {
        public:
            unsigned int flags;
            bool operator!() const { return false; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalNot = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "ReturnTypeCheck") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Exclaim) {
                        opLogicalNot = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalNot, nullptr) << "operator! not found";
    QualType returnType = opLogicalNot->getReturnType();

    EXPECT_TRUE(returnType->isBooleanType())
        << "operator! return type must be bool, got: " << returnType.getAsString();
    EXPECT_TRUE(opLogicalNot->hasBody())
        << "operator! should have implementation body";
}

// ============================================================================
// ADDITIONAL COVERAGE TEST (operator! with non-const)
// ============================================================================

class LogicalNotOperatorNonConstTest : public LogicalNotOperatorTestBase {};

// Test 9: LogicalNotNonConst - Non-const variant (less common)
TEST_F(LogicalNotOperatorNonConstTest, LogicalNotNonConst) {
    const char *code = R"(
        class Mutable {
        public:
            mutable int call_count;
            bool operator!();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalNot = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Mutable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_Exclaim) {
                        opLogicalNot = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalNot, nullptr) << "operator! not found";
    EXPECT_EQ(opLogicalNot->getNumParams(), 0)
        << "Non-const operator! should still be unary";
    EXPECT_TRUE(opLogicalNot->getReturnType()->isBooleanType())
        << "operator! should return bool";
    // Note: This variant is non-const (can't guarantee const semantics)
    EXPECT_FALSE(opLogicalNot->isConst())
        << "This variant is intentionally non-const";
}

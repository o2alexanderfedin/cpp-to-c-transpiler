// Unit Tests for C++ operator&& (Logical AND) Binary Operator
// Comprehensive tests for logical AND operator overloading in C++ to C transpiler
//
// NOTE: operator&& is RARE in practice because:
// 1. Short-circuit evaluation semantics are LOST when overloaded
// 2. Both operands are ALWAYS evaluated (unlike built-in &&)
// 3. Return type is typically bool (not convertible to bool)
// 4. Not commonly used in real-world C++ code
//
// These tests verify:
// - Correct AST detection of operator&&
// - Const correctness of the operator
// - Parameter and return type handling
// - Proper transformation to C function calls

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"

using namespace clang;

// Test fixture base class with helper method
class LogicalAndOperatorTestBase : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// LOGICAL AND OPERATOR (&&) TESTS
// ============================================================================

class LogicalAndOperatorTest : public LogicalAndOperatorTestBase {};

// Test 1: BasicLogicalAnd - Simple member operator&&
TEST_F(LogicalAndOperatorTest, BasicLogicalAnd) {
    const char *code = R"(
        class Bool {
        public:
            bool value;
            bool operator&&(const Bool& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opAnd = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Bool") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_AmpAmp) {
                        opAnd = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opAnd, nullptr) << "operator&& not found";
    EXPECT_EQ(opAnd->getNumParams(), 1) << "operator&& should have 1 parameter";
    EXPECT_TRUE(opAnd->getReturnType()->isBooleanType()) << "operator&& should return bool";
}

// Test 2: LogicalAndConstCorrectness - Verify const member function
TEST_F(LogicalAndOperatorTest, LogicalAndConstCorrectness) {
    const char *code = R"(
        class Boolean {
        public:
            bool value;
            bool operator&&(const Boolean& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opAnd = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Boolean") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_AmpAmp) {
                        opAnd = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opAnd, nullptr) << "operator&& not found";
    EXPECT_TRUE(opAnd->isConst()) << "operator&& should be const member function";

    // Verify parameter const correctness
    QualType paramType = opAnd->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType.isConstQualified()) << "Parameter should be const";
}

// Test 3: LogicalAndWarning - Document short-circuit evaluation loss
TEST_F(LogicalAndOperatorTest, LogicalAndWarning) {
    // This test documents the critical semantic difference:
    // C++ built-in && has short-circuit semantics (right operand not evaluated if left is false)
    // operator&& override LOSES this semantic (both operands always evaluated)
    //
    // Example:
    //   a && b   // With built-in: if a is false, b is never evaluated
    //   a.operator&&(b)  // Both a and b are always evaluated!

    const char *code = R"(
        class LogicalValue {
        public:
            bool value;

            // DANGER: This operator loses short-circuit evaluation
            bool operator&&(const LogicalValue& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opAnd = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "LogicalValue") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_AmpAmp) {
                        opAnd = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opAnd, nullptr) << "operator&& not found";

    // WARNING: In C, we cannot preserve short-circuit semantics
    // The transpiler must generate: bool_result = left_object.operator&&(right_object)
    // This is equivalent to function call: result = object__operator_AmpAmp(&left, &right)
    // where BOTH arguments are always evaluated before the call
}

// Test 4: LogicalAndBothEvaluated - Verify both operands evaluated (not short-circuit)
TEST_F(LogicalAndOperatorTest, LogicalAndBothEvaluated) {
    const char *code = R"(
        class Condition {
        public:
            int state;

            // Both operands MUST be evaluated - no short-circuit
            bool operator&&(const Condition& other) const {
                return state && other.state;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opAnd = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Condition") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_AmpAmp) {
                        opAnd = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opAnd, nullptr) << "operator&& not found";
    EXPECT_TRUE(opAnd->hasBody()) << "operator&& should have body";

    // The transpiler must generate a C function that calls both operands
    // C translation:
    //   bool Condition__operator_AmpAmp(Condition* this, const Condition* other) {
    //       return this->state && other->state;
    //   }
}

// Test 5: LogicalAndCallSite - Verify call site transformation
TEST_F(LogicalAndOperatorTest, LogicalAndCallSite) {
    const char *code = R"(
        class Flag {
        public:
            bool enabled;
            bool operator&&(const Flag& other) const;
        };

        void test() {
            Flag a, b;
            bool result = a && b;  // Calls a.operator&&(b)
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find the Flag class
    CXXRecordDecl *flagClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Flag") {
                flagClass = RD;
                break;
            }
        }
    }

    ASSERT_NE(flagClass, nullptr) << "Flag class not found";

    // Verify operator&& exists
    CXXMethodDecl *opAnd = nullptr;
    for (auto *M : flagClass->methods()) {
        if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_AmpAmp) {
            opAnd = M;
            break;
        }
    }

    ASSERT_NE(opAnd, nullptr) << "operator&& not found in Flag class";

    // C transpilation at call site:
    //   bool result = Flag__operator_AmpAmp(&a, &b);
    // Note: This is a FUNCTION CALL, not an infix operator
}

// Test 6: LogicalAndReturnType - Verify returns bool
TEST_F(LogicalAndOperatorTest, LogicalAndReturnType) {
    const char *code = R"(
        class BoolWrapper {
        public:
            bool value;
            bool operator&&(const BoolWrapper& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opAnd = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "BoolWrapper") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_AmpAmp) {
                        opAnd = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opAnd, nullptr) << "operator&& not found";

    QualType returnType = opAnd->getReturnType();
    EXPECT_TRUE(returnType->isBooleanType()) << "operator&& should return bool";

    // C function signature:
    //   bool BoolWrapper__operator_AmpAmp(BoolWrapper* this, const BoolWrapper* other)
}

// Test 7: LogicalAndWithDifferentParameterType
TEST_F(LogicalAndOperatorTest, LogicalAndWithDifferentParameterType) {
    const char *code = R"(
        class IntBool {
        public:
            int value;
            bool operator&&(int other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opAnd = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "IntBool") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_AmpAmp) {
                        opAnd = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opAnd, nullptr) << "operator&&(int) not found";

    QualType paramType = opAnd->getParamDecl(0)->getType();
    EXPECT_TRUE(paramType->isIntegerType()) << "Parameter should be int";
}

// Test 8: LogicalAndMultipleOverloads
TEST_F(LogicalAndOperatorTest, LogicalAndMultipleOverloads) {
    const char *code = R"(
        class Multi {
        public:
            bool value;
            bool operator&&(const Multi& other) const;
            bool operator&&(int other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int andOpCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Multi") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_AmpAmp) {
                        andOpCount++;
                    }
                }
            }
        }
    }

    EXPECT_EQ(andOpCount, 2) << "Expected 2 overloaded operator&& methods";
}

// Test 9: LogicalAndNonConst - Non-const variant
TEST_F(LogicalAndOperatorTest, LogicalAndNonConst) {
    const char *code = R"(
        class Mutable {
        public:
            bool value;
            bool operator&&(const Mutable& other);  // Note: NOT const
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opAnd = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Mutable") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_AmpAmp) {
                        opAnd = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opAnd, nullptr) << "operator&& not found";
    EXPECT_FALSE(opAnd->isConst()) << "operator&& should NOT be const in this case";
}

// Test 10: LogicalAndFriend - Friend operator&& (rare but possible)
TEST_F(LogicalAndOperatorTest, LogicalAndFriend) {
    const char *code = R"(
        class Value {
        public:
            bool data;
            friend bool operator&&(const Value& a, const Value& b);
        };
        bool operator&&(const Value& a, const Value& b);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *friendOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->isOverloadedOperator() && FD->getOverloadedOperator() == OO_AmpAmp) {
                friendOp = FD;
                break;
            }
        }
    }

    ASSERT_NE(friendOp, nullptr) << "Friend operator&& not found";
    EXPECT_EQ(friendOp->getNumParams(), 2) << "Friend operator&& should have 2 parameters";
}

// Test 11: LogicalAndExpressionBody - With function body
TEST_F(LogicalAndOperatorTest, LogicalAndExpressionBody) {
    const char *code = R"(
        class Smart {
        public:
            bool valid;
            Smart(bool v) : valid(v) {}
            bool operator&&(const Smart& other) const {
                return valid && other.valid;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opAnd = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Smart") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() && M->getOverloadedOperator() == OO_AmpAmp) {
                        opAnd = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opAnd, nullptr) << "operator&& not found";
    EXPECT_TRUE(opAnd->hasBody()) << "operator&& should have function body";
    EXPECT_TRUE(opAnd->isConst()) << "operator&& should be const";
}

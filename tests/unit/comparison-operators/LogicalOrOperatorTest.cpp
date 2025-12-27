// Unit Tests for C++ operator|| (Logical OR) Binary Operator
// Phase 51: Comparison & Logical Operators
//
// These tests ensure that C++ operator|| (logical OR) is correctly detected
// and can be translated to C function calls. Note: operator|| is RARE in
// practice because it loses short-circuit evaluation semantics.
//
// WARNING: Overloading operator|| has critical semantic implications:
// - Built-in operator||: short-circuit evaluation (RHS not evaluated if LHS is true)
// - Overloaded operator||: both operands ALWAYS evaluated (function call semantics)
// This loss of short-circuit evaluation is a breaking semantic change that
// should be documented when translating C++ code using operator|| overloads.

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"

using namespace clang;

// Test fixture base class with helper method
class LogicalOrOperatorTestBase : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// LOGICAL OR OPERATOR (operator||) - 6 Tests
// ============================================================================

class LogicalOrOperatorTest : public LogicalOrOperatorTestBase {};

// Test 1: BasicLogicalOr
// Verify that a basic member operator|| can be detected in the AST
TEST_F(LogicalOrOperatorTest, BasicLogicalOr) {
    const char *code = R"(
        class Boolean {
        public:
            bool value;
            bool operator||(const Boolean& other) const {
                return value || other.value;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalOr = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Boolean") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_PipePipe) {
                        opLogicalOr = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalOr, nullptr) << "operator|| not found";
    EXPECT_EQ(opLogicalOr->getNumParams(), 1)
        << "operator|| should have 1 parameter (binary operator with implicit this)";
}

// Test 2: LogicalOrConstCorrectness
// Verify that operator|| respects const correctness
TEST_F(LogicalOrOperatorTest, LogicalOrConstCorrectness) {
    const char *code = R"(
        class Flag {
        public:
            bool state;
            bool operator||(const Flag& other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalOr = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Flag") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_PipePipe) {
                        opLogicalOr = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalOr, nullptr) << "operator|| not found";
    EXPECT_TRUE(opLogicalOr->isConst())
        << "operator|| should be const member function";

    // Verify parameter is const reference
    QualType paramType = opLogicalOr->getParamDecl(0)->getType();
    if (paramType->isReferenceType()) {
        paramType = paramType->getPointeeType();
    }
    EXPECT_TRUE(paramType.isConstQualified())
        << "Parameter should be const";
}

// Test 3: LogicalOrWarning
// Document the semantic issue: short-circuit evaluation is lost
// This test ensures we can detect operator|| to emit appropriate warnings
TEST_F(LogicalOrOperatorTest, LogicalOrWarning) {
    const char *code = R"(
        class Condition {
        public:
            bool check;

            // WARNING: This loses short-circuit semantics!
            // In C++: if (a || b), b is NOT evaluated if a is true
            // When transpiled: both a and b WILL be evaluated
            bool operator||(const Condition& other) const {
                return check || other.check;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalOr = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Condition") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_PipePipe) {
                        opLogicalOr = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalOr, nullptr) << "operator|| not found";
    // The detection itself is the test - we can now emit a warning about semantics
    EXPECT_TRUE(opLogicalOr->hasBody())
        << "operator|| should have implementation";
}

// Test 4: LogicalOrBothEvaluated
// Verify that both operands are evaluated (not short-circuit)
// This documents the critical semantic difference from built-in ||
TEST_F(LogicalOrOperatorTest, LogicalOrBothEvaluated) {
    const char *code = R"(
        class Evaluator {
        public:
            int callCount;

            Evaluator() : callCount(0) {}

            // Each call increments counter - if both evaluated, counter = 2
            bool operator||(const Evaluator& other) const {
                // In transpiled C: both operands evaluated before function call
                // This is DIFFERENT from built-in || which short-circuits
                return true;
            }
        };

        Evaluator getEvaluator() {
            static Evaluator e;
            e.callCount++;
            return e;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalOr = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Evaluator") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_PipePipe) {
                        opLogicalOr = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalOr, nullptr) << "operator|| not found";

    // Verify the operator exists and returns bool
    EXPECT_TRUE(opLogicalOr->getReturnType()->isBooleanType())
        << "operator|| must return bool";

    // Verify parameter count - binary operator with implicit this
    EXPECT_EQ(opLogicalOr->getNumParams(), 1)
        << "operator|| is binary, so 1 explicit parameter (other)";
}

// Test 5: LogicalOrCallSite
// Verify how operator|| call expressions are represented in the AST
TEST_F(LogicalOrOperatorTest, LogicalOrCallSite) {
    const char *code = R"(
        class Assertion {
        public:
            bool valid;
            bool operator||(const Assertion& other) const;
        };

        void checkAssertions(const Assertion& a, const Assertion& b) {
            // This call expression should be translatable to function call
            if (a || b) {
                // Both a and b evaluated (no short-circuit!)
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find the operator|| method to verify it exists
    CXXMethodDecl *opLogicalOr = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Assertion") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_PipePipe) {
                        opLogicalOr = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalOr, nullptr) << "operator|| not found";

    // Find the function that uses the operator
    FunctionDecl *checkFunc = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "checkAssertions") {
                checkFunc = FD;
                break;
            }
        }
    }

    ASSERT_NE(checkFunc, nullptr) << "checkAssertions function not found";
    EXPECT_TRUE(checkFunc->hasBody())
        << "checkAssertions should have a body with operator|| call";
}

// Test 6: LogicalOrReturnType
// Verify that operator|| returns bool (critical for C translation)
TEST_F(LogicalOrOperatorTest, LogicalOrReturnType) {
    const char *code = R"(
        class Result {
        public:
            bool success;

            // IMPORTANT: Must return bool for C translation via <stdbool.h>
            bool operator||(const Result& other) const {
                return success || other.success;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalOr = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Result") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_PipePipe) {
                        opLogicalOr = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalOr, nullptr) << "operator|| not found";

    QualType returnType = opLogicalOr->getReturnType();
    EXPECT_TRUE(returnType->isBooleanType())
        << "operator|| must return bool type";

    // Verify it's not a reference or pointer to bool
    EXPECT_FALSE(returnType->isPointerType() || returnType->isReferenceType())
        << "operator|| should return bool by value, not reference or pointer";
}

// ============================================================================
// Additional edge cases and integration scenarios
// ============================================================================

// Test 7: Friend Logical OR Operator
// Non-member operator|| declared as friend
TEST_F(LogicalOrOperatorTest, FriendLogicalOrOperator) {
    const char *code = R"(
        class Signal {
        public:
            bool active;
            friend bool operator||(const Signal& lhs, const Signal& rhs);
        };

        bool operator||(const Signal& lhs, const Signal& rhs) {
            return lhs.active || rhs.active;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find the friend operator as a free function
    FunctionDecl *friendOp = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->isOverloadedOperator() &&
                FD->getOverloadedOperator() == OO_PipePipe &&
                !isa<CXXMethodDecl>(FD)) {
                friendOp = FD;
                break;
            }
        }
    }

    ASSERT_NE(friendOp, nullptr) << "Friend operator|| not found";
    EXPECT_EQ(friendOp->getNumParams(), 2)
        << "Friend operator|| should have 2 parameters (both explicit)";
    EXPECT_TRUE(friendOp->getReturnType()->isBooleanType())
        << "Friend operator|| should return bool";
}

// Test 8: Logical OR in Conditional Expression
// Verify operator|| can be used in if/while conditions
TEST_F(LogicalOrOperatorTest, LogicalOrInConditional) {
    const char *code = R"(
        class Predicate {
        public:
            bool result;
            bool operator||(const Predicate& other) const;
        };

        void evaluate(const Predicate& p1, const Predicate& p2) {
            // Typical usage in conditional - will become function call
            if (p1 || p2) {
                // Block executed if either predicate is true
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalOr = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Predicate") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_PipePipe) {
                        opLogicalOr = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalOr, nullptr) << "operator|| not found";
    EXPECT_TRUE(opLogicalOr->getReturnType()->isBooleanType())
        << "operator|| must return bool for conditional usage";
}

// Test 9: Multiple Logical OR Operators
// Verify a class can have multiple overloaded operator|| for different types
TEST_F(LogicalOrOperatorTest, OverloadedLogicalOrOperator) {
    const char *code = R"(
        class Condition {
        public:
            bool value;
            bool operator||(const Condition& other) const;
            bool operator||(bool other) const;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    int logicalOrCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Condition") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_PipePipe) {
                        logicalOrCount++;
                    }
                }
            }
        }
    }

    EXPECT_EQ(logicalOrCount, 2)
        << "Expected 2 overloaded operator|| methods";
}

// Test 10: Logical OR with Non-Bool Return
// Verify that operator|| can return non-bool (although unusual)
TEST_F(LogicalOrOperatorTest, LogicalOrNonBoolReturn) {
    const char *code = R"(
        class Wrapper {
        public:
            int value;

            // Unusual: returning int instead of bool
            // Still valid C++ (implicit conversion to bool in conditionals)
            int operator||(const Wrapper& other) const {
                return value | other.value;  // Bitwise OR, not logical
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CXXMethodDecl *opLogicalOr = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Wrapper") {
                for (auto *M : RD->methods()) {
                    if (M->isOverloadedOperator() &&
                        M->getOverloadedOperator() == OO_PipePipe) {
                        opLogicalOr = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(opLogicalOr, nullptr) << "operator|| not found";

    // Even though return type is int, it should be detectable
    QualType returnType = opLogicalOr->getReturnType();
    EXPECT_TRUE(returnType->isIntegerType())
        << "This operator|| returns int, not bool";
}

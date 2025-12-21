// tests/gtest/ACSLBehaviorAnnotatorTest_GTest.cpp
// Unit tests for ACSL Behavior Annotator (Phase 5, v1.22.0)
// Migrated to Google Test framework
//
// Phase 5: ACSL Function Behaviors
// Plan: .planning/phases/05-function-behaviors/PLAN.md
//
// Comprehensive test suite for behavior extraction (15 tests)

#include "../../include/ACSLBehaviorAnnotator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>
#include <vector>

using namespace clang;
using namespace std;

// Store AST units to prevent premature destruction
// FIX: Heap-use-after-free bug - keeps ASTUnits alive until program exit
static vector<unique_ptr<ASTUnit>> persistentASTs;

// Test helper: Extract FunctionDecl from source code
class FunctionExtractor : public RecursiveASTVisitor<FunctionExtractor> {
public:
    vector<const FunctionDecl*> functions;

    bool VisitFunctionDecl(FunctionDecl* decl) {
        if (decl->isThisDeclarationADefinition() && !decl->isMain()) {
            functions.push_back(decl);
        }
        return true;
    }
};

// Test fixture for ACSL Behavior Annotator
class ACSLBehaviorAnnotatorTest : public ::testing::Test {
protected:
    ACSLBehaviorAnnotator annotator;

    // Helper: Parse C++ code and extract first function
    const FunctionDecl* parseFunction(const string& code) {
        vector<string> args = {"-std=c++17"};
        unique_ptr<ASTUnit> AST = tooling::buildASTFromCodeWithArgs(code, args);
        if (!AST) return nullptr;

        FunctionExtractor extractor;
        extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        const FunctionDecl* result = nullptr;
        if (!extractor.functions.empty()) {
            result = extractor.functions[0];
        }

        // Keep AST alive until program exit to prevent dangling pointers
        persistentASTs.push_back(std::move(AST));
        return result;
    }

    void SetUp() override {
        annotator = ACSLBehaviorAnnotator();
    }
};

// Test 1: SimpleBehaviorExtraction - If/else → 2 behaviors
TEST_F(ACSLBehaviorAnnotatorTest, SimpleBehaviorExtraction) {
    string code = R"(
        int getValue(int *p) {
            if (p == nullptr) {
                return -1;
            }
            return *p;
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify behaviors exist
    EXPECT_FALSE(behaviorCode.empty()) << "Behavior code should not be empty";
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should contain behavior declarations";
    EXPECT_NE(behaviorCode.find("assumes"), string::npos)
        << "Should contain assumes clauses";
    EXPECT_NE(behaviorCode.find("ensures"), string::npos)
        << "Should contain ensures clauses";

    // Verify completeness and disjointness
    EXPECT_NE(behaviorCode.find("complete behaviors"), string::npos)
        << "Should have completeness clause";
    EXPECT_NE(behaviorCode.find("disjoint behaviors"), string::npos)
        << "Should have disjointness clause";
}

// Test 2: SwitchBehaviors - Switch → N behaviors
TEST_F(ACSLBehaviorAnnotatorTest, SwitchBehaviors) {
    string code = R"(
        int classify(int value) {
            switch (value) {
                case 0: return -1;
                case 1: return 0;
                case 2: return 1;
                default: return -2;
            }
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify multiple behaviors from switch
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should extract behaviors from switch";
    EXPECT_NE(behaviorCode.find("assumes"), string::npos)
        << "Should have assumes clauses for each case";
}

// Test 3: CompletenessCheck - Complete behaviors verified
TEST_F(ACSLBehaviorAnnotatorTest, CompletenessCheck) {
    string code = R"(
        int absValue(int x) {
            if (x >= 0) {
                return x;
            } else {
                return -x;
            }
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify completeness declaration
    EXPECT_NE(behaviorCode.find("complete behaviors"), string::npos)
        << "Should declare behaviors as complete";

    // Complete means all input cases covered (x >= 0 OR x < 0)
    bool isComplete = annotator.checkCompleteness(func);
    EXPECT_TRUE(isComplete) << "Behaviors should be complete";
}

// Test 4: DisjointnessCheck - Disjoint behaviors verified
TEST_F(ACSLBehaviorAnnotatorTest, DisjointnessCheck) {
    string code = R"(
        int sign(int x) {
            if (x > 0) return 1;
            if (x < 0) return -1;
            return 0;
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify disjointness declaration
    EXPECT_NE(behaviorCode.find("disjoint behaviors"), string::npos)
        << "Should declare behaviors as disjoint";

    // Disjoint means no overlapping conditions
    bool isDisjoint = annotator.checkDisjointness(func);
    EXPECT_TRUE(isDisjoint) << "Behaviors should be disjoint";
}

// Test 5: NestedConditionBehaviors - Nested if/else
TEST_F(ACSLBehaviorAnnotatorTest, NestedConditionBehaviors) {
    string code = R"(
        int processValue(int x, int y) {
            if (x > 0) {
                if (y > 0) {
                    return x + y;
                } else {
                    return x;
                }
            } else {
                return 0;
            }
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify nested behaviors are extracted
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should extract behaviors from nested conditions";
    EXPECT_NE(behaviorCode.find("assumes"), string::npos)
        << "Should have assumes for nested paths";
}

// Test 6: ErrorBehavior - Error return path
TEST_F(ACSLBehaviorAnnotatorTest, ErrorBehavior) {
    string code = R"(
        int divide(int a, int b) {
            if (b == 0) {
                return -1;  // Error
            }
            return a / b;
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify error behavior detected
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should detect error behavior";
    EXPECT_TRUE(behaviorCode.find("error") != string::npos ||
                behaviorCode.find("b == 0") != string::npos)
        << "Should identify error condition";
}

// Test 7: NormalBehavior - Success path
TEST_F(ACSLBehaviorAnnotatorTest, NormalBehavior) {
    string code = R"(
        int addPositive(int a, int b) {
            if (a > 0 && b > 0) {
                return a + b;
            }
            return 0;
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify normal/success behavior
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should detect normal behavior";
    EXPECT_NE(behaviorCode.find("assumes"), string::npos)
        << "Should have success path assumptions";
}

// Test 8: MultipleReturnBehaviors - Multiple return points
TEST_F(ACSLBehaviorAnnotatorTest, MultipleReturnBehaviors) {
    string code = R"(
        int findFirst(int arr[], int size, int value) {
            if (arr == nullptr) return -1;
            if (size <= 0) return -1;
            for (int i = 0; i < size; i++) {
                if (arr[i] == value) return i;
            }
            return -1;
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify multiple return behaviors
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should extract behaviors for multiple returns";
}

// Test 9: GuardedPointerBehaviors - Null check patterns
TEST_F(ACSLBehaviorAnnotatorTest, GuardedPointerBehaviors) {
    string code = R"(
        int safeDeref(int *ptr) {
            if (ptr == nullptr) {
                return 0;
            }
            return *ptr;
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify null check behaviors
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should detect null check behaviors";
    EXPECT_TRUE(behaviorCode.find("null") != string::npos ||
                behaviorCode.find("ptr == \\null") != string::npos)
        << "Should reference null check";
}

// Test 10: RangeBehaviors - Value range conditions
TEST_F(ACSLBehaviorAnnotatorTest, RangeBehaviors) {
    string code = R"(
        int clamp(int value, int min, int max) {
            if (value < min) return min;
            if (value > max) return max;
            return value;
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify range-based behaviors
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should extract range-based behaviors";
    EXPECT_NE(behaviorCode.find("assumes"), string::npos)
        << "Should have range assumptions";
}

// Test 11: FlagBehaviors - Boolean flag conditions
TEST_F(ACSLBehaviorAnnotatorTest, FlagBehaviors) {
    string code = R"(
        int process(bool flag, int value) {
            if (flag) {
                return value * 2;
            } else {
                return value;
            }
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify flag-based behaviors
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should extract flag-based behaviors";
}

// Test 12: EnumBehaviors - Enum-based dispatch
TEST_F(ACSLBehaviorAnnotatorTest, EnumBehaviors) {
    string code = R"(
        enum Color { RED, GREEN, BLUE };
        int getColorValue(Color c) {
            if (c == RED) return 1;
            if (c == GREEN) return 2;
            if (c == BLUE) return 3;
            return 0;
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify enum-based behaviors
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should extract enum-based behaviors";
}

// Test 13: OverlappingBehaviorsWarning - Detect overlap
TEST_F(ACSLBehaviorAnnotatorTest, OverlappingBehaviorsWarning) {
    string code = R"(
        int overlapping(int x) {
            if (x > 0) return 1;
            if (x >= 0) return 2;  // Overlaps with x > 0
            return 0;
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    // Check for overlapping behaviors
    bool isDisjoint = annotator.checkDisjointness(func);
    EXPECT_FALSE(isDisjoint) << "Should detect overlapping behaviors";
}

// Test 14: IncompleteBehaviorsWarning - Detect gaps
TEST_F(ACSLBehaviorAnnotatorTest, IncompleteBehaviorsWarning) {
    string code = R"(
        int incomplete(int x) {
            if (x > 0) return 1;
            if (x < -10) return -1;
            // Gap: -10 <= x <= 0 not covered
        }
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    // Check for incomplete behaviors
    bool isComplete = annotator.checkCompleteness(func);
    EXPECT_FALSE(isComplete) << "Should detect incomplete behaviors";
}

// Test 15: BehaviorInheritance - Virtual function behaviors
TEST_F(ACSLBehaviorAnnotatorTest, BehaviorInheritance) {
    string code = R"(
        class Base {
        public:
            virtual int compute(int x) {
                if (x > 0) return x;
                return 0;
            }
        };
    )";

    const FunctionDecl* func = parseFunction(code);
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string behaviorCode = annotator.generateBehaviors(func);

    // Verify behaviors work with virtual functions
    EXPECT_NE(behaviorCode.find("behavior"), string::npos)
        << "Should extract behaviors from virtual functions";
}

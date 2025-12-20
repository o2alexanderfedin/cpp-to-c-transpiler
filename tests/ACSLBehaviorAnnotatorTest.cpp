// Phase 5 (v1.22.0): ACSL Function Behaviors
// Plan: .planning/phases/05-function-behaviors/PLAN.md
//
// Test-Driven Development: Comprehensive test suite for behavior extraction
//
// Test coverage (15+ tests as per plan):
// 1. SimpleBehaviorExtraction - If/else → 2 behaviors
// 2. SwitchBehaviors - Switch → N behaviors
// 3. CompletenessCheck - Complete behaviors verified
// 4. DisjointnessCheck - Disjoint behaviors verified
// 5. NestedConditionBehaviors - Nested if/else
// 6. ErrorBehavior - Error return path
// 7. NormalBehavior - Success path
// 8. MultipleReturnBehaviors - Multiple return points
// 9. GuardedPointerBehaviors - Null check patterns
// 10. RangeBehaviors - Value range conditions
// 11. FlagBehaviors - Boolean flag conditions
// 12. EnumBehaviors - Enum-based dispatch
// 13. OverlappingBehaviorsWarning - Detect overlap
// 14. IncompleteBehaviorsWarning - Detect gaps
// 15. BehaviorInheritance - Virtual function behaviors

#include "ACSLBehaviorAnnotator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <string>

using namespace clang;

// Test helper: Extract FunctionDecl from source code
class FunctionExtractor : public RecursiveASTVisitor<FunctionExtractor> {
public:
    std::vector<const FunctionDecl*> functions;

    bool VisitFunctionDecl(FunctionDecl* decl) {
        if (decl->isThisDeclarationADefinition() && !decl->isMain()) {
            functions.push_back(decl);
        }
        return true;
    }
};

// Test helper: Parse C++ code and extract AST nodes
std::unique_ptr<ASTUnit> parseCode(const std::string& code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args);
}

// Test 1: SimpleBehaviorExtraction - If/else → 2 behaviors
void testSimpleBehaviorExtraction() {
    std::cout << "Test 1: SimpleBehaviorExtraction - If/else → 2 behaviors... ";

    std::string code = R"(
        int getValue(int *p) {
            if (p == nullptr) {
                return -1;
            }
            return *p;
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify behaviors exist
    assert(!behaviorCode.empty() && "Behavior code should not be empty");
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should contain behavior declarations");
    assert(behaviorCode.find("assumes") != std::string::npos &&
           "Should contain assumes clauses");
    assert(behaviorCode.find("ensures") != std::string::npos &&
           "Should contain ensures clauses");

    // Verify completeness and disjointness
    assert(behaviorCode.find("complete behaviors") != std::string::npos &&
           "Should have completeness clause");
    assert(behaviorCode.find("disjoint behaviors") != std::string::npos &&
           "Should have disjointness clause");

    std::cout << "PASSED\n";
}

// Test 2: SwitchBehaviors - Switch → N behaviors
void testSwitchBehaviors() {
    std::cout << "Test 2: SwitchBehaviors - Switch → N behaviors... ";

    std::string code = R"(
        int classify(int value) {
            switch (value) {
                case 0: return -1;
                case 1: return 0;
                case 2: return 1;
                default: return -2;
            }
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify multiple behaviors from switch
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should extract behaviors from switch");
    assert(behaviorCode.find("assumes") != std::string::npos &&
           "Should have assumes clauses for each case");

    std::cout << "PASSED\n";
}

// Test 3: CompletenessCheck - Complete behaviors verified
void testCompletenessCheck() {
    std::cout << "Test 3: CompletenessCheck - Complete behaviors verified... ";

    std::string code = R"(
        int absValue(int x) {
            if (x >= 0) {
                return x;
            } else {
                return -x;
            }
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify completeness declaration
    assert(behaviorCode.find("complete behaviors") != std::string::npos &&
           "Should declare behaviors as complete");

    // Complete means all input cases covered (x >= 0 OR x < 0)
    bool isComplete = annotator.checkCompleteness(func);
    assert(isComplete && "Behaviors should be complete");

    std::cout << "PASSED\n";
}

// Test 4: DisjointnessCheck - Disjoint behaviors verified
void testDisjointnessCheck() {
    std::cout << "Test 4: DisjointnessCheck - Disjoint behaviors verified... ";

    std::string code = R"(
        int sign(int x) {
            if (x > 0) return 1;
            if (x < 0) return -1;
            return 0;
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify disjointness declaration
    assert(behaviorCode.find("disjoint behaviors") != std::string::npos &&
           "Should declare behaviors as disjoint");

    // Disjoint means no overlapping conditions
    bool isDisjoint = annotator.checkDisjointness(func);
    assert(isDisjoint && "Behaviors should be disjoint");

    std::cout << "PASSED\n";
}

// Test 5: NestedConditionBehaviors - Nested if/else
void testNestedConditionBehaviors() {
    std::cout << "Test 5: NestedConditionBehaviors - Nested if/else... ";

    std::string code = R"(
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

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify nested behaviors are extracted
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should extract behaviors from nested conditions");
    assert(behaviorCode.find("assumes") != std::string::npos &&
           "Should have assumes for nested paths");

    std::cout << "PASSED\n";
}

// Test 6: ErrorBehavior - Error return path
void testErrorBehavior() {
    std::cout << "Test 6: ErrorBehavior - Error return path... ";

    std::string code = R"(
        int divide(int a, int b) {
            if (b == 0) {
                return -1;  // Error
            }
            return a / b;
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify error behavior detected
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should detect error behavior");
    assert(behaviorCode.find("error") != std::string::npos ||
           behaviorCode.find("b == 0") != std::string::npos &&
           "Should identify error condition");

    std::cout << "PASSED\n";
}

// Test 7: NormalBehavior - Success path
void testNormalBehavior() {
    std::cout << "Test 7: NormalBehavior - Success path... ";

    std::string code = R"(
        int addPositive(int a, int b) {
            if (a > 0 && b > 0) {
                return a + b;
            }
            return 0;
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify normal/success behavior
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should detect normal behavior");
    assert(behaviorCode.find("assumes") != std::string::npos &&
           "Should have success path assumptions");

    std::cout << "PASSED\n";
}

// Test 8: MultipleReturnBehaviors - Multiple return points
void testMultipleReturnBehaviors() {
    std::cout << "Test 8: MultipleReturnBehaviors - Multiple return points... ";

    std::string code = R"(
        int findFirst(int arr[], int size, int value) {
            if (arr == nullptr) return -1;
            if (size <= 0) return -1;
            for (int i = 0; i < size; i++) {
                if (arr[i] == value) return i;
            }
            return -1;
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify multiple return behaviors
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should extract behaviors for multiple returns");

    std::cout << "PASSED\n";
}

// Test 9: GuardedPointerBehaviors - Null check patterns
void testGuardedPointerBehaviors() {
    std::cout << "Test 9: GuardedPointerBehaviors - Null check patterns... ";

    std::string code = R"(
        int safeDeref(int *ptr) {
            if (ptr == nullptr) {
                return 0;
            }
            return *ptr;
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify null check behaviors
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should detect null check behaviors");
    assert(behaviorCode.find("null") != std::string::npos ||
           behaviorCode.find("ptr == \\null") != std::string::npos &&
           "Should reference null check");

    std::cout << "PASSED\n";
}

// Test 10: RangeBehaviors - Value range conditions
void testRangeBehaviors() {
    std::cout << "Test 10: RangeBehaviors - Value range conditions... ";

    std::string code = R"(
        int clamp(int value, int min, int max) {
            if (value < min) return min;
            if (value > max) return max;
            return value;
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify range-based behaviors
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should extract range-based behaviors");
    assert(behaviorCode.find("assumes") != std::string::npos &&
           "Should have range assumptions");

    std::cout << "PASSED\n";
}

// Test 11: FlagBehaviors - Boolean flag conditions
void testFlagBehaviors() {
    std::cout << "Test 11: FlagBehaviors - Boolean flag conditions... ";

    std::string code = R"(
        int process(bool flag, int value) {
            if (flag) {
                return value * 2;
            } else {
                return value;
            }
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify flag-based behaviors
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should extract flag-based behaviors");

    std::cout << "PASSED\n";
}

// Test 12: EnumBehaviors - Enum-based dispatch
void testEnumBehaviors() {
    std::cout << "Test 12: EnumBehaviors - Enum-based dispatch... ";

    std::string code = R"(
        enum Color { RED, GREEN, BLUE };
        int getColorValue(Color c) {
            if (c == RED) return 1;
            if (c == GREEN) return 2;
            if (c == BLUE) return 3;
            return 0;
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify enum-based behaviors
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should extract enum-based behaviors");

    std::cout << "PASSED\n";
}

// Test 13: OverlappingBehaviorsWarning - Detect overlap
void testOverlappingBehaviorsWarning() {
    std::cout << "Test 13: OverlappingBehaviorsWarning - Detect overlap... ";

    std::string code = R"(
        int overlapping(int x) {
            if (x > 0) return 1;
            if (x >= 0) return 2;  // Overlaps with x > 0
            return 0;
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    // Check for overlapping behaviors
    bool isDisjoint = annotator.checkDisjointness(func);
    assert(!isDisjoint && "Should detect overlapping behaviors");

    std::cout << "PASSED\n";
}

// Test 14: IncompleteBehaviorsWarning - Detect gaps
void testIncompleteBehaviorsWarning() {
    std::cout << "Test 14: IncompleteBehaviorsWarning - Detect gaps... ";

    std::string code = R"(
        int incomplete(int x) {
            if (x > 0) return 1;
            if (x < -10) return -1;
            // Gap: -10 <= x <= 0 not covered
        }
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    // Check for incomplete behaviors
    bool isComplete = annotator.checkCompleteness(func);
    assert(!isComplete && "Should detect incomplete behaviors");

    std::cout << "PASSED\n";
}

// Test 15: BehaviorInheritance - Virtual function behaviors
void testBehaviorInheritance() {
    std::cout << "Test 15: BehaviorInheritance - Virtual function behaviors... ";

    std::string code = R"(
        class Base {
        public:
            virtual int compute(int x) {
                if (x > 0) return x;
                return 0;
            }
        };
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    FunctionExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.functions.empty() && "No functions found");

    const FunctionDecl* func = extractor.functions[0];
    ACSLBehaviorAnnotator annotator;

    std::string behaviorCode = annotator.generateBehaviors(func);

    // Verify behaviors work with virtual functions
    assert(behaviorCode.find("behavior") != std::string::npos &&
           "Should extract behaviors from virtual functions");

    std::cout << "PASSED\n";
}

// Main test runner
int main() {
    std::cout << "=== Phase 5 (v1.22.0): ACSL Behavior Annotator Tests ===\n\n";

    int passedTests = 0;
    int totalTests = 15;

    try {
        testSimpleBehaviorExtraction();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testSwitchBehaviors();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testCompletenessCheck();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testDisjointnessCheck();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testNestedConditionBehaviors();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testErrorBehavior();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testNormalBehavior();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testMultipleReturnBehaviors();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testGuardedPointerBehaviors();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testRangeBehaviors();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testFlagBehaviors();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testEnumBehaviors();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testOverlappingBehaviorsWarning();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testIncompleteBehaviorsWarning();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    try {
        testBehaviorInheritance();
        passedTests++;
    } catch (...) {
        std::cout << "FAILED\n";
    }

    std::cout << "\n=== Test Summary ===\n";
    std::cout << "Passed: " << passedTests << "/" << totalTests << "\n";
    std::cout << "Status: " << (passedTests == totalTests ? "SUCCESS" : "FAILURE") << "\n";

    return (passedTests == totalTests) ? 0 : 1;
}

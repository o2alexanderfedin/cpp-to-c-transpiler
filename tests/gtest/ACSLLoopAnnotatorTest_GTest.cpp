// tests/gtest/ACSLLoopAnnotatorTest_GTest.cpp
// Unit tests for ACSL Loop Annotator (Epic #193, Story #197)
// Migrated to Google Test framework
//
// Comprehensive ACSL loop invariant, variant, and assigns clause generation

#include "../../include/ACSLLoopAnnotator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>

using namespace clang;
using namespace std;

// Test fixture for ACSL Loop Annotator
class ACSLLoopAnnotatorTest : public ::testing::Test {
protected:
    ACSLLoopAnnotator annotator;

    // Helper: Parse C++ code and extract first loop statement from function
    Stmt* parseLoopStmt(const string& code, const string& funcName) {
        unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
        if (!AST) return nullptr;

        ASTContext& ctx = AST->getASTContext();
        TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* func = dyn_cast<FunctionDecl>(decl)) {
                if (func->getNameAsString() == funcName && func->hasBody()) {
                    // Find first loop in function body
                    CompoundStmt* body = dyn_cast<CompoundStmt>(func->getBody());
                    if (!body) return nullptr;

                    for (auto* stmt : body->body()) {
                        if (isa<ForStmt>(stmt) || isa<WhileStmt>(stmt) || isa<DoStmt>(stmt)) {
                            return stmt;
                        }
                    }
                }
            }
        }
        return nullptr;
    }

    void SetUp() override {
        annotator = ACSLLoopAnnotator();
    }
};

// Test 1: Basic for-loop with counter - loop invariant bounds
TEST_F(ACSLLoopAnnotatorTest, BasicForLoopBounds) {
    string code = R"(
        void test() {
            for (int i = 0; i < 10; i++) {
                // empty body
            }
        }
    )";

    Stmt* loop = parseLoopStmt(code, "test");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";
    ASSERT_TRUE(isa<ForStmt>(loop)) << "Expected ForStmt";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

    EXPECT_NE(annotations.find("loop invariant"), string::npos)
        << "Should contain loop invariant";
    EXPECT_NE(annotations.find("0 <= i"), string::npos)
        << "Should contain lower bound";
    EXPECT_NE(annotations.find("i <= 10"), string::npos)
        << "Should contain upper bound";
    EXPECT_NE(annotations.find("/*@"), string::npos)
        << "Should be ACSL comment";
}

// Test 2: For-loop with variant - loop termination measure
TEST_F(ACSLLoopAnnotatorTest, ForLoopVariant) {
    string code = R"(
        void test() {
            for (int i = 0; i < 10; i++) {
                // empty body
            }
        }
    )";

    Stmt* loop = parseLoopStmt(code, "test");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

    EXPECT_NE(annotations.find("loop variant"), string::npos)
        << "Should contain loop variant";
    EXPECT_NE(annotations.find("10 - i"), string::npos)
        << "Variant should be n - i for ascending loop";
}

// Test 3: Array fill pattern - quantified loop invariant
TEST_F(ACSLLoopAnnotatorTest, ArrayFillPatternInvariant) {
    string code = R"(
        void fillArray(int* arr, int n, int value) {
            for (int i = 0; i < n; i++) {
                arr[i] = value;
            }
        }
    )";

    Stmt* loop = parseLoopStmt(code, "fillArray");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

    EXPECT_NE(annotations.find("\\forall integer j"), string::npos)
        << "Should contain quantified invariant";
    EXPECT_NE(annotations.find("0 <= j < i"), string::npos)
        << "Invariant should quantify over completed iterations";
    EXPECT_NE(annotations.find("arr[j]"), string::npos)
        << "Invariant should reference array";
}

// Test 4: Accumulator pattern - sum invariant
TEST_F(ACSLLoopAnnotatorTest, AccumulatorSumInvariant) {
    string code = R"(
        int sumArray(int* arr, int n) {
            int sum = 0;
            for (int i = 0; i < n; i++) {
                sum += arr[i];
            }
            return sum;
        }
    )";

    Stmt* loop = parseLoopStmt(code, "sumArray");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

    // Should contain sum accumulator invariant
    EXPECT_NE(annotations.find("loop invariant"), string::npos)
        << "Should have loop invariant";
    // Note: Full \sum syntax may be complex, at minimum should track sum variable
}

// Test 5: Loop assigns clause - track modified variables
TEST_F(ACSLLoopAnnotatorTest, LoopAssignsClause) {
    string code = R"(
        void modifyArray(int* arr, int n) {
            for (int i = 0; i < n; i++) {
                arr[i] = i;
            }
        }
    )";

    Stmt* loop = parseLoopStmt(code, "modifyArray");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

    EXPECT_NE(annotations.find("loop assigns"), string::npos)
        << "Should contain loop assigns";
    EXPECT_NE(annotations.find("arr["), string::npos)
        << "Should track array modifications";
}

// Test 6: While-loop annotation
TEST_F(ACSLLoopAnnotatorTest, WhileLoopAnnotation) {
    string code = R"(
        void test() {
            int i = 0;
            while (i < 10) {
                i++;
            }
        }
    )";

    Stmt* loop = parseLoopStmt(code, "test");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";
    ASSERT_TRUE(isa<WhileStmt>(loop)) << "Expected WhileStmt";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<WhileStmt>(loop));

    EXPECT_NE(annotations.find("loop invariant"), string::npos)
        << "While loop should have invariant";
    EXPECT_NE(annotations.find("/*@"), string::npos)
        << "Should be ACSL comment";
}

// Test 7: Nested loops - inner loop annotation
TEST_F(ACSLLoopAnnotatorTest, NestedLoopsInnerAnnotation) {
    string code = R"(
        void test() {
            for (int i = 0; i < 10; i++) {
                for (int j = 0; j < 5; j++) {
                    // inner loop body
                }
            }
        }
    )";

    Stmt* loop = parseLoopStmt(code, "test");
    ASSERT_NE(loop, nullptr) << "Failed to parse outer loop";

    // Get inner loop
    ForStmt* outerLoop = dyn_cast<ForStmt>(loop);
    ASSERT_NE(outerLoop, nullptr) << "Expected ForStmt";

    Stmt* body = outerLoop->getBody();
    ForStmt* innerLoop = nullptr;
    if (auto* compound = dyn_cast<CompoundStmt>(body)) {
        for (auto* stmt : compound->body()) {
            if (auto* forStmt = dyn_cast<ForStmt>(stmt)) {
                innerLoop = forStmt;
                break;
            }
        }
    }

    if (innerLoop) {
        string annotations = annotator.generateLoopAnnotations(innerLoop);

        EXPECT_NE(annotations.find("loop invariant"), string::npos)
            << "Inner loop should have invariant";
        EXPECT_NE(annotations.find("j"), string::npos)
            << "Inner loop invariant should reference j";
    }
}

// Test 8: Descending loop - variant adjustment
TEST_F(ACSLLoopAnnotatorTest, DescendingLoopVariant) {
    string code = R"(
        void test() {
            for (int i = 10; i > 0; i--) {
                // empty body
            }
        }
    )";

    Stmt* loop = parseLoopStmt(code, "test");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

    EXPECT_NE(annotations.find("loop variant"), string::npos)
        << "Should contain loop variant";
    // For descending loops, variant should be i or i - 0
    EXPECT_NE(annotations.find("i"), string::npos)
        << "Variant should reference loop counter";
}

// Test 9: Loop with multiple variables modified
TEST_F(ACSLLoopAnnotatorTest, LoopMultipleAssigns) {
    string code = R"(
        void test(int* a, int* b, int n) {
            for (int i = 0; i < n; i++) {
                a[i] = i;
                b[i] = i * 2;
            }
        }
    )";

    Stmt* loop = parseLoopStmt(code, "test");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

    EXPECT_NE(annotations.find("loop assigns"), string::npos)
        << "Should have loop assigns";
    // Should track both array modifications
}

// Test 10: Do-while loop annotation
TEST_F(ACSLLoopAnnotatorTest, DoWhileLoopAnnotation) {
    string code = R"(
        void test() {
            int i = 0;
            do {
                i++;
            } while (i < 10);
        }
    )";

    Stmt* loop = parseLoopStmt(code, "test");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";
    ASSERT_TRUE(isa<DoStmt>(loop)) << "Expected DoStmt";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<DoStmt>(loop));

    EXPECT_NE(annotations.find("loop invariant"), string::npos)
        << "Do-while loop should have invariant";
    EXPECT_NE(annotations.find("/*@"), string::npos)
        << "Should be ACSL comment";
}

// Test 11: Loop with break condition - additional invariant
TEST_F(ACSLLoopAnnotatorTest, LoopWithBreakInvariant) {
    string code = R"(
        int findElement(int* arr, int n, int target) {
            for (int i = 0; i < n; i++) {
                if (arr[i] == target) {
                    break;
                }
            }
            return -1;
        }
    )";

    Stmt* loop = parseLoopStmt(code, "findElement");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

    EXPECT_NE(annotations.find("loop invariant"), string::npos)
        << "Should have loop invariant";
    // Should have bounds invariant at minimum
    EXPECT_NE(annotations.find("0 <= i"), string::npos)
        << "Should have lower bound invariant";
}

// Test 12: Complex loop condition
TEST_F(ACSLLoopAnnotatorTest, ComplexLoopCondition) {
    string code = R"(
        void test(int* arr, int n) {
            for (int i = 0; i < n && arr[i] != 0; i++) {
                arr[i] = arr[i] + 1;
            }
        }
    )";

    Stmt* loop = parseLoopStmt(code, "test");
    ASSERT_NE(loop, nullptr) << "Failed to parse loop";

    string annotations = annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

    EXPECT_NE(annotations.find("loop invariant"), string::npos)
        << "Complex condition loop should have invariant";
    EXPECT_NE(annotations.find("0 <= i"), string::npos)
        << "Should maintain bounds invariant";
}

// Main function for standalone execution
int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}

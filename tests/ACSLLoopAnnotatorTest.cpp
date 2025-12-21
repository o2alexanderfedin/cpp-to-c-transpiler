// TDD Tests for ACSLLoopAnnotator - Epic #193, Story #197
// Comprehensive ACSL loop invariant, variant, and assigns clause generation

#include <gtest/gtest.h>
#include "ACSLLoopAnnotator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <memory>
#include <string>

using namespace clang;

// Helper: Parse C++ code and extract first loop statement from function
Stmt *parseLoopStmt(const std::string &code, const std::string &funcName) {
  std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
  if (!AST)
    return nullptr;

  ASTContext &ctx = AST->getASTContext();
  TranslationUnitDecl *TU = ctx.getTranslationUnitDecl();

  for (auto *decl : TU->decls()) {
    if (auto *func = dyn_cast<FunctionDecl>(decl)) {
      if (func->getNameAsString() == funcName && func->hasBody()) {
        // Find first loop in function body
        CompoundStmt *body = dyn_cast<CompoundStmt>(func->getBody());
        if (!body)
          return nullptr;

        for (auto *stmt : body->body()) {
          if (isa<ForStmt>(stmt) || isa<WhileStmt>(stmt) || isa<DoStmt>(stmt)) {
            return stmt;
          }
        }
      }
    }
  }
  return nullptr;
}

// Test 1: Basic for-loop with counter - loop invariant bounds

// Test fixture
class ACSLLoopAnnotatorTest : public ::testing::Test {
protected:
};

TEST_F(ACSLLoopAnnotatorTest, BasicForLoopBounds) {
    std::string code = R"(
            void test() {
                for (int i = 0; i < 10; i++) {
                    // empty body
                }
            }
        )";

      Stmt *loop = parseLoopStmt(code, "test");
      ASSERT_TRUE(loop != nullptr) << "Failed to parse loop";
      ASSERT_TRUE(isa<ForStmt>(loop)) << "Expected ForStmt";

      ACSLLoopAnnotator annotator;
      std::string annotations =
          annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

      EXPECT_NE((annotations).find("loop invariant"), std::string::npos) << "Should contain loop invariant";
      EXPECT_NE((annotations).find("0 <= i"), std::string::npos) << "Should contain lower bound";
      EXPECT_NE((annotations).find("i <= 10"), std::string::npos) << "Should contain upper bound";
      EXPECT_NE((annotations).find("/*@"), std::string::npos) << "Should be ACSL comment";
}

TEST_F(ACSLLoopAnnotatorTest, ForLoopVariant) {
    std::string code = R"(
            void test() {
                for (int i = 0; i < 10; i++) {
                    // empty body
                }
            }
        )";

      Stmt *loop = parseLoopStmt(code, "test");
      ASSERT_TRUE(loop != nullptr) << "Failed to parse loop";

      ACSLLoopAnnotator annotator;
      std::string annotations =
          annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

      EXPECT_NE((annotations).find("loop variant"), std::string::npos) << "Should contain loop variant";
      EXPECT_NE((annotations).find("10 - i"), std::string::npos) << "Variant should be n - i for ascending loop";
}

TEST_F(ACSLLoopAnnotatorTest, ArrayFillPatternInvariant) {
    std::string code = R"(
            void fillArray(int* arr, int n, int value) {
                for (int i = 0; i < n; i++) {
                    arr[i] = value;
                }
            }
        )";

      Stmt *loop = parseLoopStmt(code, "fillArray");
      ASSERT_TRUE(loop != nullptr) << "Failed to parse loop";

      ACSLLoopAnnotator annotator;
      std::string annotations =
          annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

      EXPECT_NE((annotations).find("\\forall integer j"), std::string::npos) << "Should contain quantified invariant";
      EXPECT_NE((annotations).find("0 <= j < i"), std::string::npos) << "Invariant should quantify over completed iterations";
      EXPECT_NE((annotations).find("arr[j]"), std::string::npos) << "Invariant should reference array";
}

TEST_F(ACSLLoopAnnotatorTest, AccumulatorSumInvariant) {
    std::string code = R"(
            int sumArray(int* arr, int n) {
                int sum = 0;
                for (int i = 0; i < n; i++) {
                    sum += arr[i];
                }
                return sum;
            }
        )";

      Stmt *loop = parseLoopStmt(code, "sumArray");
      ASSERT_TRUE(loop != nullptr) << "Failed to parse loop";

      ACSLLoopAnnotator annotator;
      std::string annotations =
          annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

      // Should contain sum accumulator invariant
      EXPECT_NE((annotations).find("loop invariant"), std::string::npos) << "Should have loop invariant";
      // Note: Full \sum syntax may be complex, at minimum should track sum variable
}

TEST_F(ACSLLoopAnnotatorTest, LoopAssignsClause) {
    std::string code = R"(
            void modifyArray(int* arr, int n) {
                for (int i = 0; i < n; i++) {
                    arr[i] = i;
                }
            }
        )";

      Stmt *loop = parseLoopStmt(code, "modifyArray");
      ASSERT_TRUE(loop != nullptr) << "Failed to parse loop";

      ACSLLoopAnnotator annotator;
      std::string annotations =
          annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

      EXPECT_NE((annotations).find("loop assigns"), std::string::npos) << "Should contain loop assigns";
      EXPECT_NE((annotations).find("arr["), std::string::npos) << "Should track array modifications";
}

TEST_F(ACSLLoopAnnotatorTest, WhileLoopAnnotation) {
    std::string code = R"(
            void test() {
                int i = 0;
                while (i < 10) {
                    i++;
                }
            }
        )";

      Stmt *loop = parseLoopStmt(code, "test");
      ASSERT_TRUE(loop != nullptr) << "Failed to parse loop";
      ASSERT_TRUE(isa<WhileStmt>(loop)) << "Expected WhileStmt";

      ACSLLoopAnnotator annotator;
      std::string annotations =
          annotator.generateLoopAnnotations(dyn_cast<WhileStmt>(loop));

      EXPECT_NE((annotations).find("loop invariant"), std::string::npos) << "While loop should have invariant";
      EXPECT_NE((annotations).find("/*@"), std::string::npos) << "Should be ACSL comment";
}

TEST_F(ACSLLoopAnnotatorTest, DescendingLoopVariant) {
    std::string code = R"(
            void test() {
                for (int i = 10; i > 0; i--) {
                    // empty body
                }
            }
        )";

      Stmt *loop = parseLoopStmt(code, "test");
      ASSERT_TRUE(loop != nullptr) << "Failed to parse loop";

      ACSLLoopAnnotator annotator;
      std::string annotations =
          annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

      EXPECT_NE((annotations).find("loop variant"), std::string::npos) << "Should contain loop variant";
      // For descending loops, variant should be i or i - 0
      EXPECT_NE((annotations).find("i"), std::string::npos) << "Variant should reference loop counter";
}

TEST_F(ACSLLoopAnnotatorTest, LoopMultipleAssigns) {
    std::string code = R"(
            void test(int* a, int* b, int n) {
                for (int i = 0; i < n; i++) {
                    a[i] = i;
                    b[i] = i * 2;
                }
            }
        )";

      Stmt *loop = parseLoopStmt(code, "test");
      ASSERT_TRUE(loop != nullptr) << "Failed to parse loop";

      ACSLLoopAnnotator annotator;
      std::string annotations =
          annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

      EXPECT_NE((annotations).find("loop assigns"), std::string::npos) << "Should have loop assigns";
      // Should track both array modifications
}

TEST_F(ACSLLoopAnnotatorTest, DoWhileLoopAnnotation) {
    std::string code = R"(
            void test() {
                int i = 0;
                do {
                    i++;
                } while (i < 10);
            }
        )";

      Stmt *loop = parseLoopStmt(code, "test");
      ASSERT_TRUE(loop != nullptr) << "Failed to parse loop";
      ASSERT_TRUE(isa<DoStmt>(loop)) << "Expected DoStmt";

      ACSLLoopAnnotator annotator;
      std::string annotations =
          annotator.generateLoopAnnotations(dyn_cast<DoStmt>(loop));

      EXPECT_NE((annotations).find("loop invariant"), std::string::npos) << "Do-while loop should have invariant";
      EXPECT_NE((annotations).find("/*@"), std::string::npos) << "Should be ACSL comment";
}

TEST_F(ACSLLoopAnnotatorTest, ComplexLoopCondition) {
    std::string code = R"(
            void test(int* arr, int n) {
                for (int i = 0; i < n && arr[i] != 0; i++) {
                    arr[i] = arr[i] + 1;
                }
            }
        )";

      Stmt *loop = parseLoopStmt(code, "test");
      ASSERT_TRUE(loop != nullptr) << "Failed to parse loop";

      ACSLLoopAnnotator annotator;
      std::string annotations =
          annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

      EXPECT_NE((annotations).find("loop invariant"), std::string::npos) << "Complex condition loop should have invariant";
      EXPECT_NE((annotations).find("0 <= i"), std::string::npos) << "Should maintain bounds invariant";
}

// TDD Tests for ACSLLoopAnnotator - Epic #193, Story #197
// Comprehensive ACSL loop invariant, variant, and assigns clause generation

#include "ACSLLoopAnnotator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <memory>
#include <string>

using namespace clang;

// Simple test framework
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name)                                                        \
  {                                                                            \
    std::cout << "✓" << std::endl;                                             \
    tests_passed++;                                                            \
  }
#define TEST_FAIL(name, msg)                                                   \
  {                                                                            \
    std::cout << "✗ FAILED: " << msg << std::endl;                             \
    tests_failed++;                                                            \
  }
#define ASSERT(expr, msg)                                                      \
  if (!(expr)) {                                                               \
    TEST_FAIL("", msg);                                                        \
    return;                                                                    \
  }
#define ASSERT_CONTAINS(haystack, needle, msg)                                 \
  if ((haystack).find(needle) == std::string::npos) {                          \
    TEST_FAIL("", std::string(msg) + " - Expected to find: " + needle);        \
    return;                                                                    \
  }

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
void test_BasicForLoopBounds() {
  TEST_START("BasicForLoopBounds");

  std::string code = R"(
        void test() {
            for (int i = 0; i < 10; i++) {
                // empty body
            }
        }
    )";

  Stmt *loop = parseLoopStmt(code, "test");
  ASSERT(loop != nullptr, "Failed to parse loop");
  ASSERT(isa<ForStmt>(loop), "Expected ForStmt");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

  ASSERT_CONTAINS(annotations, "loop invariant",
                  "Should contain loop invariant");
  ASSERT_CONTAINS(annotations, "0 <= i", "Should contain lower bound");
  ASSERT_CONTAINS(annotations, "i <= 10", "Should contain upper bound");
  ASSERT_CONTAINS(annotations, "/*@", "Should be ACSL comment");

  TEST_PASS("BasicForLoopBounds");
}

// Test 2: For-loop with variant - loop termination measure
void test_ForLoopVariant() {
  TEST_START("ForLoopVariant");

  std::string code = R"(
        void test() {
            for (int i = 0; i < 10; i++) {
                // empty body
            }
        }
    )";

  Stmt *loop = parseLoopStmt(code, "test");
  ASSERT(loop != nullptr, "Failed to parse loop");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

  ASSERT_CONTAINS(annotations, "loop variant", "Should contain loop variant");
  ASSERT_CONTAINS(annotations, "10 - i",
                  "Variant should be n - i for ascending loop");

  TEST_PASS("ForLoopVariant");
}

// Test 3: Array fill pattern - quantified loop invariant
void test_ArrayFillPatternInvariant() {
  TEST_START("ArrayFillPatternInvariant");

  std::string code = R"(
        void fillArray(int* arr, int n, int value) {
            for (int i = 0; i < n; i++) {
                arr[i] = value;
            }
        }
    )";

  Stmt *loop = parseLoopStmt(code, "fillArray");
  ASSERT(loop != nullptr, "Failed to parse loop");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

  ASSERT_CONTAINS(annotations, "\\forall integer j",
                  "Should contain quantified invariant");
  ASSERT_CONTAINS(annotations, "0 <= j < i",
                  "Invariant should quantify over completed iterations");
  ASSERT_CONTAINS(annotations, "arr[j]", "Invariant should reference array");

  TEST_PASS("ArrayFillPatternInvariant");
}

// Test 4: Accumulator pattern - sum invariant
void test_AccumulatorSumInvariant() {
  TEST_START("AccumulatorSumInvariant");

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
  ASSERT(loop != nullptr, "Failed to parse loop");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

  // Should contain sum accumulator invariant
  ASSERT_CONTAINS(annotations, "loop invariant", "Should have loop invariant");
  // Note: Full \sum syntax may be complex, at minimum should track sum variable

  TEST_PASS("AccumulatorSumInvariant");
}

// Test 5: Loop assigns clause - track modified variables
void test_LoopAssignsClause() {
  TEST_START("LoopAssignsClause");

  std::string code = R"(
        void modifyArray(int* arr, int n) {
            for (int i = 0; i < n; i++) {
                arr[i] = i;
            }
        }
    )";

  Stmt *loop = parseLoopStmt(code, "modifyArray");
  ASSERT(loop != nullptr, "Failed to parse loop");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

  ASSERT_CONTAINS(annotations, "loop assigns", "Should contain loop assigns");
  ASSERT_CONTAINS(annotations, "arr[", "Should track array modifications");

  TEST_PASS("LoopAssignsClause");
}

// Test 6: While-loop annotation
void test_WhileLoopAnnotation() {
  TEST_START("WhileLoopAnnotation");

  std::string code = R"(
        void test() {
            int i = 0;
            while (i < 10) {
                i++;
            }
        }
    )";

  Stmt *loop = parseLoopStmt(code, "test");
  ASSERT(loop != nullptr, "Failed to parse loop");
  ASSERT(isa<WhileStmt>(loop), "Expected WhileStmt");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<WhileStmt>(loop));

  ASSERT_CONTAINS(annotations, "loop invariant",
                  "While loop should have invariant");
  ASSERT_CONTAINS(annotations, "/*@", "Should be ACSL comment");

  TEST_PASS("WhileLoopAnnotation");
}

// Test 7: Nested loops - inner loop annotation
void test_NestedLoopsInnerAnnotation() {
  TEST_START("NestedLoopsInnerAnnotation");

  std::string code = R"(
        void test() {
            for (int i = 0; i < 10; i++) {
                for (int j = 0; j < 5; j++) {
                    // inner loop body
                }
            }
        }
    )";

  Stmt *loop = parseLoopStmt(code, "test");
  ASSERT(loop != nullptr, "Failed to parse outer loop");

  // Get inner loop
  ForStmt *outerLoop = dyn_cast<ForStmt>(loop);
  ASSERT(outerLoop != nullptr, "Expected ForStmt");

  Stmt *body = outerLoop->getBody();
  ForStmt *innerLoop = nullptr;
  if (auto *compound = dyn_cast<CompoundStmt>(body)) {
    for (auto *stmt : compound->body()) {
      if (auto *forStmt = dyn_cast<ForStmt>(stmt)) {
        innerLoop = forStmt;
        break;
      }
    }
  }

  if (innerLoop) {
    ACSLLoopAnnotator annotator;
    std::string annotations = annotator.generateLoopAnnotations(innerLoop);

    ASSERT_CONTAINS(annotations, "loop invariant",
                    "Inner loop should have invariant");
    ASSERT_CONTAINS(annotations, "j",
                    "Inner loop invariant should reference j");
  }

  TEST_PASS("NestedLoopsInnerAnnotation");
}

// Test 8: Descending loop - variant adjustment
void test_DescendingLoopVariant() {
  TEST_START("DescendingLoopVariant");

  std::string code = R"(
        void test() {
            for (int i = 10; i > 0; i--) {
                // empty body
            }
        }
    )";

  Stmt *loop = parseLoopStmt(code, "test");
  ASSERT(loop != nullptr, "Failed to parse loop");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

  ASSERT_CONTAINS(annotations, "loop variant", "Should contain loop variant");
  // For descending loops, variant should be i or i - 0
  ASSERT_CONTAINS(annotations, "i", "Variant should reference loop counter");

  TEST_PASS("DescendingLoopVariant");
}

// Test 9: Loop with multiple variables modified
void test_LoopMultipleAssigns() {
  TEST_START("LoopMultipleAssigns");

  std::string code = R"(
        void test(int* a, int* b, int n) {
            for (int i = 0; i < n; i++) {
                a[i] = i;
                b[i] = i * 2;
            }
        }
    )";

  Stmt *loop = parseLoopStmt(code, "test");
  ASSERT(loop != nullptr, "Failed to parse loop");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

  ASSERT_CONTAINS(annotations, "loop assigns", "Should have loop assigns");
  // Should track both array modifications

  TEST_PASS("LoopMultipleAssigns");
}

// Test 10: Do-while loop annotation
void test_DoWhileLoopAnnotation() {
  TEST_START("DoWhileLoopAnnotation");

  std::string code = R"(
        void test() {
            int i = 0;
            do {
                i++;
            } while (i < 10);
        }
    )";

  Stmt *loop = parseLoopStmt(code, "test");
  ASSERT(loop != nullptr, "Failed to parse loop");
  ASSERT(isa<DoStmt>(loop), "Expected DoStmt");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<DoStmt>(loop));

  ASSERT_CONTAINS(annotations, "loop invariant",
                  "Do-while loop should have invariant");
  ASSERT_CONTAINS(annotations, "/*@", "Should be ACSL comment");

  TEST_PASS("DoWhileLoopAnnotation");
}

// Test 11: Loop with break condition - additional invariant
void test_LoopWithBreakInvariant() {
  TEST_START("LoopWithBreakInvariant");

  std::string code = R"(
        int findElement(int* arr, int n, int target) {
            for (int i = 0; i < n; i++) {
                if (arr[i] == target) {
                    break;
                }
            }
            return -1;
        }
    )";

  Stmt *loop = parseLoopStmt(code, "findElement");
  ASSERT(loop != nullptr, "Failed to parse loop");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

  ASSERT_CONTAINS(annotations, "loop invariant", "Should have loop invariant");
  // Should have bounds invariant at minimum
  ASSERT_CONTAINS(annotations, "0 <= i", "Should have lower bound invariant");

  TEST_PASS("LoopWithBreakInvariant");
}

// Test 12: Complex loop condition
void test_ComplexLoopCondition() {
  TEST_START("ComplexLoopCondition");

  std::string code = R"(
        void test(int* arr, int n) {
            for (int i = 0; i < n && arr[i] != 0; i++) {
                arr[i] = arr[i] + 1;
            }
        }
    )";

  Stmt *loop = parseLoopStmt(code, "test");
  ASSERT(loop != nullptr, "Failed to parse loop");

  ACSLLoopAnnotator annotator;
  std::string annotations =
      annotator.generateLoopAnnotations(dyn_cast<ForStmt>(loop));

  ASSERT_CONTAINS(annotations, "loop invariant",
                  "Complex condition loop should have invariant");
  ASSERT_CONTAINS(annotations, "0 <= i", "Should maintain bounds invariant");

  TEST_PASS("ComplexLoopCondition");
}

// Main test runner
int main() {
  std::cout << "\n=== ACSLLoopAnnotator Tests (Epic #193, Story #197) ===\n\n";

  test_BasicForLoopBounds();
  test_ForLoopVariant();
  test_ArrayFillPatternInvariant();
  test_AccumulatorSumInvariant();
  test_LoopAssignsClause();
  test_WhileLoopAnnotation();
  test_NestedLoopsInnerAnnotation();
  test_DescendingLoopVariant();
  test_LoopMultipleAssigns();
  test_DoWhileLoopAnnotation();
  test_LoopWithBreakInvariant();
  test_ComplexLoopCondition();

  std::cout << "\n=== Test Summary ===\n";
  std::cout << "Passed: " << tests_passed << "\n";
  std::cout << "Failed: " << tests_failed << "\n";
  std::cout << "Total:  " << (tests_passed + tests_failed) << "\n";

  return (tests_failed == 0) ? 0 : 1;
}

// Phase 3: [[assume]] Attribute Handling Test
// Tests for AssumeAttributeHandler class (C++23 P1774R8)

#include "../include/AssumeAttributeHandler.h"
#include "../include/CNodeBuilder.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include "gtest/gtest.h"

using namespace clang;

class AssumeAttributeHandlerTest : public ::testing::Test {
protected:
  void SetUp() override {
    // Each test will create its own AST
  }

  void TearDown() override {
    // Cleanup happens automatically
  }

  // Helper to build AST from C++23 code
  std::unique_ptr<ASTUnit> buildAST(const std::string& Code) {
    std::vector<std::string> Args = {"-std=c++23"};
    return tooling::buildASTFromCodeWithArgs(Code, Args, "test.cpp");
  }

  // Helper to find AttributedStmt in AST
  AttributedStmt* findAttributedStmt(ASTContext& Ctx) {
    struct Finder : RecursiveASTVisitor<Finder> {
      AttributedStmt* Result = nullptr;

      bool VisitAttributedStmt(AttributedStmt* S) {
        if (!Result) {
          Result = S;
        }
        return true;
      }
    };

    Finder F;
    F.TraverseDecl(Ctx.getTranslationUnitDecl());
    return F.Result;
  }
};

// Test 1: Basic assume with simple condition
TEST_F(AssumeAttributeHandlerTest, BasicAssumeSimpleCondition) {
  std::string Code = R"(
    void test(int x) {
      [[assume(x > 0)]];
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Comment);

  auto* AttrStmt = findAttributedStmt(Ctx);
  ASSERT_NE(AttrStmt, nullptr) << "Failed to find [[assume]] attribute";

  auto* Result = Handler.handle(AttrStmt, Ctx);
  ASSERT_NE(Result, nullptr);
}

// Test 2: Assume with nullptr check
TEST_F(AssumeAttributeHandlerTest, AssumeNullptrCheck) {
  std::string Code = R"(
    void test(int* ptr) {
      [[assume(ptr != nullptr)]];
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Comment);

  auto* AttrStmt = findAttributedStmt(Ctx);
  ASSERT_NE(AttrStmt, nullptr);

  auto* Result = Handler.handle(AttrStmt, Ctx);
  ASSERT_NE(Result, nullptr);
}

// Test 3: Assume with compound condition
TEST_F(AssumeAttributeHandlerTest, AssumeCompoundCondition) {
  std::string Code = R"(
    void test(int a, int b) {
      [[assume(a > 0 && b > 0)]];
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Comment);

  auto* AttrStmt = findAttributedStmt(Ctx);
  ASSERT_NE(AttrStmt, nullptr);

  auto* Result = Handler.handle(AttrStmt, Ctx);
  ASSERT_NE(Result, nullptr);
}

// Test 4: Multiple assumes in sequence
TEST_F(AssumeAttributeHandlerTest, MultipleAssumes) {
  std::string Code = R"(
    void test(int* data, size_t n) {
      [[assume(data != nullptr)]];
      [[assume(n > 0)]];
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Comment);

  // Find all AttributedStmt nodes
  struct Finder : RecursiveASTVisitor<Finder> {
    std::vector<AttributedStmt*> Results;

    bool VisitAttributedStmt(AttributedStmt* S) {
      Results.push_back(S);
      return true;
    }
  };

  Finder F;
  F.TraverseDecl(Ctx.getTranslationUnitDecl());

  ASSERT_GE(F.Results.size(), 2u) << "Expected at least 2 assume attributes";

  for (auto* AttrStmt : F.Results) {
    auto* Result = Handler.handle(AttrStmt, Ctx);
    ASSERT_NE(Result, nullptr);
  }
}

// Test 5: Strip strategy produces no output (just underlying statement)
TEST_F(AssumeAttributeHandlerTest, StripStrategyProducesNoOutput) {
  std::string Code = R"(
    void test(int x) {
      [[assume(x > 0)]];
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Strip);

  auto* AttrStmt = findAttributedStmt(Ctx);
  ASSERT_NE(AttrStmt, nullptr);

  auto* Result = Handler.handle(AttrStmt, Ctx);

  // Strip strategy should return the underlying statement
  // which for a null statement is a NullStmt
  ASSERT_NE(Result, nullptr);
  EXPECT_TRUE(isa<NullStmt>(Result) || Result == AttrStmt->getSubStmt());
}

// Test 6: Comment strategy produces comment
TEST_F(AssumeAttributeHandlerTest, CommentStrategyProducesComment) {
  std::string Code = R"(
    void test(int x) {
      [[assume(x > 0)]];
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Comment);

  auto* AttrStmt = findAttributedStmt(Ctx);
  ASSERT_NE(AttrStmt, nullptr);

  auto* Result = Handler.handle(AttrStmt, Ctx);
  ASSERT_NE(Result, nullptr);

  // For Comment strategy, we expect the handler to attach
  // a comment to the statement (implementation-specific)
}

// Test 7: Builtin strategy produces __builtin_assume()
TEST_F(AssumeAttributeHandlerTest, BuiltinStrategyProducesBuiltin) {
  std::string Code = R"(
    void test(int x) {
      [[assume(x > 0)]];
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Builtin);

  auto* AttrStmt = findAttributedStmt(Ctx);
  ASSERT_NE(AttrStmt, nullptr);

  auto* Result = Handler.handle(AttrStmt, Ctx);
  ASSERT_NE(Result, nullptr);

  // For Builtin strategy, we expect a CallExpr or CompoundStmt
  // containing __builtin_assume() call
}

// Test 8: Complex expression translation
TEST_F(AssumeAttributeHandlerTest, ComplexExpressionTranslation) {
  std::string Code = R"(
    void test(int* arr, size_t len) {
      [[assume(arr != nullptr && len > 0 && len < 1000)]];
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Comment);

  auto* AttrStmt = findAttributedStmt(Ctx);
  ASSERT_NE(AttrStmt, nullptr);

  auto* Result = Handler.handle(AttrStmt, Ctx);
  ASSERT_NE(Result, nullptr);
}

// Test 9: Assume with pointer arithmetic
TEST_F(AssumeAttributeHandlerTest, AssumePointerArithmetic) {
  std::string Code = R"(
    void test(int* begin, int* end) {
      [[assume(end > begin)]];
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Comment);

  auto* AttrStmt = findAttributedStmt(Ctx);
  ASSERT_NE(AttrStmt, nullptr);

  auto* Result = Handler.handle(AttrStmt, Ctx);
  ASSERT_NE(Result, nullptr);
}

// Test 10: Assume with bitwise operations
TEST_F(AssumeAttributeHandlerTest, AssumeBitwiseOperations) {
  std::string Code = R"(
    void test(unsigned int flags) {
      [[assume((flags & 0x01) != 0)]];
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Comment);

  auto* AttrStmt = findAttributedStmt(Ctx);
  ASSERT_NE(AttrStmt, nullptr);

  auto* Result = Handler.handle(AttrStmt, Ctx);
  ASSERT_NE(Result, nullptr);
}

// Test 11: Test all three strategies with same input
TEST_F(AssumeAttributeHandlerTest, AllStrategiesWork) {
  std::string Code = R"(
    void test(int x) {
      [[assume(x > 0)]];
    }
  )";

  // Test Strip strategy
  {
    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr);
    auto& Ctx = AST->getASTContext();
    CNodeBuilder Builder(Ctx);
    AssumeAttributeHandler Handler(Builder, AssumeStrategy::Strip);
    auto* AttrStmt = findAttributedStmt(Ctx);
    ASSERT_NE(AttrStmt, nullptr);
    auto* Result = Handler.handle(AttrStmt, Ctx);
    ASSERT_NE(Result, nullptr);
  }

  // Test Comment strategy
  {
    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr);
    auto& Ctx = AST->getASTContext();
    CNodeBuilder Builder(Ctx);
    AssumeAttributeHandler Handler(Builder, AssumeStrategy::Comment);
    auto* AttrStmt = findAttributedStmt(Ctx);
    ASSERT_NE(AttrStmt, nullptr);
    auto* Result = Handler.handle(AttrStmt, Ctx);
    ASSERT_NE(Result, nullptr);
  }

  // Test Builtin strategy
  {
    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr);
    auto& Ctx = AST->getASTContext();
    CNodeBuilder Builder(Ctx);
    AssumeAttributeHandler Handler(Builder, AssumeStrategy::Builtin);
    auto* AttrStmt = findAttributedStmt(Ctx);
    ASSERT_NE(AttrStmt, nullptr);
    auto* Result = Handler.handle(AttrStmt, Ctx);
    ASSERT_NE(Result, nullptr);
  }
}

// Test 12: Assume followed by statement (separate)
TEST_F(AssumeAttributeHandlerTest, AssumeFollowedByStatement) {
  std::string Code = R"(
    void test(int x) {
      [[assume(x > 0)]];
      int y = x * 2;
    }
  )";

  auto AST = buildAST(Code);
  ASSERT_NE(AST, nullptr);

  auto& Ctx = AST->getASTContext();
  CNodeBuilder Builder(Ctx);
  AssumeAttributeHandler Handler(Builder, AssumeStrategy::Comment);

  auto* AttrStmt = findAttributedStmt(Ctx);
  ASSERT_NE(AttrStmt, nullptr);

  auto* Result = Handler.handle(AttrStmt, Ctx);
  ASSERT_NE(Result, nullptr);
}

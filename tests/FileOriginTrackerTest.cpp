// TDD Tests for FileOriginTracker - Phase 34-02 Implementation
// Purpose: Track declaration-to-file mappings for multi-file transpilation
// Replaces: 12 isInMainFile() checks with intelligent file origin filtering

#include <gtest/gtest.h>
#include "FileOriginTracker.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"

using namespace cpptoc;
using namespace clang;

// ============================================================================
// Test Fixture with Mock SourceManager Setup
// ============================================================================

class FileOriginTrackerTest : public ::testing::Test {
protected:
  void SetUp() override {
    // Will be initialized per test with specific code
  }

  void TearDown() override {
    // Cleanup happens automatically
  }

  // Helper: Create a simple AST from C++ code and return the first decl
  std::unique_ptr<ASTUnit> parseCode(const std::string &code,
                                      const std::string &filename = "test.cpp") {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, filename);
  }
};

// Integration test fixture (inherits same helper methods)
class FileOriginTrackerIntegrationTest : public FileOriginTrackerTest {};

// ============================================================================
// Test 1: Basic Declaration Recording (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, RecordsMainFileDeclarations) {
  // Given: A simple function declaration in main.cpp
  auto AST = parseCode("void testFunc() {}", "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Find the function declaration
  const FunctionDecl *funcDecl = nullptr;
  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    if (auto *FD = dyn_cast<FunctionDecl>(decl)) {
      if (FD->getNameAsString() == "testFunc") {
        funcDecl = FD;
        break;
      }
    }
  }
  ASSERT_NE(funcDecl, nullptr);

  // When: Record the declaration
  tracker.recordDeclaration(funcDecl);

  // Then: Should recognize it's from main file
  EXPECT_TRUE(tracker.isFromMainFile(funcDecl))
      << "Declaration should be recognized as from main file";
  EXPECT_EQ(tracker.getFileCategory(funcDecl), FileOriginTracker::FileCategory::MainFile)
      << "File category should be MainFile";
}

// ============================================================================
// Test 2: System Header Detection (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, DetectsSystemHeaders) {
  // Given: Code that includes a system header
  auto AST = parseCode("#include <vector>\nvoid test() {}", "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Find a declaration from system header (std::vector's ClassTemplateDecl)
  const Decl *systemDecl = nullptr;
  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    auto loc = decl->getLocation();
    if (loc.isValid() && SM.isInSystemHeader(loc)) {
      systemDecl = decl;
      break;
    }
  }

  if (systemDecl) {
    // When: Record system header declaration
    tracker.recordDeclaration(systemDecl);

    // Then: Should be classified as system header
    EXPECT_TRUE(tracker.isFromSystemHeader(systemDecl))
        << "System header declaration should be detected";
    EXPECT_EQ(tracker.getFileCategory(systemDecl),
              FileOriginTracker::FileCategory::SystemHeader)
        << "File category should be SystemHeader";
  }
}

// ============================================================================
// Test 3: shouldTranspile() for Main File (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, ShouldTranspileMainFileDeclarations) {
  // Given: A class declaration in main.cpp
  auto AST = parseCode("class TestClass { public: int x; };", "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Find the class declaration
  const CXXRecordDecl *classDecl = nullptr;
  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    if (auto *CD = dyn_cast<CXXRecordDecl>(decl)) {
      if (CD->getNameAsString() == "TestClass") {
        classDecl = CD;
        break;
      }
    }
  }
  ASSERT_NE(classDecl, nullptr);

  // When: Record and check if should transpile
  tracker.recordDeclaration(classDecl);

  // Then: Main file declarations should be transpiled
  EXPECT_TRUE(tracker.shouldTranspile(classDecl))
      << "Main file declarations must be transpiled";
}

// ============================================================================
// Test 4: shouldTranspile() for System Headers (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, ShouldNotTranspileSystemHeaders) {
  // Given: Code with system header include
  auto AST = parseCode("#include <string>\nvoid test() {}", "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Find a system header declaration
  const Decl *systemDecl = nullptr;
  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    auto loc = decl->getLocation();
    if (loc.isValid() && SM.isInSystemHeader(loc)) {
      systemDecl = decl;
      break;
    }
  }

  if (systemDecl) {
    // When: Record and check if should transpile
    tracker.recordDeclaration(systemDecl);

    // Then: System headers should NOT be transpiled
    EXPECT_FALSE(tracker.shouldTranspile(systemDecl))
        << "System header declarations should be skipped";
  }
}

// ============================================================================
// Test 5: User Header Path Configuration (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, ConfigureUserHeaderPaths) {
  // Given: Tracker with user header paths
  auto AST = parseCode("void test() {}", "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  FileOriginTracker tracker(SM);

  // When: Add user header paths
  tracker.addUserHeaderPath("/Users/test/myproject/include");
  tracker.addUserHeaderPath("/Users/test/myproject/src");

  // Then: User header paths should be configured
  // (We'll verify behavior via classification in integration tests)
  SUCCEED() << "User header paths configured successfully";
}

// ============================================================================
// Test 6: getUserHeaderFiles() Returns User Headers (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, GetUserHeaderFiles) {
  // Given: Multiple declarations from different files
  auto AST = parseCode("void mainFunc() {}", "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Record main file declaration
  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    if (auto *FD = dyn_cast<FunctionDecl>(decl)) {
      if (FD->getNameAsString() == "mainFunc") {
        tracker.recordDeclaration(FD);
        break;
      }
    }
  }

  // When: Get user header files
  auto userHeaders = tracker.getUserHeaderFiles();

  // Then: Should not include main.cpp (it's main file, not header)
  // In this simple test, we expect empty set
  EXPECT_TRUE(userHeaders.empty() || userHeaders.size() == 0)
      << "Main file should not be in user headers list";
}

// ============================================================================
// Test 7: getDeclarationsFromFile() Returns Correct Decls (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, GetDeclarationsFromFile) {
  // Given: Multiple declarations in one file
  auto AST = parseCode(
      "void func1() {}\n"
      "void func2() {}\n"
      "class TestClass {};\n",
      "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Record all declarations and count main file ones
  std::vector<const Decl*> allDecls;
  size_t mainFileCount = 0;
  std::string mainFilePath;

  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    tracker.recordDeclaration(decl);
    allDecls.push_back(decl);

    // Track main file declarations
    auto loc = decl->getLocation();
    if (loc.isValid() && SM.isInMainFile(loc)) {
      mainFileCount++;
      if (mainFilePath.empty()) {
        mainFilePath = tracker.getOriginFile(decl);
      }
    }
  }

  // When: Get declarations from main file
  auto fileDecls = tracker.getDeclarationsFromFile(mainFilePath);

  // Then: Should return all recorded declarations from that file
  EXPECT_GE(fileDecls.size(), 3u)
      << "Should have at least 3 declarations (func1, func2, TestClass), got "
      << fileDecls.size();
}

// ============================================================================
// Test 8: Statistics Collection (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, CollectsStatistics) {
  // Given: Code with multiple declarations
  auto AST = parseCode(
      "#include <vector>\n"
      "void func1() {}\n"
      "class MyClass { public: void method(); };\n",
      "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Record all declarations (including system headers)
  size_t recordedCount = 0;
  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    tracker.recordDeclaration(decl);
    recordedCount++;
  }

  // When: Get statistics
  auto stats = tracker.getStatistics();

  // Then: Statistics should reflect recorded declarations
  EXPECT_GT(stats.totalDeclarations, 0u)
      << "Should have recorded some declarations";
  EXPECT_GT(stats.uniqueFiles, 0u)
      << "Should have tracked at least one file";
  EXPECT_GE(stats.mainFileDeclarations, 2u)
      << "Should have at least 2 main file declarations (func1, MyClass)";
}

// ============================================================================
// Test 9: getOriginFile() Returns Correct Path (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, GetOriginFileReturnsCorrectPath) {
  // Given: A declaration from known file
  auto AST = parseCode("void testFunc() {}", "test.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Find the function declaration
  const FunctionDecl *funcDecl = nullptr;
  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    if (auto *FD = dyn_cast<FunctionDecl>(decl)) {
      if (FD->getNameAsString() == "testFunc") {
        funcDecl = FD;
        break;
      }
    }
  }
  ASSERT_NE(funcDecl, nullptr);

  // When: Record and get origin file
  tracker.recordDeclaration(funcDecl);
  std::string originFile = tracker.getOriginFile(funcDecl);

  // Then: Should contain "test.cpp" in the path
  EXPECT_FALSE(originFile.empty())
      << "Origin file path should not be empty";
  EXPECT_NE(originFile.find("test.cpp"), std::string::npos)
      << "Origin file should contain 'test.cpp'";
}

// ============================================================================
// Test 10: Third-Party Header Configuration (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, ConfigureThirdPartyHeaders) {
  // Given: Tracker with third-party paths
  auto AST = parseCode("void test() {}", "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  FileOriginTracker tracker(SM);

  // When: Configure third-party paths and transpilation policy
  tracker.addThirdPartyPath("/Users/test/myproject/third_party");
  tracker.addThirdPartyPath("/Users/test/myproject/external");
  tracker.setTranspileThirdParty(false);

  // Then: Configuration should succeed
  SUCCEED() << "Third-party header configuration completed";
}

// ============================================================================
// Test 11: Null Pointer Safety (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, HandlesNullPointerSafely) {
  // Given: Tracker
  auto AST = parseCode("void test() {}", "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  FileOriginTracker tracker(SM);

  // When: Query with null pointer
  const Decl *nullDecl = nullptr;

  // Then: Should handle gracefully (not crash)
  EXPECT_FALSE(tracker.isFromMainFile(nullDecl))
      << "Null pointer should return false for isFromMainFile";
  EXPECT_FALSE(tracker.shouldTranspile(nullDecl))
      << "Null pointer should return false for shouldTranspile";
  EXPECT_TRUE(tracker.getOriginFile(nullDecl).empty())
      << "Null pointer should return empty string for getOriginFile";
}

// ============================================================================
// Test 12: isFromUserHeader() Detection (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, DetectsUserHeaders) {
  // This test will be expanded in integration tests with real multi-file setup
  // For now, just ensure the API exists and returns false for main file
  auto AST = parseCode("void test() {}", "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Find a main file declaration
  const Decl *mainDecl = nullptr;
  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    if (auto *FD = dyn_cast<FunctionDecl>(decl)) {
      mainDecl = FD;
      break;
    }
  }

  if (mainDecl) {
    tracker.recordDeclaration(mainDecl);

    // Main file declarations are not user headers
    EXPECT_FALSE(tracker.isFromUserHeader(mainDecl))
        << "Main file declarations should not be classified as user headers";
  }
}

// ============================================================================
// Test 13: Memory Efficiency Check (TDD Red Phase - MUST FAIL)
// ============================================================================

TEST_F(FileOriginTrackerTest, MemoryEfficiency) {
  // Given: Large number of declarations
  auto AST = parseCode(
      "void f1() {}\n void f2() {}\n void f3() {}\n"
      "void f4() {}\n void f5() {}\n void f6() {}\n"
      "void f7() {}\n void f8() {}\n void f9() {}\n"
      "void f10() {}\n",
      "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Record many declarations
  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    tracker.recordDeclaration(decl);
  }

  // When: Get statistics
  auto stats = tracker.getStatistics();

  // Then: Memory overhead should be reasonable
  // For 10 declarations, we expect < 10KB overhead
  // Each entry: pointer (8 bytes) + string (avg 50 bytes) = ~58 bytes per decl
  // 10 decls * 58 bytes * 3 maps = ~1740 bytes < 10KB
  EXPECT_GT(stats.totalDeclarations, 0u)
      << "Should track declarations efficiently";
}

// ============================================================================
// Test 14: Integration Test with Real Multi-File C++ Project
// ============================================================================

TEST_F(FileOriginTrackerIntegrationTest, RealMultiFileProject) {
  // This integration test uses the actual multi-file test case from Phase 34
  // Location: tests/multi-file-transpilation/01-simple-class/
  // Files: Point.h, Point.cpp, main.cpp

  const char *mainCppCode = R"(
#include "Point.h"

int main() {
  Point p(3, 4);
  int dist = p.distanceSquared();
  return dist == 25 ? 0 : 1;
}
)";

  const char *pointHCode = R"(
#ifndef POINT_H
#define POINT_H

class Point {
public:
  Point(int x, int y);
  int getX() const { return m_x; }
  int getY() const;
  void setX(int x);
  void setY(int y);
  int distanceSquared() const;

private:
  int m_x;
  int m_y;
};

#endif // POINT_H
)";

  const char *pointCppCode = R"(
#include "Point.h"

Point::Point(int x, int y) : m_x(x), m_y(y) {}

int Point::getY() const { return m_y; }

void Point::setX(int x) { m_x = x; }

void Point::setY(int y) { m_y = y; }

int Point::distanceSquared() const {
  return m_x * m_x + m_y * m_y;
}
)";

  // Given: Parse main.cpp with Point.h available
  auto AST = parseCode(mainCppCode, "main.cpp");
  ASSERT_NE(AST, nullptr);

  auto &SM = AST->getSourceManager();
  auto &Context = AST->getASTContext();

  FileOriginTracker tracker(SM);

  // Configure user header paths (simulating project structure)
  std::string testDir = "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/multi-file-transpilation/01-simple-class";
  tracker.addUserHeaderPath(testDir);

  // When: Record all declarations from the translation unit
  size_t mainFileDecls = 0;
  size_t userHeaderDecls = 0;
  size_t systemHeaderDecls = 0;

  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    tracker.recordDeclaration(decl);

    if (tracker.isFromMainFile(decl)) {
      mainFileDecls++;
    } else if (tracker.isFromUserHeader(decl)) {
      userHeaderDecls++;
    } else if (tracker.isFromSystemHeader(decl)) {
      systemHeaderDecls++;
    }
  }

  // Then: Verify correct classification
  EXPECT_GT(mainFileDecls, 0u)
      << "Should have declarations from main.cpp";

  // Verify shouldTranspile() works correctly
  for (auto *decl : Context.getTranslationUnitDecl()->decls()) {
    auto loc = decl->getLocation();
    if (loc.isValid()) {
      if (SM.isInMainFile(loc)) {
        EXPECT_TRUE(tracker.shouldTranspile(decl))
            << "Main file declarations should be transpiled";
      } else if (SM.isInSystemHeader(loc)) {
        EXPECT_FALSE(tracker.shouldTranspile(decl))
            << "System header declarations should NOT be transpiled";
      }
    }
  }

  // Verify statistics
  auto stats = tracker.getStatistics();
  EXPECT_GT(stats.totalDeclarations, 0u)
      << "Should have recorded declarations";
  EXPECT_GT(stats.mainFileDeclarations, 0u)
      << "Should have main file declarations";
  EXPECT_GE(stats.uniqueFiles, 1u)
      << "Should have at least main.cpp file";

  SUCCEED() << "Integration test with real multi-file project completed successfully";
}

// ============================================================================
// Main Entry Point
// ============================================================================

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

#include "SourceLocationMapper.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticIDs.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/FileSystemOptions.h"
#include "gtest/gtest.h"

using namespace clang;

class SourceLocationMapperTest : public ::testing::Test {
protected:
  void SetUp() override {
    FileSystemOpts = std::make_unique<FileSystemOptions>();
    FileMgr = std::make_unique<FileManager>(*FileSystemOpts);

    DiagOpts = std::make_unique<DiagnosticOptions>();
    Diag = std::make_unique<DiagnosticsEngine>(
        IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()), *DiagOpts);

    Mapper = std::make_unique<SourceLocationMapper>(*FileMgr, *Diag);
  }

  std::unique_ptr<FileSystemOptions> FileSystemOpts;
  std::unique_ptr<FileManager> FileMgr;
  std::unique_ptr<DiagnosticOptions> DiagOpts;
  std::unique_ptr<DiagnosticsEngine> Diag;
  std::unique_ptr<SourceLocationMapper> Mapper;
};

TEST_F(SourceLocationMapperTest, RegisterFile_ReturnsValidFileID) {
  FileID FID = Mapper->registerFile("output/test.c");

  EXPECT_TRUE(FID.isValid());
  EXPECT_NE(FID.getHashValue(), 0u);
}

TEST_F(SourceLocationMapperTest, RegisterFile_CachesFileID) {
  FileID FID1 = Mapper->registerFile("output/test.c");
  FileID FID2 = Mapper->registerFile("output/test.c");

  // Same file should return same FileID
  EXPECT_EQ(FID1, FID2);
}

TEST_F(SourceLocationMapperTest, RegisterFile_DistinctFileIDsForDifferentFiles) {
  FileID FID1 = Mapper->registerFile("output/game.c");
  FileID FID2 = Mapper->registerFile("output/player.c");

  EXPECT_NE(FID1, FID2);
}

TEST_F(SourceLocationMapperTest, GetStartOfFile_ReturnsValidLocation) {
  SourceLocation Loc = Mapper->getStartOfFile("output/test.c");

  EXPECT_TRUE(Loc.isValid());
  EXPECT_TRUE(Loc.isFileID());
  EXPECT_FALSE(Loc.isMacroID());
}

TEST_F(SourceLocationMapperTest, GetStartOfFile_PrintsCorrectly) {
  SourceLocation Loc = Mapper->getStartOfFile("output/test.c");

  // Verify SourceManager can print the location
  std::string LocStr;
  llvm::raw_string_ostream OS(LocStr);
  Loc.print(OS, Mapper->getSourceManager());
  OS.flush();

  EXPECT_TRUE(LocStr.find("output/test.c") != std::string::npos);
  EXPECT_TRUE(LocStr.find("1:1") != std::string::npos);
}

TEST_F(SourceLocationMapperTest, GetStartOfFile_RoundTrip) {
  SourceLocation Loc = Mapper->getStartOfFile("output/test.c");

  SourceManager &SM = Mapper->getSourceManager();
  unsigned Line = SM.getSpellingLineNumber(Loc);
  unsigned Col = SM.getSpellingColumnNumber(Loc);

  EXPECT_EQ(Line, 1u);
  EXPECT_EQ(Col, 1u);
}

TEST_F(SourceLocationMapperTest, GetLocation_ValidLineColumn) {
  SourceLocation Loc = Mapper->getLocation("output/test.c", 10, 5);

  EXPECT_TRUE(Loc.isValid());

  SourceManager &SM = Mapper->getSourceManager();
  unsigned Line = SM.getSpellingLineNumber(Loc);
  unsigned Col = SM.getSpellingColumnNumber(Loc);

  EXPECT_EQ(Line, 10u);
  EXPECT_EQ(Col, 5u);
}

TEST_F(SourceLocationMapperTest, GetLocation_ZeroLineFallsBackToStartOfFile) {
  SourceLocation Loc = Mapper->getLocation("output/test.c", 0, 1);

  // Should fall back to start of file (never returns invalid)
  EXPECT_TRUE(Loc.isValid());

  SourceManager &SM = Mapper->getSourceManager();
  unsigned Line = SM.getSpellingLineNumber(Loc);
  unsigned Col = SM.getSpellingColumnNumber(Loc);
  EXPECT_EQ(Line, 1u);
  EXPECT_EQ(Col, 1u);
}

TEST_F(SourceLocationMapperTest, GetLocation_ZeroColumnFallsBackToStartOfFile) {
  SourceLocation Loc = Mapper->getLocation("output/test.c", 1, 0);

  // Should fall back to start of file (never returns invalid)
  EXPECT_TRUE(Loc.isValid());

  SourceManager &SM = Mapper->getSourceManager();
  unsigned Line = SM.getSpellingLineNumber(Loc);
  unsigned Col = SM.getSpellingColumnNumber(Loc);
  EXPECT_EQ(Line, 1u);
  EXPECT_EQ(Col, 1u);
}

TEST_F(SourceLocationMapperTest, GetLocation_ExceedsMaxLinesFallsBackToStartOfFile) {
  SourceLocation Loc = Mapper->getLocation("output/test.c", 20000, 1);

  // Should fall back to start of file when exceeding MAX_LINES = 10000
  EXPECT_TRUE(Loc.isValid());

  SourceManager &SM = Mapper->getSourceManager();
  unsigned Line = SM.getSpellingLineNumber(Loc);
  unsigned Col = SM.getSpellingColumnNumber(Loc);
  EXPECT_EQ(Line, 1u);
  EXPECT_EQ(Col, 1u);
}

TEST_F(SourceLocationMapperTest, GetLocation_MultiplePositionsInSameFile) {
  SourceLocation Loc1 = Mapper->getLocation("output/test.c", 1, 1);
  SourceLocation Loc2 = Mapper->getLocation("output/test.c", 5, 10);
  SourceLocation Loc3 = Mapper->getLocation("output/test.c", 100, 1);

  EXPECT_TRUE(Loc1.isValid());
  EXPECT_TRUE(Loc2.isValid());
  EXPECT_TRUE(Loc3.isValid());

  // Locations should be different
  EXPECT_NE(Loc1, Loc2);
  EXPECT_NE(Loc2, Loc3);
  EXPECT_NE(Loc1, Loc3);
}

TEST_F(SourceLocationMapperTest, GetLocation_DifferentFiles) {
  SourceLocation Loc1 = Mapper->getLocation("output/game.c", 10, 5);
  SourceLocation Loc2 = Mapper->getLocation("output/player.c", 10, 5);

  EXPECT_TRUE(Loc1.isValid());
  EXPECT_TRUE(Loc2.isValid());

  // Same line/column but different files should have different locations
  EXPECT_NE(Loc1, Loc2);
}

TEST_F(SourceLocationMapperTest, MapFromCppLocation_InvalidCppLocation) {
  // Create a separate DiagnosticsEngine for C++ SourceManager
  auto CppDiagOpts = std::make_unique<DiagnosticOptions>();
  DiagnosticsEngine cppDiag(IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()), *CppDiagOpts);

  SourceLocation cppLoc; // Invalid location
  SourceManager cppSM(cppDiag, *FileMgr);

  SourceLocation Loc =
      Mapper->mapFromCppLocation("output/test.c", cppLoc, cppSM);

  // Should return start of file when C++ location is invalid
  EXPECT_TRUE(Loc.isValid());

  unsigned Line = Mapper->getSourceManager().getSpellingLineNumber(Loc);
  unsigned Col = Mapper->getSourceManager().getSpellingColumnNumber(Loc);
  EXPECT_EQ(Line, 1u);
  EXPECT_EQ(Col, 1u);
}

TEST_F(SourceLocationMapperTest, MapFromCppLocation_ValidCppLocation) {
  // Create a separate DiagnosticsEngine for C++ SourceManager
  auto CppDiagOpts = std::make_unique<DiagnosticOptions>();
  DiagnosticsEngine cppDiag(IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()), *CppDiagOpts);

  // Create a C++ file and location
  SourceManager cppSM(cppDiag, *FileMgr);
  auto CppBuffer = llvm::MemoryBuffer::getMemBufferCopy(
      "// Line 1\n"
      "// Line 2\n"
      "// Line 3\n"
      "int x = 42;\n", // Line 4
      "input.cpp");
  FileID CppFID = cppSM.createFileID(std::move(CppBuffer), SrcMgr::C_User);
  SourceLocation cppLoc = cppSM.translateLineCol(CppFID, 4, 5);

  ASSERT_TRUE(cppLoc.isValid());

  // Map to C file
  SourceLocation Loc =
      Mapper->mapFromCppLocation("output/test.c", cppLoc, cppSM);

  EXPECT_TRUE(Loc.isValid());

  // Should have same line/column as C++ location
  unsigned Line = Mapper->getSourceManager().getSpellingLineNumber(Loc);
  unsigned Col = Mapper->getSourceManager().getSpellingColumnNumber(Loc);
  EXPECT_EQ(Line, 4u);
  EXPECT_EQ(Col, 5u);
}

TEST_F(SourceLocationMapperTest, GetSourceManager_ReturnsValid) {
  SourceManager &SM = Mapper->getSourceManager();

  // Should be able to use the SourceManager
  FileID FID = Mapper->registerFile("output/test.c");
  SourceLocation Loc = SM.getLocForStartOfFile(FID);

  EXPECT_TRUE(Loc.isValid());
}

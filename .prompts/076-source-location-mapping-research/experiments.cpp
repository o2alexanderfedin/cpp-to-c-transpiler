// Experiments for SourceLocation Mapping Research
// This file contains 4 experiments to test SourceManager and SourceLocation APIs
// Compiled independently from the main transpiler

#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>

using namespace clang;
using namespace llvm;

// =============================================================================
// Experiment 1: Register a File with SourceManager
// =============================================================================
void experiment1_registerFile() {
  outs() << "\n=== Experiment 1: Register a File ===\n";

  // Step 1: Create FileManager and DiagnosticsEngine
  FileSystemOptions FileSystemOpts;
  FileManager FileMgr(FileSystemOpts);

  IntrusiveRefCntPtr<DiagnosticOptions> DiagOpts = new DiagnosticOptions();
  DiagnosticsEngine Diag(
      IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()),
      DiagOpts.get());

  // Step 2: Create SourceManager
  SourceManager SrcMgr(Diag, FileMgr);

  // Step 3: Create a synthetic MemoryBuffer for a target C file
  const char* filePath = "output/generated.c";
  const char* fileContent = "// Generated C file\n";

  auto Buffer = MemoryBuffer::getMemBufferCopy(fileContent, filePath);

  // Step 4: Register the buffer with SourceManager
  FileID FID = SrcMgr.createFileID(std::move(Buffer), SrcMgr::C_User);

  // Step 5: Verify the FileID is valid
  if (FID.isValid()) {
    outs() << "SUCCESS: FileID is valid\n";
    outs() << "  FileID opaque value: " << FID.getHashValue() << "\n";
  } else {
    outs() << "FAILURE: FileID is invalid\n";
  }
}

// =============================================================================
// Experiment 2: Create Basic Location (start of file)
// =============================================================================
void experiment2_createBasicLocation() {
  outs() << "\n=== Experiment 2: Create Basic Location ===\n";

  // Setup (same as Experiment 1)
  FileSystemOptions FileSystemOpts;
  FileManager FileMgr(FileSystemOpts);
  IntrusiveRefCntPtr<DiagnosticOptions> DiagOpts = new DiagnosticOptions();
  DiagnosticsEngine Diag(
      IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()),
      DiagOpts.get());
  SourceManager SrcMgr(Diag, FileMgr);

  const char* filePath = "output/generated.h";
  const char* fileContent = "// Generated header\n";
  auto Buffer = MemoryBuffer::getMemBufferCopy(fileContent, filePath);
  FileID FID = SrcMgr.createFileID(std::move(Buffer), SrcMgr::C_User);

  // Step 1: Get SourceLocation for start of file
  SourceLocation StartLoc = SrcMgr.getLocForStartOfFile(FID);

  // Step 2: Verify the location is valid
  if (StartLoc.isValid()) {
    outs() << "SUCCESS: SourceLocation is valid\n";
    outs() << "  Raw encoding: " << StartLoc.getRawEncoding() << "\n";
    outs() << "  Is file location: " << (StartLoc.isFileID() ? "yes" : "no") << "\n";
    outs() << "  Is macro location: " << (StartLoc.isMacroID() ? "yes" : "no") << "\n";

    // Print the location using SourceManager
    StartLoc.print(outs(), SrcMgr);
    outs() << "\n";
  } else {
    outs() << "FAILURE: SourceLocation is invalid\n";
  }
}

// =============================================================================
// Experiment 3: Line/Column Offsets
// =============================================================================
void experiment3_lineColumnOffsets() {
  outs() << "\n=== Experiment 3: Line/Column Offsets ===\n";

  // Setup
  FileSystemOptions FileSystemOpts;
  FileManager FileMgr(FileSystemOpts);
  IntrusiveRefCntPtr<DiagnosticOptions> DiagOpts = new DiagnosticOptions();
  DiagnosticsEngine Diag(
      IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()),
      DiagOpts.get());
  SourceManager SrcMgr(Diag, FileMgr);

  // Create a multi-line file
  const char* filePath = "output/multiline.c";
  const char* fileContent =
    "// Line 1\n"
    "int x = 42;\n"
    "int y = 100;\n"
    "int z = 200;\n";

  auto Buffer = MemoryBuffer::getMemBufferCopy(fileContent, filePath);
  FileID FID = SrcMgr.createFileID(std::move(Buffer), SrcMgr::C_User);

  // Test different line/column positions
  struct TestCase {
    unsigned line;
    unsigned col;
    const char* description;
  };

  TestCase testCases[] = {
    {1, 1, "First line, first column"},
    {2, 1, "Second line, first column"},
    {2, 5, "Second line, column 5 (at 'x')"},
    {4, 1, "Fourth line, first column"},
  };

  for (const auto& tc : testCases) {
    outs() << "\nTest: " << tc.description << " (line=" << tc.line << ", col=" << tc.col << ")\n";

    SourceLocation Loc = SrcMgr.translateLineCol(FID, tc.line, tc.col);

    if (Loc.isValid()) {
      outs() << "  SUCCESS: Location is valid\n";
      outs() << "  Raw encoding: " << Loc.getRawEncoding() << "\n";
      outs() << "  Location string: ";
      Loc.print(outs(), SrcMgr);
      outs() << "\n";

      // Verify we can get line/column back
      unsigned Line = SrcMgr.getSpellingLineNumber(Loc);
      unsigned Col = SrcMgr.getSpellingColumnNumber(Loc);
      outs() << "  Verified: line=" << Line << ", col=" << Col << "\n";

      if (Line == tc.line && Col == tc.col) {
        outs() << "  Round-trip SUCCESSFUL\n";
      } else {
        outs() << "  Round-trip FAILED (expected line=" << tc.line << ", col=" << tc.col << ")\n";
      }
    } else {
      outs() << "  FAILURE: Location is invalid\n";
    }
  }
}

// =============================================================================
// Experiment 4: Multiple Files
// =============================================================================
void experiment4_multipleFiles() {
  outs() << "\n=== Experiment 4: Multiple Files ===\n";

  // Setup
  FileSystemOptions FileSystemOpts;
  FileManager FileMgr(FileSystemOpts);
  IntrusiveRefCntPtr<DiagnosticOptions> DiagOpts = new DiagnosticOptions();
  DiagnosticsEngine Diag(
      IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()),
      DiagOpts.get());
  SourceManager SrcMgr(Diag, FileMgr);

  // Register multiple files
  struct FileInfo {
    const char* path;
    const char* content;
    FileID fid;
    SourceLocation loc;
  };

  FileInfo files[] = {
    {"output/game.h", "// Game header\n#ifndef GAME_H\n#define GAME_H\n", FileID(), SourceLocation()},
    {"output/game.c", "// Game implementation\n#include \"game.h\"\n", FileID(), SourceLocation()},
    {"output/player.h", "// Player header\n", FileID(), SourceLocation()},
    {"output/player.c", "// Player implementation\n", FileID(), SourceLocation()},
  };

  // Register all files
  for (auto& file : files) {
    auto Buffer = MemoryBuffer::getMemBufferCopy(file.content, file.path);
    file.fid = SrcMgr.createFileID(std::move(Buffer), SrcMgr::C_User);
    file.loc = SrcMgr.getLocForStartOfFile(file.fid);

    outs() << "\nRegistered: " << file.path << "\n";
    outs() << "  FileID valid: " << (file.fid.isValid() ? "yes" : "no") << "\n";
    outs() << "  FileID hash: " << file.fid.getHashValue() << "\n";
    outs() << "  Location valid: " << (file.loc.isValid() ? "yes" : "no") << "\n";
    outs() << "  Location encoding: " << file.loc.getRawEncoding() << "\n";
    outs() << "  Location string: ";
    file.loc.print(outs(), SrcMgr);
    outs() << "\n";
  }

  // Verify all FileIDs are distinct
  outs() << "\nVerifying FileIDs are distinct:\n";
  for (size_t i = 0; i < 4; ++i) {
    for (size_t j = i + 1; j < 4; ++j) {
      if (files[i].fid == files[j].fid) {
        outs() << "  FAILURE: " << files[i].path << " and " << files[j].path << " have same FileID\n";
      }
    }
  }
  outs() << "  All FileIDs are distinct\n";

  // Test creating locations in different files
  outs() << "\nTesting line/column in different files:\n";
  for (const auto& file : files) {
    SourceLocation Loc = SrcMgr.translateLineCol(file.fid, 1, 1);
    outs() << "  " << file.path << " at (1,1): ";
    if (Loc.isValid()) {
      Loc.print(outs(), SrcMgr);
      outs() << " - VALID\n";
    } else {
      outs() << "INVALID\n";
    }
  }
}

// =============================================================================
// Main
// =============================================================================
int main() {
  outs() << "SourceLocation Mapping Experiments\n";
  outs() << "====================================\n";

  experiment1_registerFile();
  experiment2_createBasicLocation();
  experiment3_lineColumnOffsets();
  experiment4_multipleFiles();

  outs() << "\n=== All Experiments Complete ===\n";
  return 0;
}

#pragma once

#include "FileOriginTracker.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include <string>

// ASTConsumer that handles the translation unit
// Single Responsibility: Consume and process the AST
class CppToCConsumer : public clang::ASTConsumer {
  clang::ASTContext &Context;
  std::string InputFilename;  // Input source file name
  std::string SourceDir;      // Source directory for structure preservation

  // Phase 34 (v2.5.0): File origin tracking for multi-file transpilation
  cpptoc::FileOriginTracker fileOriginTracker;

public:
  explicit CppToCConsumer(clang::ASTContext &Context, const std::string &Filename,
                         const std::string &SrcDir = "")
    : Context(Context), InputFilename(Filename), SourceDir(SrcDir),
      fileOriginTracker(Context.getSourceManager()) {}

  // Called after entire translation unit is parsed
  void HandleTranslationUnit(clang::ASTContext &Context) override;

  // Phase 34: Accessor for FileOriginTracker (used by CppToCVisitor)
  cpptoc::FileOriginTracker& getFileOriginTracker() { return fileOriginTracker; }
};

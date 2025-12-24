#pragma once

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include <string>

// ASTConsumer that handles the translation unit
// Single Responsibility: Consume and process the AST
class CppToCConsumer : public clang::ASTConsumer {
  clang::ASTContext &Context;
  std::string InputFilename;  // Input source file name

public:
  explicit CppToCConsumer(clang::ASTContext &Context, const std::string &Filename)
    : Context(Context), InputFilename(Filename) {}

  // Called after entire translation unit is parsed
  void HandleTranslationUnit(clang::ASTContext &Context) override;
};

#pragma once

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"

// ASTConsumer that handles the translation unit
// Single Responsibility: Consume and process the AST
class CppToCConsumer : public clang::ASTConsumer {
  clang::ASTContext &Context;

public:
  explicit CppToCConsumer(clang::ASTContext &Context) : Context(Context) {}

  // Called after entire translation unit is parsed
  void HandleTranslationUnit(clang::ASTContext &Context) override;
};

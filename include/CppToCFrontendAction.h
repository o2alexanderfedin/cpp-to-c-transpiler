#pragma once

#include "clang/Frontend/FrontendAction.h"
#include "clang/Frontend/CompilerInstance.h"
#include <memory>

// FrontendAction that creates our ASTConsumer
// Single Responsibility: Create and configure AST consumer
class CppToCFrontendAction : public clang::ASTFrontendAction {
public:
  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &CI, llvm::StringRef file) override;
};

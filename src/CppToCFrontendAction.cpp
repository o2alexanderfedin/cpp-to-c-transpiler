#include "CppToCFrontendAction.h"
#include "CppToCConsumer.h"

std::unique_ptr<clang::ASTConsumer>
CppToCFrontendAction::CreateASTConsumer(clang::CompilerInstance &CI,
                                        llvm::StringRef file) {
  // Create and return our custom AST consumer
  return std::make_unique<CppToCConsumer>(CI.getASTContext());
}

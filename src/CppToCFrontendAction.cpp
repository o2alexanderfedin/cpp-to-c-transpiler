#include "CppToCFrontendAction.h"
#include "CppToCConsumer.h"

// External accessor for source directory (defined in main.cpp)
extern std::string getSourceDir();

std::unique_ptr<clang::ASTConsumer>
CppToCFrontendAction::CreateASTConsumer(clang::CompilerInstance &CI,
                                        llvm::StringRef file) {
  // Get source directory from command line
  std::string sourceDir = getSourceDir();

  // Create and return our custom AST consumer with the input filename and source directory
  return std::make_unique<CppToCConsumer>(CI.getASTContext(), file.str(), sourceDir);
}

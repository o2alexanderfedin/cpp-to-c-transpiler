// cpptoc - C++ to C Transpiler
// Main entry point using Clang LibTooling

#include "CppToCFrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"

using namespace clang::tooling;

// Define tool category for command line options
static llvm::cl::OptionCategory ToolCategory("cpptoc options");

int main(int argc, const char **argv) {
  // Parse command line arguments
  auto ExpectedParser = CommonOptionsParser::create(argc, argv, ToolCategory);
  if (!ExpectedParser) {
    llvm::errs() << ExpectedParser.takeError();
    return 1;
  }

  CommonOptionsParser &OptionsParser = ExpectedParser.get();

  // Create ClangTool with parsed options
  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());

  // Run tool with our custom FrontendAction
  return Tool.run(newFrontendActionFactory<CppToCFrontendAction>().get());
}

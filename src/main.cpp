// cpptoc - C++ to C Transpiler
// Main entry point using Clang LibTooling

#include "CppToCFrontendAction.h"
#include "DependencyGraphVisualizer.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"

using namespace clang::tooling;

// Define tool category for command line options
static llvm::cl::OptionCategory ToolCategory("cpptoc options");

// Command line option for #pragma once support
static llvm::cl::opt<bool> UsePragmaOnce(
    "use-pragma-once",
    llvm::cl::desc("Use #pragma once instead of traditional include guards"),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(false));

// Command line option for dependency visualization
static llvm::cl::opt<std::string> DumpDeps(
    "dump-deps",
    llvm::cl::desc("Generate dependency graph in DOT format and save to file"),
    llvm::cl::value_desc("filename"),
    llvm::cl::cat(ToolCategory));

static llvm::cl::opt<bool> VisualizeDeps(
    "visualize-deps",
    llvm::cl::desc("Generate dependency graph visualization (saved as deps.dot)"),
    llvm::cl::cat(ToolCategory));

// Global accessor for pragma once setting
bool shouldUsePragmaOnce() {
  return UsePragmaOnce;
}

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
  int result = Tool.run(newFrontendActionFactory<CppToCFrontendAction>().get());

  // Handle dependency visualization if requested
  if (VisualizeDeps || !DumpDeps.empty()) {
    // TODO: This is a placeholder for integration with HeaderSeparator
    // In a full implementation, we would:
    // 1. Track dependencies during AST traversal
    // 2. Store them in a global/static structure
    // 3. Use them here to generate the visualization
    //
    // For now, we demonstrate the visualizer with example data
    DependencyGraphVisualizer viz;

    llvm::outs() << "\nGenerating dependency graph visualization...\n";

    // Example: Add some dependencies (in real implementation, these would come from HeaderSeparator)
    // viz.addFile("Example.h", {});
    // viz.addFile("Example.c", {"Example.h"});

    // Determine output filename
    std::string outputFile = DumpDeps.empty() ? "deps.dot" : DumpDeps.getValue();

    if (viz.writeToFile(outputFile)) {
      llvm::outs() << "Dependency graph written to: " << outputFile << "\n";
      llvm::outs() << "View with: dot -Tpng " << outputFile << " -o deps.png\n";
    } else {
      llvm::errs() << "Error: Failed to write dependency graph to " << outputFile << "\n";
      return 1;
    }
  }

  return result;
}

// cpptoc - C++ to C Transpiler
// Main entry point using Clang LibTooling

#include "CppToCFrontendAction.h"
#include "DependencyGraphVisualizer.h"
#include "ACSLGenerator.h"
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

// Epic #193: ACSL Annotation Generation for Transpiled Code
// Story #195: CLI flags for ACSL generation

// Command line option to enable ACSL generation
static llvm::cl::opt<bool> GenerateACSL(
    "generate-acsl",
    llvm::cl::desc("Generate ACSL annotations for formal verification (default: off)"),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(false));

// ACSL coverage level enum
enum ACSLCoverageLevelEnum {
  Basic,  // Function contracts only (requires, ensures, assigns)
  Full    // Function contracts + loop invariants + class invariants
};

// Command line option for ACSL coverage level
static llvm::cl::opt<ACSLCoverageLevelEnum> ACSLCoverageLevel(
    "acsl-level",
    llvm::cl::desc("ACSL annotation coverage level (requires --generate-acsl)"),
    llvm::cl::values(
        clEnumValN(Basic, "basic", "Function contracts only (default)"),
        clEnumValN(Full, "full", "Function contracts + loop invariants + class invariants")),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(Basic));

// ACSL output mode enum
enum ACSLOutputModeEnum {
  Inline,    // Annotations inline in generated C code
  Separate   // Annotations in separate .acsl files
};

// Command line option for ACSL output mode
static llvm::cl::opt<ACSLOutputModeEnum> ACSLOutput(
    "acsl-output",
    llvm::cl::desc("ACSL output mode (requires --generate-acsl)"),
    llvm::cl::values(
        clEnumValN(Inline, "inline", "Annotations inline in C code (default)"),
        clEnumValN(Separate, "separate", "Annotations in separate .acsl files")),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(Inline));

// Phase 6 (v1.23.0): Advanced Memory Predicates
// Command line option for ACSL memory predicates
static llvm::cl::opt<bool> ACSLMemoryPredicates(
    "acsl-memory-predicates",
    llvm::cl::desc("Generate advanced memory predicates (allocable, freeable, block_length) (requires --generate-acsl)"),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(false));

// Phase 11 (v2.4.0): Template Monomorphization
// Command line option to enable template monomorphization
static llvm::cl::opt<bool> TemplateMonomorphization(
    "template-monomorphization",
    llvm::cl::desc("Enable template monomorphization (default: on)"),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(true));

// Command line option for template instantiation limit
static llvm::cl::opt<unsigned int> TemplateInstantiationLimit(
    "template-instantiation-limit",
    llvm::cl::desc("Maximum number of template instantiations (default: 1000)"),
    llvm::cl::value_desc("N"),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(1000));

// Phase 12 (v2.5.0): Exception Handling
// Command line option to enable exception handling translation
static llvm::cl::opt<bool> EnableExceptions(
    "enable-exceptions",
    llvm::cl::desc("Enable exception handling translation (try-catch-throw to setjmp/longjmp) (default: on)"),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(true));

// Exception handling model enum
enum ExceptionModelEnum {
  SJLJ,    // Setjmp/Longjmp model (default)
  Tables   // Table-based model (future)
};

// Command line option for exception handling model
static llvm::cl::opt<ExceptionModelEnum> ExceptionModel(
    "exception-model",
    llvm::cl::desc("Exception handling model (default: sjlj)"),
    llvm::cl::values(
        clEnumValN(SJLJ, "sjlj", "Setjmp/longjmp model (default)"),
        clEnumValN(Tables, "tables", "Table-based model (future)")),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(SJLJ));

// Phase 13 (v2.6.0): RTTI Support
// Command line option to enable RTTI translation
static llvm::cl::opt<bool> EnableRTTI(
    "enable-rtti",
    llvm::cl::desc("Enable RTTI translation (typeid and dynamic_cast) (default: on)"),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(true));

// Global accessor for pragma once setting
bool shouldUsePragmaOnce() {
  return UsePragmaOnce;
}

// Global accessor for ACSL generation setting
bool shouldGenerateACSL() {
  return GenerateACSL;
}

// Global accessor for ACSL level
ACSLLevel getACSLLevel() {
  return (ACSLCoverageLevel == Basic) ? ACSLLevel::Basic : ACSLLevel::Full;
}

// Global accessor for ACSL output mode
ACSLOutputMode getACSLOutputMode() {
  return (ACSLOutput == Inline) ? ACSLOutputMode::Inline : ACSLOutputMode::Separate;
}

// Global accessor for ACSL memory predicates setting (Phase 6, v1.23.0)
bool shouldGenerateMemoryPredicates() {
  return ACSLMemoryPredicates;
}

// Global accessor for template monomorphization setting (Phase 11, v2.4.0)
bool shouldMonomorphizeTemplates() {
  return TemplateMonomorphization;
}

// Global accessor for template instantiation limit (Phase 11, v2.4.0)
unsigned int getTemplateInstantiationLimit() {
  return TemplateInstantiationLimit;
}

// Global accessor for exception handling setting (Phase 12, v2.5.0)
bool shouldEnableExceptions() {
  return EnableExceptions;
}

// Global accessor for exception model (Phase 12, v2.5.0)
std::string getExceptionModel() {
  return (ExceptionModel == SJLJ) ? "sjlj" : "tables";
}

// Global accessor for RTTI setting (Phase 13, v2.6.0)
bool shouldEnableRTTI() {
  return EnableRTTI;
}

int main(int argc, const char **argv) {
  // Parse command line arguments
  auto ExpectedParser = CommonOptionsParser::create(argc, argv, ToolCategory);
  if (!ExpectedParser) {
    llvm::errs() << ExpectedParser.takeError();
    return 1;
  }

  CommonOptionsParser &OptionsParser = ExpectedParser.get();

  // Story #195: Validate ACSL option dependencies
  // --acsl-level and --acsl-output require --generate-acsl to be enabled
  if (!GenerateACSL && ACSLCoverageLevel.getNumOccurrences() > 0) {
    llvm::errs() << "Error: --acsl-level requires --generate-acsl to be enabled\n";
    llvm::errs() << "Use --generate-acsl to enable ACSL annotation generation\n";
    return 1;
  }

  if (!GenerateACSL && ACSLOutput.getNumOccurrences() > 0) {
    llvm::errs() << "Error: --acsl-output requires --generate-acsl to be enabled\n";
    llvm::errs() << "Use --generate-acsl to enable ACSL annotation generation\n";
    return 1;
  }

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

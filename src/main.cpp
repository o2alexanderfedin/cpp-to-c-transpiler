// cpptoc - C++ to C Transpiler
// Main entry point using Clang LibTooling

#include "CppToCFrontendAction.h"
#include "DependencyGraphVisualizer.h"
#include "ACSLGenerator.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include <filesystem>
#include <unordered_set>

namespace fs = std::filesystem;
using namespace clang::tooling;

// Define tool category for command line options
static llvm::cl::OptionCategory ToolCategory("cpptoc options");

// Command line option for #pragma once support
static llvm::cl::opt<bool> UsePragmaOnce(
    "use-pragma-once",
    llvm::cl::desc("Use #pragma once instead of traditional include guards"),
    llvm::cl::cat(ToolCategory),
    llvm::cl::init(false));

// Command line option for output directory
static llvm::cl::opt<std::string> OutputDir(
    "output-dir",
    llvm::cl::desc("Output directory for generated .c and .h files (default: current directory)"),
    llvm::cl::value_desc("directory"),
    llvm::cl::cat(ToolCategory));

// Command line option for source directory (structure preservation + auto-discovery)
static llvm::cl::opt<std::string> SourceDir(
    "source-dir",
    llvm::cl::desc("(REQUIRED) Project root directory for transpilation.\n"
                   "cpptoc operates on a per-project basis and automatically discovers\n"
                   "all .cpp, .cxx, and .cc files recursively in this directory.\n"
                   "Individual file arguments are IGNORED.\n"
                   "Automatically excludes: .git, .svn, build*, cmake-build-*,\n"
                   "node_modules, vendor, and hidden directories.\n"
                   "Output preserves the source directory structure."),
    llvm::cl::value_desc("directory"),
    llvm::cl::Required,
    llvm::cl::cat(ToolCategory));

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

// Global accessor for output directory setting
std::string getOutputDir() {
  return OutputDir;
}

// Global accessor for source directory setting
std::string getSourceDir() {
  return SourceDir;
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

// ============================================================================
// File Discovery Functions (Recursive .cpp file discovery)
// ============================================================================

// Helper: Check if file has valid C++ source extension
static bool isCppSourceFile(const fs::path& path) {
  static const std::unordered_set<std::string> validExtensions = {
    ".cpp", ".cxx", ".cc"
  };
  return validExtensions.count(path.extension().string()) > 0;
}

// Helper: Check if directory should be excluded from discovery
static bool shouldExcludeDirectory(const std::string& dirName) {
  // Exact match exclusions
  static const std::unordered_set<std::string> excludedDirs = {
    ".git", ".svn", ".hg",
    "node_modules", "vendor"
  };

  if (excludedDirs.count(dirName) > 0) {
    return true;
  }

  // Prefix pattern exclusions
  if (dirName.find("build") == 0) return true;  // build, build-debug, etc.
  if (dirName.find("cmake-build-") == 0) return true;  // CLion build dirs
  if (dirName.size() > 0 && dirName[0] == '.' && dirName != "..") return true;  // Hidden dirs

  return false;
}

// Main file discovery function: recursively finds all .cpp/.cxx/.cc files
static std::vector<std::string> discoverSourceFiles(const std::string& sourceDir) {
  std::vector<std::string> discoveredFiles;

  // Validate source directory
  fs::path sourcePath(sourceDir);
  if (!fs::exists(sourcePath)) {
    llvm::errs() << "Error: Source directory does not exist: " << sourceDir << "\n";
    return discoveredFiles;
  }

  if (!fs::is_directory(sourcePath)) {
    llvm::errs() << "Error: Not a directory: " << sourceDir << "\n";
    return discoveredFiles;
  }

  // Configure directory iteration options
  fs::directory_options opts = fs::directory_options::skip_permission_denied;

  // Recursively iterate directory tree
  std::error_code ec;
  for (auto it = fs::recursive_directory_iterator(sourcePath, opts, ec);
       it != fs::recursive_directory_iterator();
       it.increment(ec)) {

    if (ec) {
      llvm::errs() << "Warning: " << ec.message() << " for " << it->path() << "\n";
      ec.clear();
      continue;
    }

    // Skip excluded directories
    if (it->is_directory()) {
      std::string dirName = it->path().filename().string();
      if (shouldExcludeDirectory(dirName)) {
        it.disable_recursion_pending();  // Don't descend into this directory
        continue;
      }
    }

    // Collect C++ source files
    if (it->is_regular_file() && isCppSourceFile(it->path())) {
      // Use absolute paths for consistency
      discoveredFiles.push_back(fs::absolute(it->path()).string());
    }
  }

  return discoveredFiles;
}

// ============================================================================
// Main Entry Point
// ============================================================================

int main(int argc, const char **argv) {
  // Project-based transpilation: always add dummy file for CommonOptionsParser
  // CommonOptionsParser requires at least one file argument, but we'll discover files later
  std::vector<const char*> modifiedArgv(argv, argv + argc);

  // Add dummy file before "--" to satisfy CommonOptionsParser
  // Individual files are IGNORED - we always discover all files from --source-dir
  auto insertPos = std::find_if(modifiedArgv.begin(), modifiedArgv.end(),
                                 [](const char* s) { return std::string(s) == "--"; });
  modifiedArgv.insert(insertPos, "__dummy_for_discovery__.cpp");
  argc++;

  // Parse command line arguments
  auto ExpectedParser = CommonOptionsParser::create(argc, modifiedArgv.data(), ToolCategory);
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

  // ============================================================================
  // Project-Based Transpilation (--source-dir is REQUIRED)
  // ============================================================================
  std::vector<std::string> sourceFiles;

  // Require --source-dir for project-based transpilation
  if (SourceDir.empty()) {
    llvm::errs() << "Error: --source-dir is required for project-based transpilation\n"
                 << "Usage: cpptoc --source-dir=<project-root> --output-dir=<output> --\n"
                 << "Example: cpptoc --source-dir=src/ --output-dir=build/ --\n";
    return 1;
  }

  // AUTO-DISCOVERY MODE (project-based transpilation only)
  // Individual file arguments are IGNORED - we always transpile the entire project
  llvm::outs() << "Auto-discovering C++ source files in: " << SourceDir << "\n";

  sourceFiles = discoverSourceFiles(SourceDir);

  if (sourceFiles.empty()) {
    llvm::errs() << "Warning: No C++ source files (.cpp, .cxx, .cc) found in "
                 << SourceDir << "\n";
    return 1;  // Non-fatal error code
  }

  llvm::outs() << "Discovered " << sourceFiles.size() << " file(s) for transpilation\n";

  // Create ClangTool with discovered or provided files
  ClangTool Tool(OptionsParser.getCompilations(), sourceFiles);

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

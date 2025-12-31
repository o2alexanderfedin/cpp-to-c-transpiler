#pragma once

#include <string>
#include <vector>

namespace cpptoc {
namespace pipeline {

/// ACSL coverage level enumeration
enum class ACSLCoverageLevel {
  Basic,  ///< Basic ACSL annotations (preconditions, postconditions)
  Full    ///< Full ACSL coverage (including loop invariants, assertions)
};

/// ACSL output mode enumeration
enum class ACSLOutputMode {
  Inline,    ///< Inline ACSL comments in generated C code
  Separate   ///< Separate ACSL specification files (.acsl)
};

/// Exception handling model enumeration
enum class ExceptionModel {
  SetjmpLongjmp,  ///< setjmp/longjmp-based exception handling (portable)
  GotoCleanup     ///< goto-based cleanup (simpler, but limited)
};

/// Pipeline configuration extracted from CLI arguments
struct PipelineConfig {
  // ========== Input/Output Paths ==========

  /// Source directory for file discovery and structure preservation
  std::string sourceDir;

  /// Output directory for generated .c/.h files
  std::string outputDir;

  /// Explicit input files (if provided, skip auto-discovery)
  std::vector<std::string> inputFiles;

  // ========== Code Generation Options ==========

  /// Use #pragma once instead of traditional include guards
  bool usePragmaOnce = false;

  // ========== ACSL Annotation Options ==========

  /// Generate ACSL annotations for formal verification
  bool generateACSL = false;

  /// ACSL coverage level (Basic or Full)
  ACSLCoverageLevel acslCoverageLevel = ACSLCoverageLevel::Basic;

  /// ACSL output mode (Inline or Separate)
  ACSLOutputMode acslOutputMode = ACSLOutputMode::Inline;

  /// Generate ACSL memory predicates (valid, separated, etc.)
  bool acslMemoryPredicates = false;

  // ========== Template Handling Options ==========

  /// Enable template monomorphization (generate C code for each instantiation)
  bool templateMonomorphization = true;

  /// Template instantiation depth limit (prevent infinite recursion)
  unsigned int templateInstantiationLimit = 256;

  // ========== Exception Handling Options ==========

  /// Enable C++ exception handling translation
  bool enableExceptions = true;

  /// Exception handling model (setjmp/longjmp or goto-based)
  ExceptionModel exceptionModel = ExceptionModel::SetjmpLongjmp;

  // ========== RTTI Options ==========

  /// Enable C++ RTTI (Run-Time Type Information) translation
  bool enableRTTI = true;

  // ========== Dependency Analysis Options ==========

  /// Dump dependency graph to file (GraphViz dot format)
  std::string dumpDependencies;

  /// Visualize dependencies (requires Graphviz)
  bool visualizeDependencies = false;
};

/// Parse command line arguments into PipelineConfig
///
/// Extracts all CLI options from argc/argv using llvm::cl and populates
/// a PipelineConfig struct. This allows passing configuration explicitly
/// instead of relying on global llvm::cl::opt variables.
///
/// @param argc Argument count from main()
/// @param argv Argument vector from main()
/// @return Populated PipelineConfig with parsed options
PipelineConfig parseCLIArgs(int argc, const char* const* argv);

}} // namespace cpptoc::pipeline

#include "pipeline/PipelineConfig.h"

namespace cpptoc {
namespace pipeline {

// Accessor functions defined in main.cpp (extern linkage)
// These provide access to the global llvm::cl::opt variables
extern bool shouldUsePragmaOnce();
extern std::string getOutputDir();
extern std::string getSourceDir();
extern bool shouldGenerateACSL();
extern bool shouldEnableTemplateMonomorphization();
extern unsigned int getTemplateInstantiationLimit();
extern bool shouldEnableExceptions();
extern bool shouldEnableRTTI();
extern std::string getDependencyDumpFile();
extern bool shouldVisualizeDependencies();

// Note: ACSL level/output mode and exception model accessors need to be added to main.cpp

PipelineConfig parseCLIArgs(int argc, const char* const* argv) {
  PipelineConfig config;

  // Note: llvm::cl::ParseCommandLineOptions is called in main.cpp
  // before this function. We just read the parsed values via accessors.

  // Input/Output paths
  config.sourceDir = getSourceDir();
  config.outputDir = getOutputDir();
  // inputFiles populated separately by file discovery or explicit args

  // Code generation options
  config.usePragmaOnce = shouldUsePragmaOnce();

  // ACSL options
  config.generateACSL = shouldGenerateACSL();
  // TODO: Add accessors for ACSL level, output mode, and memory predicates in main.cpp
  config.acslCoverageLevel = ACSLCoverageLevel::Basic;  // Default for now
  config.acslOutputMode = ACSLOutputMode::Inline;       // Default for now
  config.acslMemoryPredicates = false;                  // Default for now

  // Template options
  config.templateMonomorphization = shouldEnableTemplateMonomorphization();
  config.templateInstantiationLimit = getTemplateInstantiationLimit();

  // Exception handling options
  config.enableExceptions = shouldEnableExceptions();
  // TODO: Add accessor for exception model in main.cpp
  config.exceptionModel = ExceptionModel::SetjmpLongjmp;  // Default for now

  // RTTI options
  config.enableRTTI = shouldEnableRTTI();

  // Dependency analysis options
  config.dumpDependencies = getDependencyDumpFile();
  config.visualizeDependencies = shouldVisualizeDependencies();

  return config;
}

}} // namespace cpptoc::pipeline

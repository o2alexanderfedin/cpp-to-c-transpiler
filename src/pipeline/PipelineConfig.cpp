#include "pipeline/PipelineConfig.h"
#include "ACSLGenerator.h"  // For ACSLLevel and ACSLOutputMode

namespace cpptoc {
namespace pipeline {

// Accessor functions defined in main.cpp (extern linkage)
// These provide access to the global llvm::cl::opt variables
extern bool shouldUsePragmaOnce();
extern std::string getOutputDir();
extern std::string getSourceDir();
extern bool shouldGenerateACSL();
extern ::ACSLLevel getACSLLevel();  // Returns global namespace ACSLLevel
extern ::ACSLOutputMode getACSLOutputMode();  // Returns global namespace ACSLOutputMode
extern bool shouldGenerateMemoryPredicates();
extern bool shouldEnableTemplateMonomorphization();
extern unsigned int getTemplateInstantiationLimit();
extern bool shouldEnableExceptions();
extern std::string getExceptionModel();  // Returns "sjlj" or "tables"
extern bool shouldEnableRTTI();
extern std::string getDependencyDumpFile();
extern bool shouldVisualizeDependencies();

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

  // Convert from ACSLGenerator.h enums to PipelineConfig enums
  ::ACSLLevel acslLevel = getACSLLevel();
  config.acslCoverageLevel = (acslLevel == ::ACSLLevel::Basic)
      ? ACSLCoverageLevel::Basic
      : ACSLCoverageLevel::Full;

  ::ACSLOutputMode acslOutput = getACSLOutputMode();
  config.acslOutputMode = (acslOutput == ::ACSLOutputMode::Inline)
      ? ACSLOutputMode::Inline
      : ACSLOutputMode::Separate;

  config.acslMemoryPredicates = shouldGenerateMemoryPredicates();

  // Template options
  config.templateMonomorphization = shouldEnableTemplateMonomorphization();
  config.templateInstantiationLimit = getTemplateInstantiationLimit();

  // Exception handling options
  config.enableExceptions = shouldEnableExceptions();

  // Convert from string to ExceptionModel enum
  std::string exModel = getExceptionModel();
  config.exceptionModel = (exModel == "sjlj")
      ? ExceptionModel::SetjmpLongjmp
      : ExceptionModel::GotoCleanup;

  // RTTI options
  config.enableRTTI = shouldEnableRTTI();

  // Dependency analysis options
  config.dumpDependencies = getDependencyDumpFile();
  config.visualizeDependencies = shouldVisualizeDependencies();

  return config;
}

}} // namespace cpptoc::pipeline

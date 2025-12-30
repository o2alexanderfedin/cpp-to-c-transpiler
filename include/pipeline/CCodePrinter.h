#pragma once

#include "pipeline/PipelineConfig.h"
#include "TargetContext.h"
#include <string>

namespace cpptoc {
namespace pipeline {

/// C code printer - generates .c and .h files from C AST
///
/// Wraps CodeGenerator and FileOutputManager for clean pipeline integration.
/// Generates header (.h) and implementation (.c) files from the accumulated C AST.
///
/// **Strategy Pattern:**
/// Uses Strategy pattern through different separation strategies:
/// - Simple strategy: All decls in both header and impl (controlled by declarationOnly flag)
/// - HeaderSeparator strategy: Forward decls, header decls, impl decls (more sophisticated)
class CCodePrinter {
public:
  /// Construct printer with pipeline configuration
  explicit CCodePrinter(const PipelineConfig& config);

  /// Print C AST to .c and .h files for a translation unit
  ///
  /// Generates both header and implementation files from the C AST in TargetContext.
  /// Uses configuration to determine output directory, pragma once usage, etc.
  ///
  /// @param targetCtx TargetContext containing the C AST
  /// @param sourceFilePath Original source file path (for deriving output names)
  void print(TargetContext& targetCtx, const std::string& sourceFilePath);

  /// Print all C ASTs to files (called after all files processed)
  ///
  /// Generates files for all accumulated C translation units in TargetContext.
  void printAll(TargetContext& targetCtx);

private:
  const PipelineConfig& config_;
};

}} // namespace cpptoc::pipeline

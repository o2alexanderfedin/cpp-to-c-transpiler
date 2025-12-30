#pragma once

#include "pipeline/PipelineConfig.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "TargetContext.h"
#include "mapping/PathMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include <string>

namespace cpptoc {
namespace pipeline {

/// Dispatcher-based C++ to C AST transformation
///
/// Wraps the CppToCVisitorDispatcher setup and invocation for clean pipeline integration.
/// Accumulates transformed C nodes into the shared C ASTContext (TargetContext singleton).
///
/// **Strategy Pattern:**
/// The dispatcher uses Strategy pattern via handler registration.
/// Different transformation strategies can be selected by registering different handlers.
class DispatcherTransformer {
public:
  /// Construct transformer with pipeline configuration
  explicit DispatcherTransformer(const PipelineConfig& config);

  /// Transform C++ AST to C AST for a single translation unit
  ///
  /// Creates dispatcher, registers all handlers, and dispatches on the C++ TU.
  /// Results accumulate in TargetContext singleton.
  ///
  /// @param cppASTContext C++ ASTContext for the source file
  /// @param cppTU C++ TranslationUnitDecl for the source file
  /// @param sourceFilePath Path to the source file being processed
  void transform(
    clang::ASTContext& cppASTContext,
    clang::TranslationUnitDecl* cppTU,
    const std::string& sourceFilePath
  );

  /// Get the shared C AST context
  ///
  /// Returns the TargetContext singleton that contains the accumulated C AST.
  ///
  /// @return Reference to TargetContext singleton
  TargetContext& getTargetContext();

private:
  const PipelineConfig& config_;
};

}} // namespace cpptoc::pipeline

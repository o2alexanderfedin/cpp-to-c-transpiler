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
/// Accumulates transformed C nodes into a TargetContext instance (RAII pattern).
///
/// **Strategy Pattern:**
/// The dispatcher uses Strategy pattern via handler registration.
/// Different transformation strategies can be selected by registering different handlers.
///
/// **RAII Pattern:**
/// Owns its own TargetContext instance for complete isolation.
/// Each DispatcherTransformer has independent state - no shared singleton.
class DispatcherTransformer {
public:
  /// Construct transformer with pipeline configuration
  explicit DispatcherTransformer(const PipelineConfig& config);

  /// Transform C++ AST to C AST for a single translation unit
  ///
  /// Creates dispatcher, registers all handlers, and dispatches on the C++ TU.
  /// Results accumulate in this transformer's TargetContext instance.
  ///
  /// @param cppASTContext C++ ASTContext for the source file
  /// @param cppTU C++ TranslationUnitDecl for the source file
  /// @param sourceFilePath Path to the source file being processed
  void transform(
    clang::ASTContext& cppASTContext,
    clang::TranslationUnitDecl* cppTU,
    const std::string& sourceFilePath
  );

  /// Get the C AST context for this transformer
  ///
  /// Returns this transformer's TargetContext that contains the accumulated C AST.
  ///
  /// @return Reference to this transformer's TargetContext
  TargetContext& getTargetContext();

private:
  const PipelineConfig& config_;
  TargetContext targetCtx_;  ///< Owned TargetContext instance (RAII)
};

}} // namespace cpptoc::pipeline

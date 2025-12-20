// RuntimeModeInline.h - Inline runtime mode implementation
// Story #116: Implement Inline Runtime Mode
//
// This class handles embedding runtime code directly into generated C files
// for zero-dependency, self-contained output suitable for embedded systems
// and safety-critical applications.
//
// SOLID Principles:
//   - Single Responsibility: Manages inline runtime code generation only
//   - Open/Closed: Extensible for new runtime modules
//   - Interface Segregation: Clean API for runtime embedding
//   - Dependency Inversion: Depends on runtime abstractions, not implementations

#ifndef __RUNTIME_MODE_INLINE_H__
#define __RUNTIME_MODE_INLINE_H__

#include <string>
#include <set>

/// @brief Runtime features that can be embedded
enum class RuntimeFeature {
  Exceptions,   ///< Exception handling runtime (setjmp/longjmp + action tables)
  RTTI,         ///< Runtime type information (type_info, dynamic_cast)
  Memory,       ///< Memory management (coroutine frames, heap allocation)
  VInherit      ///< Virtual inheritance support (virtual base tables)
};

/// @brief Inline runtime mode - embeds runtime code in generated files
///
/// This class generates self-contained C code by embedding the necessary
/// runtime support directly into each output file. This eliminates the need
/// for external runtime libraries, making the output suitable for:
/// - Embedded systems (zero dependencies)
/// - Safety-critical applications (single-file certification)
/// - Minimal deployments (no runtime library distribution)
///
/// Usage:
///   RuntimeModeInline inlineMode;
///   inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);
///   std::string runtime = inlineMode.generateInlineRuntime();
///   // Prepend runtime to generated C code
class RuntimeModeInline {
private:
  /// @brief Set of runtime features used in the current translation unit
  std::set<RuntimeFeature> usedFeatures_;

public:
  /// @brief Constructor - initializes inline mode
  RuntimeModeInline();

  /// @brief Check if inline mode is active
  /// @return True (always true for this class)
  bool isInlineMode() const;

  /// @brief Mark a runtime feature as used
  /// @param feature The runtime feature to mark as used
  ///
  /// Calling this method ensures the corresponding runtime code will be
  /// included in the generated output. Only marked features are embedded.
  void markFeatureUsed(RuntimeFeature feature);

  /// @brief Embed exception handling runtime code
  /// @return C code for exception runtime (with include guards)
  ///
  /// Generates setjmp/longjmp-based exception handling runtime including:
  /// - Exception frame structures
  /// - throw/catch/rethrow functions
  /// - Action table support for destructors
  std::string embedExceptionRuntime() const;

  /// @brief Embed RTTI (Runtime Type Information) code
  /// @return C code for RTTI runtime (with include guards)
  ///
  /// Generates runtime type information support including:
  /// - type_info structures
  /// - dynamic_cast implementation
  /// - Type hierarchy traversal
  std::string embedRTTIRuntime() const;

  /// @brief Embed memory management runtime code
  /// @return C code for memory runtime (with include guards)
  ///
  /// Generates memory management support including:
  /// - Coroutine frame allocation
  /// - Heap management wrappers
  std::string embedMemoryRuntime() const;

  /// @brief Embed virtual inheritance runtime code
  /// @return C code for virtual inheritance runtime (with include guards)
  ///
  /// Generates virtual inheritance support including:
  /// - Virtual base tables
  /// - Virtual base offset calculation
  std::string embedVInheritRuntime() const;

  /// @brief Generate complete inline runtime for all used features
  /// @return Combined C code for all marked runtime features
  ///
  /// This method combines the runtime code for all features marked as used
  /// via markFeatureUsed(). Only used features are included, minimizing
  /// code size. Each feature is wrapped in preprocessor guards to prevent
  /// duplication in multi-file projects.
  std::string generateInlineRuntime() const;

private:
  /// @brief Read runtime source file and wrap with guards
  /// @param filename Path to runtime source file
  /// @param guardName Preprocessor guard macro name
  /// @return File contents wrapped with include guards
  std::string readRuntimeFile(const std::string &filename,
                               const std::string &guardName) const;
};

#endif // __RUNTIME_MODE_INLINE_H__

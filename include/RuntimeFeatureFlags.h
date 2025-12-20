// RuntimeFeatureFlags.h - Modular runtime feature flags
// Story #118: Implement Modular Runtime Feature Flags
//
// This class handles parsing and managing runtime feature flags from command line,
// allowing users to enable only the runtime features they need.
//
// SOLID Principles:
//   - Single Responsibility: Manages runtime feature flag parsing only
//   - Open/Closed: Extensible for new runtime features
//   - Interface Segregation: Clean API for flag management
//   - Dependency Inversion: Depends on RuntimeFeature abstraction

#ifndef __RUNTIME_FEATURE_FLAGS_H__
#define __RUNTIME_FEATURE_FLAGS_H__

#include <set>
#include <string>
#include <vector>
#include <stdexcept>

/// @brief Runtime features that can be enabled/disabled via command-line flags
/// This enum is shared with RuntimeModeInline and RuntimeModeLibrary
enum class RuntimeFeature {
  Exceptions,   ///< Exception handling runtime (setjmp/longjmp + action tables)
  RTTI,         ///< Runtime type information (type_info, dynamic_cast)
  Memory,       ///< Memory management (coroutine frames, heap allocation)
  VInherit      ///< Virtual inheritance support (virtual base tables)
};

/// @brief Modular runtime feature flags - parse and manage runtime features
///
/// This class parses command-line flags like --runtime=exceptions,rtti
/// and provides an API to query which features are enabled. This allows
/// users to include only the runtime code they actually need, optimizing
/// for code size and compilation speed.
///
/// Usage:
///   RuntimeFeatureFlags flags(argc, argv);
///   if (flags.isEnabled(RuntimeFeature::Exceptions)) {
///     // Generate exception handling code
///   }
///
/// Supported flags:
///   --runtime=exceptions     Enable exception handling only
///   --runtime=rtti           Enable RTTI only
///   --runtime=coroutines     Enable coroutine support (memory management)
///   --runtime=vinherit       Enable virtual inheritance only
///   --runtime=all            Enable all features (default)
///   --runtime=none           Disable all features (for testing)
///   --runtime=exceptions,rtti Multiple features (comma-separated)
class RuntimeFeatureFlags {
private:
  /// @brief Set of enabled runtime features
  std::set<RuntimeFeature> enabledFeatures_;

  /// @brief Module size estimates in bytes
  static constexpr size_t EXCEPTION_SIZE = 1000;  // 800-1200 bytes
  static constexpr size_t RTTI_SIZE = 800;        // 600-1000 bytes
  static constexpr size_t MEMORY_SIZE = 600;      // 400-800 bytes
  static constexpr size_t VINHERIT_SIZE = 700;    // 500-900 bytes

public:
  /// @brief Constructor - parse runtime flags from command line
  /// @param argc Argument count from main()
  /// @param argv Argument vector from main()
  /// @throws std::invalid_argument if unknown feature name encountered
  ///
  /// Parses command-line arguments looking for --runtime=<features> flag.
  /// If no flag found, defaults to all features enabled (backward compatibility).
  RuntimeFeatureFlags(int argc, const char** argv);

  /// @brief Check if a specific runtime feature is enabled
  /// @param feature The runtime feature to check
  /// @return True if feature is enabled, false otherwise
  bool isEnabled(RuntimeFeature feature) const;

  /// @brief Get list of all enabled features
  /// @return Vector of enabled RuntimeFeature values
  ///
  /// Useful for iterating over enabled features to generate code.
  std::vector<RuntimeFeature> getEnabledFeatures() const;

  /// @brief Get estimated size of a runtime module in bytes
  /// @param feature The runtime feature to get size for
  /// @return Estimated size in bytes
  ///
  /// Returns approximate size of the runtime code for this feature.
  /// Used for documentation and size impact analysis.
  size_t getModuleSize(RuntimeFeature feature) const;

  /// @brief Get total size of all enabled modules
  /// @return Sum of enabled module sizes in bytes
  size_t getTotalEnabledSize() const;

  /// @brief Generate preprocessor defines for enabled features
  /// @return C preprocessor #define statements
  ///
  /// Generates:
  ///   #define CPPTOC_RUNTIME_EXCEPTIONS
  ///   #define CPPTOC_RUNTIME_RTTI
  ///   etc.
  ///
  /// These defines can be used in runtime code to conditionally compile features.
  std::string generatePreprocessorDefines() const;

  /// @brief Generate size impact documentation
  /// @return Markdown table of module sizes
  ///
  /// Generates a table showing:
  ///   | Feature     | Size (bytes) | Enabled |
  ///   |-------------|--------------|---------|
  ///   | Exceptions  | 800-1200     | Yes     |
  ///   | ...         | ...          | ...     |
  std::string generateSizeDocumentation() const;

private:
  /// @brief Parse --runtime flag value
  /// @param value The flag value (e.g., "exceptions,rtti" or "all")
  /// @throws std::invalid_argument if unknown feature name
  void parseRuntimeFlag(const std::string& value);

  /// @brief Parse single feature name
  /// @param name Feature name (case-insensitive)
  /// @return RuntimeFeature enum value
  /// @throws std::invalid_argument if unknown feature name
  RuntimeFeature parseFeatureName(const std::string& name) const;

  /// @brief Convert RuntimeFeature to string name
  /// @param feature The feature to convert
  /// @return Lowercase feature name (e.g., "exceptions")
  std::string featureToString(RuntimeFeature feature) const;

  /// @brief Convert string to lowercase
  /// @param str Input string
  /// @return Lowercase version
  std::string toLower(const std::string& str) const;
};

#endif // __RUNTIME_FEATURE_FLAGS_H__

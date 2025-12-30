#pragma once

#include "pipeline/PipelineConfig.h"
#include <range/v3/all.hpp>
#include <filesystem>
#include <string>
#include <vector>

namespace cpptoc {
namespace pipeline {

namespace fs = std::filesystem;

/// File discovery iterator using generator pattern for lazy evaluation
///
/// Discovers C++ source files (.cpp, .cxx, .cc) lazily - files are discovered
/// only when requested via next(). This avoids loading all file paths into memory.
///
/// **Strategy Pattern:**
/// Uses Strategy pattern for file filtering (extension, directory exclusion).
/// Different filtering strategies can be composed.
///
/// **IMPORTANT:** True lazy evaluation - files discovered on demand, not upfront.
/// This is critical for large codebases to avoid memory overhead.
///
/// Example:
/// ```cpp
/// FileIterator it(config);
/// while (auto filePath = it.next()) {
///   // Process *filePath (lazy - only one file path in memory at a time)
/// }
/// ```
class FileIterator {
public:
  /// Construct file iterator from pipeline configuration
  ///
  /// Sets up iteration but does NOT discover files yet (lazy).
  explicit FileIterator(const PipelineConfig& config);

  /// Get next file path (generator pattern)
  ///
  /// Returns the next C++ source file path that matches criteria.
  /// Files are discovered lazily - only when next() is called.
  ///
  /// @return Next file path, or std::nullopt if no more files
  std::optional<std::string> next();

  /// Reset iterator to beginning
  ///
  /// Allows re-iteration over the same set of files.
  void reset();

private:
  const PipelineConfig& config_;

  // For explicit file list mode
  size_t currentIndex_;

  // For directory scanning mode
  std::unique_ptr<fs::recursive_directory_iterator> dirIterator_;
  bool usingExplicitFiles_;
  bool exhausted_;

  /// Initialize directory iterator
  void initializeDirectoryIterator();

  /// Advance to next valid file
  std::optional<std::string> advanceToNextFile();

  /// Check if file has valid C++ source extension
  static bool isCppSourceFile(const fs::path& path);

  /// Check if directory should be excluded from discovery
  static bool shouldExcludeDirectory(const std::string& dirName);
};

}} // namespace cpptoc::pipeline

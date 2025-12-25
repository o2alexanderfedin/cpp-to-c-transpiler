#ifndef FILE_ORIGIN_TRACKER_H
#define FILE_ORIGIN_TRACKER_H

#include "clang/AST/Decl.h"
#include "clang/Basic/SourceManager.h"
#include <string>
#include <set>
#include <unordered_map>
#include <memory>

namespace cpptoc {

/// @brief Tracks which declarations originate from which source files
///
/// SOLID Principles:
/// - Single Responsibility: Only tracks file origins for declarations
/// - Open/Closed: Extensible via file classification strategies
/// - Dependency Inversion: Depends on Clang SourceManager abstraction
///
/// Purpose: Enable multi-file transpilation by distinguishing:
/// 1. User headers (should be transpiled)
/// 2. System headers (should be skipped: /usr/include, /Library, etc.)
/// 3. Third-party headers (configurable: skip or transpile)
/// 4. Main source files (always transpiled)
///
/// This replaces the 12 isInMainFile() checks with intelligent filtering.
///
/// @example
/// @code
/// FileOriginTracker tracker(SM);
/// tracker.addUserHeaderPath("include/");
/// tracker.recordDeclaration(myClassDecl);
/// if (tracker.shouldTranspile(myClassDecl)) {
///   // Generate C code for this declaration
/// }
/// @endcode
class FileOriginTracker {
public:
  /// File categories for classification
  enum class FileCategory {
    MainFile,        ///< The primary input file being transpiled
    UserHeader,      ///< User-defined headers (should be transpiled)
    SystemHeader,    ///< System headers (skip: /usr/include, /Library, etc.)
    ThirdPartyHeader ///< Third-party libraries (configurable)
  };

  /// @brief Constructor
  /// @param SM Source manager for location queries
  explicit FileOriginTracker(clang::SourceManager &SM);

  /// @brief Record a declaration's origin file
  /// @param D Declaration to track (can be null - will be ignored safely)
  ///
  /// Stores the declaration in three data structures:
  /// 1. declToFile: Maps declaration to absolute file path
  /// 2. fileCategories: Caches file classification
  /// 3. fileToDecls: Maps file path to set of declarations
  ///
  /// Time Complexity: O(1) average case (hash map operations)
  /// Space Complexity: O(1) per declaration
  void recordDeclaration(const clang::Decl *D);

  /// @brief Check if declaration is from main file
  /// @param D Declaration to check
  /// @return true if from main file, false otherwise (including null)
  ///
  /// Time Complexity: O(1) - hash map lookup
  bool isFromMainFile(const clang::Decl *D) const;

  /// @brief Check if declaration is from a user header
  /// @param D Declaration to check
  /// @return true if from user header, false otherwise (including null)
  ///
  /// User headers are determined by:
  /// 1. Files in directories added via addUserHeaderPath()
  /// 2. Files in project directory (heuristic fallback)
  ///
  /// Time Complexity: O(1) - hash map lookup
  bool isFromUserHeader(const clang::Decl *D) const;

  /// @brief Check if declaration is from a system header
  /// @param D Declaration to check
  /// @return true if from system header, false otherwise (including null)
  ///
  /// System headers are detected by checking paths:
  /// - /usr/include/*
  /// - /Library/Developer/*
  /// - /System/Library/*
  /// - Or using Clang's SourceManager::isInSystemHeader()
  ///
  /// Time Complexity: O(1) - hash map lookup + cached classification
  bool isFromSystemHeader(const clang::Decl *D) const;

  /// @brief Check if declaration should be transpiled
  /// @param D Declaration to check
  /// @return true if should transpile (main file or user header), false otherwise
  ///
  /// This is the primary API to replace isInMainFile() checks:
  /// OLD: if (!SM.isInMainFile(D->getLocation())) return true;
  /// NEW: if (!tracker.shouldTranspile(D)) return true;
  ///
  /// Transpilation Policy:
  /// - MainFile: Always transpile
  /// - UserHeader: Always transpile
  /// - ThirdPartyHeader: Configurable (default: skip)
  /// - SystemHeader: Never transpile
  ///
  /// Time Complexity: O(1)
  bool shouldTranspile(const clang::Decl *D) const;

  /// @brief Get origin file path for a declaration
  /// @param D Declaration to query
  /// @return Absolute file path, or empty string if not tracked or null
  ///
  /// Time Complexity: O(1) - hash map lookup
  std::string getOriginFile(const clang::Decl *D) const;

  /// @brief Get file category for a declaration
  /// @param D Declaration to query
  /// @return File category (MainFile, UserHeader, SystemHeader, ThirdPartyHeader)
  ///
  /// If declaration is not tracked, returns SystemHeader as safe default
  /// (skip unknown files to avoid transpiling system code)
  ///
  /// Time Complexity: O(1) - hash map lookup
  FileCategory getFileCategory(const clang::Decl *D) const;

  /// @brief Get all user header files encountered
  /// @return Set of absolute paths to user headers
  ///
  /// Used for multi-file output generation. Each user header will be
  /// transpiled to a separate .h/.c pair.
  ///
  /// Time Complexity: O(n) where n = number of unique files
  std::set<std::string> getUserHeaderFiles() const;

  /// @brief Get all declarations from a specific file
  /// @param filepath Absolute file path
  /// @return Set of declarations from that file
  ///
  /// Used to route declarations to correct output files during code generation.
  ///
  /// Time Complexity: O(1) - hash map lookup
  std::set<const clang::Decl *> getDeclarationsFromFile(const std::string &filepath) const;

  /// @brief Add a directory to user header search paths
  /// @param dir Directory containing user headers (e.g., "include/", "src/")
  ///
  /// Any file under this directory will be classified as UserHeader.
  /// Paths can be relative or absolute.
  ///
  /// @example
  /// @code
  /// tracker.addUserHeaderPath("/Users/project/include");
  /// tracker.addUserHeaderPath("src/");  // Relative path
  /// @endcode
  void addUserHeaderPath(const std::string &dir);

  /// @brief Add a directory to third-party header search paths
  /// @param dir Directory containing third-party headers (e.g., "third_party/", "external/")
  ///
  /// Files under this directory will be classified as ThirdPartyHeader.
  /// Transpilation policy controlled by setTranspileThirdParty().
  void addThirdPartyPath(const std::string &dir);

  /// @brief Set whether to transpile third-party headers
  /// @param transpile If true, treat third-party headers as user headers
  ///
  /// Default: false (skip third-party headers)
  /// When true: Third-party headers are transpiled like user headers
  void setTranspileThirdParty(bool transpile);

  /// @brief Get statistics for debugging and performance monitoring
  struct Statistics {
    size_t totalDeclarations;           ///< Total declarations recorded
    size_t mainFileDeclarations;        ///< Declarations from main file
    size_t userHeaderDeclarations;      ///< Declarations from user headers
    size_t systemHeaderDeclarations;    ///< Declarations from system headers
    size_t thirdPartyHeaderDeclarations;///< Declarations from third-party headers
    size_t uniqueFiles;                 ///< Number of unique source files
  };

  /// @brief Get current statistics
  /// @return Statistics structure with current counts
  ///
  /// Used for:
  /// - Performance monitoring (memory overhead = totalDeclarations * ~58 bytes)
  /// - Debugging file classification
  /// - Progress reporting during transpilation
  Statistics getStatistics() const;

private:
  clang::SourceManager &SM; ///< Source manager reference

  // Core tracking data structures
  // Memory overhead: ~58 bytes per declaration (8-byte pointer + 50-byte string avg)
  // For 10,000 declarations: ~1.74 MB total
  std::unordered_map<const clang::Decl *, std::string> declToFile;
  std::unordered_map<std::string, FileCategory> fileCategories;
  std::unordered_map<std::string, std::set<const clang::Decl *>> fileToDecls;

  // Configuration
  std::set<std::string> userHeaderPaths;    ///< User header directories
  std::set<std::string> thirdPartyPaths;    ///< Third-party directories
  bool transpileThirdParty = false;         ///< Whether to transpile third-party code

  /// @brief Get absolute file path for a declaration
  /// @param D Declaration to query
  /// @return Absolute file path, or empty string if invalid
  ///
  /// Helper method that handles:
  /// - Invalid source locations
  /// - Macro expansions (uses spelling location)
  /// - File ID to path conversion
  std::string getFilePath(const clang::Decl *D) const;

  /// @brief Classify a file into one of four categories
  /// @param filepath Absolute file path
  /// @return File category
  ///
  /// Classification algorithm (in priority order):
  /// 1. If main file ID → MainFile
  /// 2. If in system path → SystemHeader
  /// 3. If in user path → UserHeader
  /// 4. If in third-party path → ThirdPartyHeader
  /// 5. Heuristic: If in project directory → UserHeader, else SystemHeader
  ///
  /// Results are cached in fileCategories map.
  FileCategory classifyFile(const std::string &filepath) const;

  /// @brief Check if path is a system header location
  /// @param filepath Absolute file path
  /// @return true if system header
  ///
  /// System paths (macOS):
  /// - /usr/include/*
  /// - /Library/Developer/*
  /// - /System/Library/*
  /// - /Applications/Xcode.app/Contents/Developer/*
  ///
  /// Also checks Clang's SourceManager::isInSystemHeader() for robustness.
  bool isSystemPath(const std::string &filepath) const;

  /// @brief Check if path is in user header directories
  /// @param filepath Absolute file path
  /// @return true if matches user header path prefix
  ///
  /// Checks if filepath starts with any path in userHeaderPaths.
  bool isUserPath(const std::string &filepath) const;

  /// @brief Check if path is in third-party directories
  /// @param filepath Absolute file path
  /// @return true if matches third-party path prefix
  ///
  /// Checks if filepath starts with any path in thirdPartyPaths.
  bool isThirdPartyPath(const std::string &filepath) const;
};

} // namespace cpptoc

#endif // FILE_ORIGIN_TRACKER_H

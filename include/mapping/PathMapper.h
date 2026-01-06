#ifndef PATHMAPPER_H
#define PATHMAPPER_H

#include "TargetContext.h"
#include "clang/AST/Decl.h"
#include "clang/Basic/SourceManager.h"
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace cpptoc {

/**
 * @brief Maps source file paths to target (C output) file paths and manages C AST translation units
 *
 * The transpiler processes multiple C++ source files and generates corresponding C output files.
 * This class manages the mapping between input source files and output C files, ensuring that:
 * - Each source file maps to exactly one output location
 * - Each translation unit (C_TU) corresponds to one source file
 * - Declarations are properly associated with their target output files
 *
 * **Single Responsibility**: Map source file paths to target paths and manage C_TU instances
 *
 * **Architecture Integration**:
 * - Works with TargetContext to create and access shared C_TranslationUnit instances
 * - Works with SourceManager to resolve actual file paths
 * - Manages the fileToTU map: source file → C_TranslationUnit
 * - Manages the declToTarget map: declaration → output file path
 *
 * **Usage Example**:
 * ```cpp
 * PathMapper mapper(targetCtx, sourceManager, "/src", "/output");
 *
 * // Map a source file to its output location
 * std::string targetPath = mapper.mapSourceToTarget("/src/Point.cpp");
 * // Returns: "/output/Point_transpiled.c"
 *
 * // Get or create translation unit for a file
 * clang::TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);
 *
 * // Register where a declaration will be output
 * mapper.registerDeclaration(classDecl, "/output/Point_transpiled.c");
 *
 * // Find where a declaration should be output
 * std::string outputFile = mapper.getTargetPathForDecl(methodDecl);
 *
 * // Get all generated output files
 * std::vector<std::string> files = mapper.getAllTargetFiles();
 * ```
 *
 * **Path Mapping Rules**:
 * - Source: `/src/Point.cpp` → Target: `/output/Point_transpiled.c`
 * - Source: `/src/include/Point.h` → Target: `/output/include/Point_transpiled.h`
 * - Preserves directory structure: source subtree appears in output subtree
 * - Adds `_transpiled` suffix before file extension
 */
class PathMapper {
public:
  /**
   * @brief Public constructor for RAII pattern
   * @param sourceDir Source root directory (e.g., "/src")
   * @param outputDir Output root directory (e.g., "/output")
   *
   * **RAII Pattern**: Each test creates its own PathMapper instance
   * **Thread Safety**: Each thread/test has isolated instance - fully thread-safe
   * **Lifetime**: Automatically cleaned up when object goes out of scope
   *
   * Example:
   * ```cpp
   * auto pathMapper = std::make_unique<PathMapper>("/src", "/output");
   * // Use pathMapper...
   * // Automatic cleanup when unique_ptr goes out of scope
   * ```
   */
  PathMapper(const std::string& sourceDir, const std::string& outputDir);

  // Prevent copying (use move semantics or unique_ptr instead)
  PathMapper(const PathMapper&) = delete;
  PathMapper& operator=(const PathMapper&) = delete;

  // Allow move semantics for modern C++
  PathMapper(PathMapper&&) = default;
  PathMapper& operator=(PathMapper&&) = default;

  /**
   * @brief Map a source file path to its target output path
   * @param sourcePath Absolute path to source file (e.g., "/src/Point.cpp")
   * @return Output path (e.g., "/output/Point_transpiled.c")
   *
   * **Mapping Rules**:
   * - Strips sourceDir prefix from sourcePath
   * - Adds outputDir prefix to result
   * - Replaces .cpp/.h with _transpiled.c/_transpiled.h
   * - Preserves intermediate directories
   *
   * **Examples**:
   * - `/src/Point.cpp` → `/output/Point_transpiled.c`
   * - `/src/include/types.h` → `/output/include/types_transpiled.h`
   * - `/src/data/parser/tokens.cpp` → `/output/data/parser/tokens_transpiled.c`
   *
   * **Idempotent**: Calling multiple times with same input returns same output
   */
  std::string mapSourceToTarget(const std::string& sourcePath);

  /**
   * @brief Get or create a C TranslationUnit for a target output file
   * @param targetPath Output file path (typically from mapSourceToTarget)
   * @return Pointer to TranslationUnitDecl in shared TargetContext
   *
   * **Behavior**:
   * - If target file already has a C_TU: returns existing C_TU
   * - If target file is new: creates new C_TU in shared TargetContext and caches it
   *
   * **Guarantees**:
   * - Always returns a valid, non-null TranslationUnitDecl
   * - Multiple calls with same targetPath return same C_TU instance
   * - All C_TU instances are created in the shared TargetContext
   *
   * **Typical Usage**:
   * ```cpp
   * std::string target = mapper.mapSourceToTarget(sourcePath);
   * clang::TranslationUnitDecl* cTU = mapper.getOrCreateTU(target);
   * // Now add C AST nodes to this C_TU
   * ```
   */
  clang::TranslationUnitDecl* getOrCreateTU(const std::string& targetPath);

  /**
   * @brief Register a declaration and its target output file
   * @param decl Clang Decl pointer from source C++ AST
   * @param targetPath Output file path where this declaration's C code will be emitted
   *
   * **Purpose**: Track which output file should contain the C code for a given declaration
   *
   * **Usage**:
   * ```cpp
   * if (auto classDecl = dyn_cast<CXXRecordDecl>(D)) {
   *   std::string target = mapper.mapSourceToTarget(sourceFile);
   *   mapper.registerDeclaration(classDecl, target);
   * }
   * ```
   *
   * **Thread Safety**: Not thread-safe; intended for single-threaded transpilation phase
   */
  void registerDeclaration(const clang::Decl* decl, const std::string& targetPath);

  /**
   * @brief Get the target output file path for a declaration
   * @param decl Clang Decl pointer from source C++ AST
   * @return Output file path where C code for this declaration should be emitted
   *         Returns empty string if declaration not registered
   *
   * **Typical Usage**:
   * ```cpp
   * std::string targetFile = mapper.getTargetPathForDecl(methodDecl);
   * if (!targetFile.empty()) {
   *   // Emit method's C code to targetFile
   * }
   * ```
   *
   * **Note**: Only returns paths for declarations explicitly registered with registerDeclaration()
   */
  std::string getTargetPathForDecl(const clang::Decl* decl) const;

  /**
   * @brief Get all target output files that have been mapped or registered
   * @return Vector of absolute paths to all target files (e.g., ["/output/Point_transpiled.c", ...])
   *
   * **Contents**: Includes all files mentioned in either:
   * - mapSourceToTarget() calls
   * - getOrCreateTU() calls
   * - registerDeclaration() calls
   *
   * **Usage**:
   * ```cpp
   * std::vector<std::string> outputFiles = mapper.getAllTargetFiles();
   * for (const auto& file : outputFiles) {
   *   generateCCodeForFile(file);
   * }
   * ```
   *
   * **Ordering**: Results may be in arbitrary order; use std::sort if order matters
   */
  std::vector<std::string> getAllTargetFiles() const;

  /**
   * @brief Set output file location for a C AST node (Phase 1.2)
   * @param node C AST node
   * @param location Output file path
   *
   * Delegates to TargetContext for centralized node tracking
   */
  void setNodeLocation(const clang::Decl* node, const std::string& location);

  /**
   * @brief Get output file location for a C AST node (Phase 1.2)
   * @param node C AST node
   * @return Output file path, or empty string if not set
   *
   * Delegates to TargetContext for centralized node tracking
   */
  std::string getNodeLocation(const clang::Decl* node) const;

  /**
   * @brief Get all C AST nodes that belong to a specific output file (Phase 1.2)
   * @param file Output file path
   * @return Vector of C AST node pointers for this file
   *
   * Used for file-based emission: get all nodes to emit to a specific .h or .c file
   */
  std::vector<const clang::Decl*> getAllNodesForFile(const std::string& file) const;

  // Note: reset() method removed - no longer needed with RAII pattern
  // Each test gets its own instance which is automatically cleaned up

private:
  // Core references (not owned)
  TargetContext& targetCtx_;           ///< Shared target context for C AST creation

  // Path configuration
  std::string sourceDir_; ///< Source root directory (e.g., "/src")
  std::string outputDir_; ///< Output root directory (e.g., "/output")

  // Caches
  std::map<std::string, clang::TranslationUnitDecl*> fileToTU_;
  ///< Maps target file paths to their C_TranslationUnit instances
  ///< Example: "/output/Point_transpiled.c" → C_TU pointer

  std::map<const clang::Decl*, std::string> declToTarget_;
  ///< Maps declarations (from source C++ AST) to their target output files
  ///< Example: CXXRecordDecl pointer → "/output/Point_transpiled.c"

  /**
   * @brief Helper: Normalize a path (remove redundant separators, resolve . and ..)
   * @param path Path to normalize
   * @return Normalized path
   *
   * Used internally to ensure consistent path representation across the class
   */
  std::string normalizePath(const std::string& path) const;

  /**
   * @brief Helper: Calculate transpiled filename from source filename
   * @param sourcePath Source file path (e.g., "/src/Point.cpp")
   * @return Transpiled filename (e.g., "Point_transpiled.c")
   *
   * Rules:
   * - Extracts filename from sourcePath
   * - Replaces .cpp/.h extension with _transpiled.c/_transpiled.h
   * - Does not include directory components
   */
  std::string getTranspiledFilename(const std::string& sourcePath) const;

  /**
   * @brief Helper: Get relative path within source directory
   * @param absolutePath Absolute path to file
   * @return Path relative to sourceDir, or original path if not under sourceDir
   *
   * Example:
   * - sourceDir = "/src", absolutePath = "/src/Point.cpp" → "Point.cpp"
   * - sourceDir = "/src", absolutePath = "/src/sub/Point.cpp" → "sub/Point.cpp"
   */
  std::string getRelativeSourcePath(const std::string& absolutePath) const;
};

} // namespace cpptoc

#endif // PATHMAPPER_H

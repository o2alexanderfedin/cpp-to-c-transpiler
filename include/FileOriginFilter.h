#ifndef FILEORIGINFILTER_H
#define FILEORIGINFILTER_H

#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "FileOriginTracker.h"

namespace cpptoc {

/**
 * @brief Filters AST nodes to determine which belong to the current source file
 *
 * When ClangTool processes multiple source files, it creates ONE AST containing
 * declarations and definitions from ALL files. This filter ensures we only process
 * nodes that belong to the current file being transpiled.
 *
 * **Single Responsibility**: Determine node origin and filter appropriately
 *
 * **Key Decisions**:
 * - For declarations: Check file location
 * - For definitions: Check where the body is defined
 * - For templates: Check instantiation location
 *
 * **Usage**:
 * ```cpp
 * FileOriginFilter filter(tracker, "main.cpp");
 * if (!filter.shouldProcess(methodDecl)) {
 *   return true; // Skip this node
 * }
 * ```
 */
class FileOriginFilter {
public:
  /**
   * @brief Construct filter for a specific source file
   * @param tracker FileOriginTracker from the visitor
   * @param currentFile Name of file currently being processed
   */
  FileOriginFilter(FileOriginTracker& tracker, const std::string& currentFile);

  /**
   * @brief Check if a declaration should be processed for current file
   * @param D Declaration to check
   * @return true if should process, false if should skip
   *
   * Rules:
   * - Process if declared in current file
   * - Process if defined in current file (for methods with bodies)
   * - Skip if belongs to another source file
   * - Always process implicit/compiler-generated if needed by current file
   */
  bool shouldProcess(const clang::Decl* D) const;

  /**
   * @brief Check if a method should be processed for current file
   * @param MD Method declaration to check
   * @return true if should process, false if should skip
   *
   * Special handling for methods:
   * - Declaration in .h: process if .h is included by current file
   * - Definition in .cpp: process ONLY if definition is in current .cpp
   * - This ensures method bodies end up in the correct translation unit
   */
  bool shouldProcessMethod(const clang::CXXMethodDecl* MD) const;

  /**
   * @brief Check if an enum should be processed for current file
   * @param ED Enum declaration to check
   * @return true if should process, false if should skip
   */
  bool shouldProcessEnum(const clang::EnumDecl* ED) const;

  /**
   * @brief Check if a class should be processed for current file
   * @param RD Record (class/struct) declaration to check
   * @return true if should process, false if should skip
   */
  bool shouldProcessClass(const clang::CXXRecordDecl* RD) const;

private:
  FileOriginTracker& tracker_;
  std::string currentFile_;

  /**
   * @brief Get the file where a declaration's definition is located
   * @param D Declaration
   * @return File path of definition, or empty if no definition
   */
  std::string getDefinitionFile(const clang::Decl* D) const;
};

} // namespace cpptoc

#endif // FILEORIGINFILTER_H

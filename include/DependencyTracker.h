#ifndef DEPENDENCYTRACKER_H
#define DEPENDENCYTRACKER_H

#include <map>
#include <set>
#include <string>
#include <vector>

namespace cpptoc {

/**
 * @brief Tracks dependencies between output files for include generation (Phase 1.3)
 *
 * When transpiling C++ to C, we need to track which files depend on which others
 * to generate correct #include directives. For example:
 * - If main.c uses struct Point, main.c should #include "Point.h"
 * - If Entity.c uses enum GameState, Entity.c should #include "GameState.h"
 *
 * **Single Responsibility**: Track file-to-file dependencies
 *
 * **Usage Example**:
 * ```cpp
 * DependencyTracker tracker;
 *
 * // Record that main.c depends on Point.h
 * tracker.addDependency("/output/main.c", "/output/Point.h");
 *
 * // Get all dependencies for main.c
 * std::vector<std::string> deps = tracker.getDependenciesForFile("/output/main.c");
 * // deps = ["/output/Point.h"]
 * ```
 *
 * **Architecture Integration**:
 * - Works with PathMapper to resolve file paths
 * - Works with CodeGenerator to emit #include directives
 * - Automatically deduplicates dependencies (uses std::set internally)
 */
class DependencyTracker {
public:
  /**
   * @brief Construct a DependencyTracker instance
   */
  DependencyTracker() = default;

  /**
   * @brief Add a dependency between two files
   * @param file Output file that has the dependency (e.g., "/output/main.c")
   * @param dependency Output file that is depended upon (e.g., "/output/Point.h")
   *
   * **Idempotent**: Adding same dependency multiple times has no effect
   * **Automatic Deduplication**: Uses std::set internally, so duplicates are ignored
   *
   * **Example**:
   * ```cpp
   * // main.c uses Point struct, so it needs Point.h
   * tracker.addDependency("/output/main.c", "/output/Point.h");
   * ```
   */
  void addDependency(const std::string& file, const std::string& dependency);

  /**
   * @brief Get all dependencies for a specific file
   * @param file Output file path (e.g., "/output/main.c")
   * @return Vector of dependency file paths (e.g., ["/output/Point.h", "/output/Entity.h"])
   *
   * **Ordering**: Results are sorted alphabetically for deterministic output
   *
   * **Example**:
   * ```cpp
   * std::vector<std::string> deps = tracker.getDependenciesForFile("/output/main.c");
   * for (const auto& dep : deps) {
   *   emit("#include \"" + extractFilename(dep) + "\"\n");
   * }
   * ```
   */
  std::vector<std::string> getDependenciesForFile(const std::string& file) const;

  /**
   * @brief Clear all dependencies for a specific file
   * @param file Output file path
   *
   * Used for testing or re-transpilation scenarios
   */
  void clearDependenciesForFile(const std::string& file);

  /**
   * @brief Clear all tracked dependencies
   *
   * Used for testing or full re-transpilation
   */
  void clearAll();

private:
  // Maps: output file -> set of files it depends on
  // Example: "/output/main.c" -> {"/output/Point.h", "/output/Entity.h"}
  std::map<std::string, std::set<std::string>> fileDependencies_;
};

} // namespace cpptoc

#endif // DEPENDENCYTRACKER_H

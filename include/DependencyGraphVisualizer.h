#ifndef DEPENDENCY_GRAPH_VISUALIZER_H
#define DEPENDENCY_GRAPH_VISUALIZER_H

#include <string>
#include <map>
#include <set>
#include <vector>

/// @brief Visualizes dependency graphs for multi-file C projects in DOT format
///
/// SOLID Principles:
/// - Single Responsibility: Only handles dependency graph visualization
/// - Open/Closed: Extensible for different output formats
/// - Liskov Substitution: Can be extended for different graph types
/// - Interface Segregation: Minimal, focused interface
/// - Dependency Inversion: Depends on abstractions (string-based file tracking)
///
/// This class analyzes include dependencies across generated .h and .c files,
/// detects circular dependencies, tracks forward declarations, and outputs
/// the dependency graph in DOT (Graphviz) format for easy visualization.
///
/// Usage:
/// 1. Create DependencyGraphVisualizer instance
/// 2. Add files and their dependencies via addFile()
/// 3. Add forward declarations via addForwardDeclaration()
/// 4. Generate DOT output via generateDOT()
/// 5. Write to file via writeToFile()
class DependencyGraphVisualizer {
public:
    /// @brief Constructor
    DependencyGraphVisualizer();

    /// @brief Add a file and its include dependencies
    /// @param filename The file being analyzed (e.g., "Point.h" or "Point.c")
    /// @param dependencies List of files this file includes
    void addFile(const std::string& filename, const std::vector<std::string>& dependencies);

    /// @brief Add a forward declaration relationship
    /// @param sourceFile File containing the forward declaration
    /// @param declaredType Type being forward declared (e.g., "struct Circle")
    void addForwardDeclaration(const std::string& sourceFile, const std::string& declaredType);

    /// @brief Detect circular dependencies in the dependency graph
    /// @return Vector of cycles, where each cycle is a vector of filenames forming the cycle
    std::vector<std::vector<std::string>> detectCircularDependencies() const;

    /// @brief Check if a specific file has any dependencies
    /// @param filename File to check
    /// @return true if file has dependencies, false otherwise
    bool hasDependencies(const std::string& filename) const;

    /// @brief Get all dependencies for a specific file
    /// @param filename File to query
    /// @return Vector of filenames this file depends on
    std::vector<std::string> getDependencies(const std::string& filename) const;

    /// @brief Get all files in the dependency graph
    /// @return Set of all filenames in the graph
    std::set<std::string> getAllFiles() const;

    /// @brief Generate DOT format output for Graphviz visualization
    /// @param graphName Name of the graph (default: "dependencies")
    /// @return String containing complete DOT format graph
    std::string generateDOT(const std::string& graphName = "dependencies") const;

    /// @brief Write DOT output to a file
    /// @param filename Output filename (e.g., "deps.dot")
    /// @return true if successful, false on error
    bool writeToFile(const std::string& filename) const;

    /// @brief Clear all dependency data (for testing/reuse)
    void clear();

private:
    /// Map of file -> list of files it depends on (includes)
    std::map<std::string, std::vector<std::string>> dependencies_;

    /// Map of file -> set of forward declarations in that file
    std::map<std::string, std::set<std::string>> forwardDecls_;

    /// @brief Helper: DFS to detect cycles from a starting node
    /// @param node Current node being visited
    /// @param visited Set of all visited nodes
    /// @param recursionStack Set of nodes in current DFS path
    /// @param currentPath Current path being explored
    /// @param cycles Output vector to store detected cycles
    void detectCyclesFromNode(
        const std::string& node,
        std::set<std::string>& visited,
        std::set<std::string>& recursionStack,
        std::vector<std::string>& currentPath,
        std::vector<std::vector<std::string>>& cycles) const;

    /// @brief Helper: Escape DOT special characters in strings
    /// @param str String to escape
    /// @return Escaped string safe for DOT format
    std::string escapeDOT(const std::string& str) const;

    /// @brief Helper: Get node style based on file type
    /// @param filename Filename to analyze
    /// @return DOT style attributes for the node
    std::string getNodeStyle(const std::string& filename) const;

    /// @brief Helper: Check if filename is a header file
    /// @param filename Filename to check
    /// @return true if header file (.h), false otherwise
    bool isHeaderFile(const std::string& filename) const;
};

#endif // DEPENDENCY_GRAPH_VISUALIZER_H

#include "DependencyGraphVisualizer.h"
#include <fstream>
#include <sstream>
#include <algorithm>

DependencyGraphVisualizer::DependencyGraphVisualizer() {
    // KISS: Simple initialization, no complex setup needed
}

void DependencyGraphVisualizer::addFile(const std::string& filename,
                                        const std::vector<std::string>& dependencies) {
    // SOLID: Single responsibility - just record the dependency relationship
    dependencies_[filename] = dependencies;
}

void DependencyGraphVisualizer::addForwardDeclaration(const std::string& sourceFile,
                                                      const std::string& declaredType) {
    // Track forward declarations for visualization
    forwardDecls_[sourceFile].insert(declaredType);
}

bool DependencyGraphVisualizer::hasDependencies(const std::string& filename) const {
    auto it = dependencies_.find(filename);
    return it != dependencies_.end() && !it->second.empty();
}

std::vector<std::string> DependencyGraphVisualizer::getDependencies(
    const std::string& filename) const {
    auto it = dependencies_.find(filename);
    if (it != dependencies_.end()) {
        return it->second;
    }
    return {};
}

std::set<std::string> DependencyGraphVisualizer::getAllFiles() const {
    std::set<std::string> files;

    // Add all files that have entries in dependencies map
    for (const auto& pair : dependencies_) {
        files.insert(pair.first);
        // Also add all their dependencies
        for (const auto& dep : pair.second) {
            files.insert(dep);
        }
    }

    return files;
}

void DependencyGraphVisualizer::detectCyclesFromNode(
    const std::string& node,
    std::set<std::string>& visited,
    std::set<std::string>& recursionStack,
    std::vector<std::string>& currentPath,
    std::vector<std::vector<std::string>>& cycles) const {

    visited.insert(node);
    recursionStack.insert(node);
    currentPath.push_back(node);

    // Visit all dependencies
    auto deps = getDependencies(node);
    for (const auto& dep : deps) {
        // If this dependency is in the recursion stack, we found a cycle
        if (recursionStack.count(dep) > 0) {
            // Extract the cycle from currentPath
            std::vector<std::string> cycle;
            bool inCycle = false;
            for (const auto& pathNode : currentPath) {
                if (pathNode == dep) {
                    inCycle = true;
                }
                if (inCycle) {
                    cycle.push_back(pathNode);
                }
            }
            cycle.push_back(dep); // Close the cycle
            cycles.push_back(cycle);
        }
        // Continue DFS if not visited
        else if (visited.count(dep) == 0) {
            detectCyclesFromNode(dep, visited, recursionStack, currentPath, cycles);
        }
    }

    // Backtrack
    recursionStack.erase(node);
    currentPath.pop_back();
}

std::vector<std::vector<std::string>> DependencyGraphVisualizer::detectCircularDependencies() const {
    std::vector<std::vector<std::string>> cycles;
    std::set<std::string> visited;
    std::set<std::string> recursionStack;

    // Run DFS from each node to find all cycles
    auto allFiles = getAllFiles();
    for (const auto& file : allFiles) {
        if (visited.count(file) == 0) {
            std::vector<std::string> currentPath;
            detectCyclesFromNode(file, visited, recursionStack, currentPath, cycles);
        }
    }

    return cycles;
}

std::string DependencyGraphVisualizer::escapeDOT(const std::string& str) const {
    // Escape special characters for DOT format
    std::string escaped;
    for (char c : str) {
        switch (c) {
            case '"':
                escaped += "\\\"";
                break;
            case '\\':
                escaped += "\\\\";
                break;
            case '\n':
                escaped += "\\n";
                break;
            default:
                escaped += c;
        }
    }
    return escaped;
}

bool DependencyGraphVisualizer::isHeaderFile(const std::string& filename) const {
    // Check if file ends with .h
    return filename.size() >= 2 &&
           filename.substr(filename.size() - 2) == ".h";
}

std::string DependencyGraphVisualizer::getNodeStyle(const std::string& filename) const {
    // Different styles for header vs implementation files
    if (isHeaderFile(filename)) {
        // Headers: rectangular, blue
        return "[shape=box,style=filled,fillcolor=lightblue]";
    } else {
        // Implementation: elliptical, green
        return "[shape=ellipse,style=filled,fillcolor=lightgreen]";
    }
}

std::string DependencyGraphVisualizer::generateDOT(const std::string& graphName) const {
    std::ostringstream dot;

    // Header
    dot << "digraph " << escapeDOT(graphName) << " {\n";
    dot << "    // Graph attributes\n";
    dot << "    rankdir=TB;\n";  // Top to bottom layout
    dot << "    node [fontname=\"Arial\"];\n";
    dot << "    edge [fontname=\"Arial\"];\n";
    dot << "\n";

    // Add legend
    dot << "    // Legend\n";
    dot << "    subgraph cluster_legend {\n";
    dot << "        label=\"Legend\";\n";
    dot << "        style=filled;\n";
    dot << "        fillcolor=lightyellow;\n";
    dot << "        \"Header File\" [shape=box,style=filled,fillcolor=lightblue];\n";
    dot << "        \"Implementation File\" [shape=ellipse,style=filled,fillcolor=lightgreen];\n";
    dot << "        \"Forward Decl\" [shape=diamond,style=filled,fillcolor=pink];\n";
    dot << "    }\n";
    dot << "\n";

    // Detect cycles for highlighting
    auto cycles = detectCircularDependencies();
    std::set<std::string> filesInCycles;
    for (const auto& cycle : cycles) {
        for (const auto& file : cycle) {
            filesInCycles.insert(file);
        }
    }

    // Add nodes
    dot << "    // Nodes (files)\n";
    auto allFiles = getAllFiles();
    for (const auto& file : allFiles) {
        dot << "    \"" << escapeDOT(file) << "\" ";

        // Use special styling for files in cycles
        if (filesInCycles.count(file) > 0) {
            dot << "[shape=box,style=\"filled,bold\",fillcolor=red,color=darkred]";
        } else {
            dot << getNodeStyle(file);
        }

        dot << ";\n";
    }
    dot << "\n";

    // Add edges (dependencies)
    dot << "    // Edges (include dependencies)\n";
    for (const auto& pair : dependencies_) {
        const std::string& source = pair.first;
        const std::vector<std::string>& deps = pair.second;

        for (const auto& target : deps) {
            dot << "    \"" << escapeDOT(source) << "\" -> \""
                << escapeDOT(target) << "\"";

            // Check if this edge is part of a cycle
            bool isInCycle = false;
            for (const auto& cycle : cycles) {
                auto sourceIt = std::find(cycle.begin(), cycle.end(), source);
                auto targetIt = std::find(cycle.begin(), cycle.end(), target);
                if (sourceIt != cycle.end() && targetIt != cycle.end()) {
                    isInCycle = true;
                    break;
                }
            }

            if (isInCycle) {
                dot << " [color=red,penwidth=2.0,label=\"CYCLE\"]";
            }

            dot << ";\n";
        }
    }
    dot << "\n";

    // Add forward declarations as special nodes
    if (!forwardDecls_.empty()) {
        dot << "    // Forward declarations\n";
        for (const auto& pair : forwardDecls_) {
            const std::string& sourceFile = pair.first;
            const std::set<std::string>& decls = pair.second;

            for (const auto& decl : decls) {
                // Create a special node for the forward declaration
                std::string declNode = "fwd_" + decl;
                dot << "    \"" << escapeDOT(declNode) << "\" "
                    << "[shape=diamond,style=filled,fillcolor=pink,label=\""
                    << escapeDOT(decl) << "\"];\n";

                // Add edge from source file to forward declaration
                dot << "    \"" << escapeDOT(sourceFile) << "\" -> \""
                    << escapeDOT(declNode) << "\" [style=dashed,label=\"forward decl\"];\n";
            }
        }
        dot << "\n";
    }

    // Footer
    dot << "}\n";

    return dot.str();
}

bool DependencyGraphVisualizer::writeToFile(const std::string& filename) const {
    // SOLID: Delegate to standard library for file I/O
    std::ofstream file(filename);
    if (!file) {
        return false;
    }

    std::string dot = generateDOT();
    file << dot;

    return file.good();
}

void DependencyGraphVisualizer::clear() {
    // KISS: Simple cleanup
    dependencies_.clear();
    forwardDecls_.clear();
}

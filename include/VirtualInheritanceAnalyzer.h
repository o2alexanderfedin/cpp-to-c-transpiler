// include/VirtualInheritanceAnalyzer.h
// Virtual inheritance detection and analysis (Story #89)
// Detects virtual bases, builds inheritance graph, identifies diamond patterns

#ifndef VIRTUAL_INHERITANCE_ANALYZER_H
#define VIRTUAL_INHERITANCE_ANALYZER_H

#include "clang/AST/DeclCXX.h"
#include <map>
#include <set>
#include <vector>
#include <string>

// Forward declarations
namespace clang {
    class CXXRecordDecl;
}

// Represents a base class relationship in the inheritance graph
struct BaseClassInfo {
    const clang::CXXRecordDecl* baseClass;
    bool isVirtual;
    clang::AccessSpecifier accessSpecifier;

    BaseClassInfo(const clang::CXXRecordDecl* base, bool virt, clang::AccessSpecifier access)
        : baseClass(base), isVirtual(virt), accessSpecifier(access) {}
};

// Represents a path in the inheritance graph
using InheritancePath = std::vector<const clang::CXXRecordDecl*>;

// Inheritance graph for tracking virtual and non-virtual inheritance relationships
class InheritanceGraph {
private:
    // Map from derived class to its base classes
    std::map<const clang::CXXRecordDecl*, std::vector<BaseClassInfo>> edges;

public:
    // Add an edge from derived to base
    void addEdge(const clang::CXXRecordDecl* derived,
                 const clang::CXXRecordDecl* base,
                 bool isVirtual,
                 clang::AccessSpecifier access);

    // Get all direct parents of a class
    std::vector<BaseClassInfo> getParents(const clang::CXXRecordDecl* cls) const;

    // Find all paths from derived to base
    std::vector<InheritancePath> findPaths(const clang::CXXRecordDecl* derived,
                                            const clang::CXXRecordDecl* base) const;

    // Check if there are multiple paths to base (diamond pattern indicator)
    bool hasMultiplePaths(const clang::CXXRecordDecl* derived,
                          const clang::CXXRecordDecl* base) const;

private:
    // Helper for DFS path finding
    void findPathsDFS(const clang::CXXRecordDecl* current,
                      const clang::CXXRecordDecl* target,
                      InheritancePath& currentPath,
                      std::vector<InheritancePath>& allPaths,
                      std::set<const clang::CXXRecordDecl*>& visited) const;
};

// Main analyzer for virtual inheritance
class VirtualInheritanceAnalyzer {
private:
    // Inheritance graph tracking all class relationships
    InheritanceGraph inheritanceGraph;

    // Map from class to its direct virtual bases
    std::map<const clang::CXXRecordDecl*, std::vector<const clang::CXXRecordDecl*>> virtualBases;

    // Map from class to all virtual bases (direct + indirect)
    std::map<const clang::CXXRecordDecl*, std::vector<const clang::CXXRecordDecl*>> allVirtualBases;

    // Classes that need VTT generation
    std::set<const clang::CXXRecordDecl*> needsVTTSet;

    // Classes that form diamond patterns
    std::set<const clang::CXXRecordDecl*> diamondPatterns;

public:
    // Analyze a class for virtual inheritance
    void analyzeClass(const clang::CXXRecordDecl* classDecl);

    // Check if class has any virtual bases (direct or indirect)
    bool hasVirtualBases(const clang::CXXRecordDecl* classDecl) const;

    // Get all virtual bases for a class (direct + indirect, deduplicated)
    std::vector<const clang::CXXRecordDecl*> getVirtualBases(const clang::CXXRecordDecl* classDecl) const;

    // Check if class needs VTT generation
    bool needsVTT(const clang::CXXRecordDecl* classDecl) const;

    // Check if class forms a diamond pattern
    bool isDiamondPattern(const clang::CXXRecordDecl* classDecl) const;

    // Get the inheritance graph
    const InheritanceGraph& getInheritanceGraph() const { return inheritanceGraph; }

    // Determine if a class is most-derived in given construction context
    // classDecl: the class whose constructor we're analyzing
    // completeObject: the most-derived class being constructed
    bool isMostDerived(const clang::CXXRecordDecl* classDecl,
                       const clang::CXXRecordDecl* completeObject) const;

    // Get construction order for virtual bases
    std::vector<const clang::CXXRecordDecl*> getVirtualBaseConstructionOrder(
        const clang::CXXRecordDecl* classDecl) const;

private:
    // Collect all virtual bases (direct + indirect) for a class
    void collectAllVirtualBases(const clang::CXXRecordDecl* classDecl,
                                std::vector<const clang::CXXRecordDecl*>& result,
                                std::set<const clang::CXXRecordDecl*>& seen) const;

    // Check if class has path to base through virtual inheritance
    bool hasVirtualPathTo(const clang::CXXRecordDecl* derived,
                          const clang::CXXRecordDecl* base) const;

    // Detect diamond patterns for a class
    void detectDiamondPattern(const clang::CXXRecordDecl* classDecl);
};

#endif // VIRTUAL_INHERITANCE_ANALYZER_H

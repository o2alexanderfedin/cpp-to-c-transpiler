// src/VirtualInheritanceAnalyzer.cpp
// Implementation of virtual inheritance detection and analysis (Story #89)

#include "VirtualInheritanceAnalyzer.h"
#include "clang/AST/DeclCXX.h"
#include <algorithm>

using namespace clang;

//=============================================================================
// InheritanceGraph Implementation
//=============================================================================

void InheritanceGraph::addEdge(const CXXRecordDecl* derived,
                                const CXXRecordDecl* base,
                                bool isVirtual,
                                AccessSpecifier access) {
    if (!derived || !base) return;

    // Check if edge already exists
    auto& parents = edges[derived];
    for (const auto& info : parents) {
        if (info.baseClass == base) {
            return; // Edge already exists
        }
    }

    parents.emplace_back(base, isVirtual, access);
}

std::vector<BaseClassInfo> InheritanceGraph::getParents(const CXXRecordDecl* cls) const {
    auto it = edges.find(cls);
    if (it != edges.end()) {
        return it->second;
    }
    return {};
}

std::vector<InheritancePath> InheritanceGraph::findPaths(
    const CXXRecordDecl* derived,
    const CXXRecordDecl* base) const {

    std::vector<InheritancePath> allPaths;
    InheritancePath currentPath;
    std::set<const CXXRecordDecl*> visited;

    findPathsDFS(derived, base, currentPath, allPaths, visited);
    return allPaths;
}

void InheritanceGraph::findPathsDFS(
    const CXXRecordDecl* current,
    const CXXRecordDecl* target,
    InheritancePath& currentPath,
    std::vector<InheritancePath>& allPaths,
    std::set<const CXXRecordDecl*>& visited) const {

    if (!current) return;

    // Add current to path
    currentPath.push_back(current);

    // Check if we reached target
    if (current == target) {
        allPaths.push_back(currentPath);
        currentPath.pop_back();
        return;
    }

    // Avoid cycles
    if (visited.count(current)) {
        currentPath.pop_back();
        return;
    }
    visited.insert(current);

    // Explore parents
    auto parents = getParents(current);
    for (const auto& info : parents) {
        findPathsDFS(info.baseClass, target, currentPath, allPaths, visited);
    }

    // Backtrack
    visited.erase(current);
    currentPath.pop_back();
}

bool InheritanceGraph::hasMultiplePaths(const CXXRecordDecl* derived,
                                         const CXXRecordDecl* base) const {
    auto paths = findPaths(derived, base);
    return paths.size() > 1;
}

//=============================================================================
// VirtualInheritanceAnalyzer Implementation
//=============================================================================

void VirtualInheritanceAnalyzer::analyzeClass(const CXXRecordDecl* classDecl) {
    if (!classDecl || !classDecl->isCompleteDefinition()) {
        return;
    }

    // Get canonical declaration
    classDecl = classDecl->getCanonicalDecl();

    // Analyze base classes
    for (const auto& base : classDecl->bases()) {
        const Type* baseType = base.getType().getTypePtr();
        if (!baseType) continue;

        const CXXRecordDecl* baseDecl = baseType->getAsCXXRecordDecl();
        if (!baseDecl) continue;

        baseDecl = baseDecl->getCanonicalDecl();

        // Add edge to inheritance graph
        inheritanceGraph.addEdge(classDecl, baseDecl,
                                  base.isVirtual(),
                                  base.getAccessSpecifier());

        // Track direct virtual bases
        if (base.isVirtual()) {
            auto& vbases = virtualBases[classDecl];
            if (std::find(vbases.begin(), vbases.end(), baseDecl) == vbases.end()) {
                vbases.push_back(baseDecl);
            }
        }
    }

    // Collect all virtual bases (direct + indirect)
    std::vector<const CXXRecordDecl*> allVBases;
    std::set<const CXXRecordDecl*> seen;
    collectAllVirtualBases(classDecl, allVBases, seen);
    allVirtualBases[classDecl] = allVBases;

    // Determine if VTT is needed
    if (!allVBases.empty()) {
        needsVTTSet.insert(classDecl);
    }

    // Detect diamond patterns
    detectDiamondPattern(classDecl);
}

bool VirtualInheritanceAnalyzer::hasVirtualBases(const CXXRecordDecl* classDecl) const {
    if (!classDecl) return false;
    classDecl = classDecl->getCanonicalDecl();

    auto it = allVirtualBases.find(classDecl);
    return it != allVirtualBases.end() && !it->second.empty();
}

std::vector<const CXXRecordDecl*> VirtualInheritanceAnalyzer::getVirtualBases(
    const CXXRecordDecl* classDecl) const {

    if (!classDecl) return {};
    classDecl = classDecl->getCanonicalDecl();

    auto it = allVirtualBases.find(classDecl);
    if (it != allVirtualBases.end()) {
        return it->second;
    }
    return {};
}

bool VirtualInheritanceAnalyzer::needsVTT(const CXXRecordDecl* classDecl) const {
    if (!classDecl) return false;
    classDecl = classDecl->getCanonicalDecl();
    return needsVTTSet.count(classDecl) > 0;
}

bool VirtualInheritanceAnalyzer::isDiamondPattern(const CXXRecordDecl* classDecl) const {
    if (!classDecl) return false;
    classDecl = classDecl->getCanonicalDecl();
    return diamondPatterns.count(classDecl) > 0;
}

bool VirtualInheritanceAnalyzer::isMostDerived(const CXXRecordDecl* classDecl,
                                                const CXXRecordDecl* completeObject) const {
    if (!classDecl || !completeObject) return false;

    classDecl = classDecl->getCanonicalDecl();
    completeObject = completeObject->getCanonicalDecl();

    // A class is most-derived if it's the complete object being constructed
    return classDecl == completeObject;
}

std::vector<const CXXRecordDecl*> VirtualInheritanceAnalyzer::getVirtualBaseConstructionOrder(
    const CXXRecordDecl* classDecl) const {

    if (!classDecl) return {};
    classDecl = classDecl->getCanonicalDecl();

    // Get all virtual bases
    auto vbases = getVirtualBases(classDecl);

    // Construction order: depth-first, left-to-right
    // This matches C++ standard construction order
    // For now, return in declaration order (simplified)
    // TODO: Implement proper DFS ordering if needed

    return vbases;
}

void VirtualInheritanceAnalyzer::collectAllVirtualBases(
    const CXXRecordDecl* classDecl,
    std::vector<const CXXRecordDecl*>& result,
    std::set<const CXXRecordDecl*>& seen) const {

    if (!classDecl) return;
    classDecl = classDecl->getCanonicalDecl();

    // Get direct virtual bases
    auto it = virtualBases.find(classDecl);
    if (it != virtualBases.end()) {
        for (const auto* vbase : it->second) {
            if (!seen.count(vbase)) {
                seen.insert(vbase);
                result.push_back(vbase);
            }
        }
    }

    // Recursively collect from non-virtual bases
    auto parents = inheritanceGraph.getParents(classDecl);
    for (const auto& info : parents) {
        if (!info.isVirtual) {
            // Non-virtual base: inherit its virtual bases
            collectAllVirtualBases(info.baseClass, result, seen);
        }
    }
}

bool VirtualInheritanceAnalyzer::hasVirtualPathTo(const CXXRecordDecl* derived,
                                                   const CXXRecordDecl* base) const {
    if (!derived || !base) return false;

    derived = derived->getCanonicalDecl();
    base = base->getCanonicalDecl();

    // Check if there's any path with at least one virtual edge
    auto paths = inheritanceGraph.findPaths(derived, base);

    for (const auto& path : paths) {
        // Check if path has virtual edge
        for (size_t i = 0; i + 1 < path.size(); ++i) {
            auto parents = inheritanceGraph.getParents(path[i]);
            for (const auto& info : parents) {
                if (info.baseClass == path[i + 1] && info.isVirtual) {
                    return true;
                }
            }
        }
    }

    return false;
}

void VirtualInheritanceAnalyzer::detectDiamondPattern(const CXXRecordDecl* classDecl) {
    if (!classDecl) return;
    classDecl = classDecl->getCanonicalDecl();

    // Check all virtual bases
    auto vbases = getVirtualBases(classDecl);
    for (const auto* vbase : vbases) {
        // If there are multiple paths to this virtual base, it's a diamond
        if (inheritanceGraph.hasMultiplePaths(classDecl, vbase)) {
            diamondPatterns.insert(classDecl);
            return;
        }
    }
}

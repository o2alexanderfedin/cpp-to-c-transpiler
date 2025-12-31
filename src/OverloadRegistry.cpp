/**
 * @file OverloadRegistry.cpp
 * @brief Implementation of global function overload registry
 *
 * Provides singleton registry for tracking function overloads across
 * translation units, enabling deterministic name mangling.
 */

#include "OverloadRegistry.h"
#include "clang/AST/Type.h"
#include <algorithm>

namespace cpptoc {

// ============================================================================
// Singleton Access
// ============================================================================

OverloadRegistry& OverloadRegistry::getInstance() {
    // C++11 magic statics - thread-safe initialization
    static OverloadRegistry instance;
    return instance;
}

// ============================================================================
// Registration
// ============================================================================

void OverloadRegistry::registerOverload(const std::string& baseName,
                                        const clang::FunctionDecl* decl,
                                        const std::string& mangledName) {
    if (!decl) {
        return; // Ignore null declarations
    }

    // Create lookup key for fast access
    auto key = std::make_pair(baseName, decl);

    // Check if already registered (duplicate registration)
    if (declToMangledName_.find(key) != declToMangledName_.end()) {
        return; // Already registered, skip
    }

    // Create overload info
    OverloadInfo info;
    info.decl = decl;
    info.mangledName = mangledName;

    // Add to overload set (automatically sorted by operator<)
    overloadSets_[baseName].insert(info);

    // Add to fast lookup map
    declToMangledName_[key] = mangledName;
}

// ============================================================================
// Queries
// ============================================================================

std::vector<std::string> OverloadRegistry::getOverloads(const std::string& baseName) const {
    std::vector<std::string> result;

    auto it = overloadSets_.find(baseName);
    if (it == overloadSets_.end()) {
        return result; // Empty vector for non-existent base name
    }

    // Extract mangled names from ordered set
    const OverloadSet& overloads = it->second;
    result.reserve(overloads.size());

    for (const auto& info : overloads) {
        result.push_back(info.mangledName);
    }

    return result;
}

int OverloadRegistry::getOverloadIndex(const std::string& baseName,
                                       const clang::FunctionDecl* decl) const {
    if (!decl) {
        return -1;
    }

    auto it = overloadSets_.find(baseName);
    if (it == overloadSets_.end()) {
        return -1; // Base name not found
    }

    const OverloadSet& overloads = it->second;

    // Find the declaration in the ordered set
    int index = 0;
    for (const auto& info : overloads) {
        if (info.decl == decl) {
            return index;
        }
        ++index;
    }

    return -1; // Declaration not found in set
}

std::string OverloadRegistry::getMangledName(const std::string& baseName,
                                             const clang::FunctionDecl* decl) const {
    if (!decl) {
        return "";
    }

    auto key = std::make_pair(baseName, decl);
    auto it = declToMangledName_.find(key);

    if (it != declToMangledName_.end()) {
        return it->second;
    }

    return ""; // Not registered
}

bool OverloadRegistry::hasMultipleOverloads(const std::string& baseName) const {
    auto it = overloadSets_.find(baseName);
    if (it == overloadSets_.end()) {
        return false; // No overloads at all
    }

    return it->second.size() > 1;
}

size_t OverloadRegistry::countOverloads(const std::string& baseName) const {
    auto it = overloadSets_.find(baseName);
    if (it == overloadSets_.end()) {
        return 0;
    }

    return it->second.size();
}

// ============================================================================
// Utility
// ============================================================================

void OverloadRegistry::reset() {
    overloadSets_.clear();
    declToMangledName_.clear();
}

// ============================================================================
// OverloadInfo Comparison (Deterministic Ordering)
// ============================================================================

bool OverloadRegistry::OverloadInfo::operator<(const OverloadInfo& other) const {
    if (!decl || !other.decl) {
        // Null pointers sort by pointer value for stability
        return decl < other.decl;
    }

    // 1. Compare parameter count (ascending)
    unsigned thisParamCount = decl->getNumParams();
    unsigned otherParamCount = other.decl->getNumParams();

    if (thisParamCount != otherParamCount) {
        return thisParamCount < otherParamCount;
    }

    // 2. Compare parameter types (lexicographic on type names)
    for (unsigned i = 0; i < thisParamCount; ++i) {
        clang::QualType thisParamType = decl->getParamDecl(i)->getType();
        clang::QualType otherParamType = other.decl->getParamDecl(i)->getType();

        std::string thisTypeName = thisParamType.getAsString();
        std::string otherTypeName = otherParamType.getAsString();

        if (thisTypeName != otherTypeName) {
            return thisTypeName < otherTypeName;
        }
    }

    // 3. Compare return types (tie-breaker)
    std::string thisReturnType = decl->getReturnType().getAsString();
    std::string otherReturnType = other.decl->getReturnType().getAsString();

    if (thisReturnType != otherReturnType) {
        return thisReturnType < otherReturnType;
    }

    // 4. Final tie-breaker: declaration pointer (for stability)
    // This ensures consistent ordering even for identical signatures
    return decl < other.decl;
}

} // namespace cpptoc

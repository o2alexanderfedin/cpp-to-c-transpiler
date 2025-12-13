#include "DependencyAnalyzer.h"

DependencyAnalyzer::DependencyAnalyzer(const std::string& ownHeaderName)
    : ownHeader(ownHeaderName) {
    // KISS: Simple initialization
}

std::vector<std::string> DependencyAnalyzer::getRequiredIncludes() const {
    std::vector<std::string> includes;

    // Own header always comes first (SOLID: consistent behavior)
    includes.push_back(ownHeader);

    // Future: Add runtime dependencies here
    // includes.insert(includes.end(), runtimeDeps.begin(), runtimeDeps.end());

    return includes;
}

std::string DependencyAnalyzer::emitIncludes() const {
    std::string result;

    auto includes = getRequiredIncludes();
    for (const auto& header : includes) {
        result += "#include \"" + header + "\"\n";
    }

    return result;
}

void DependencyAnalyzer::addRuntimeDependency(const std::string& headerName) {
    // YAGNI: Placeholder for future implementation (Phase 3+)
    // Will be used when we implement exceptions, RTTI, etc.
    runtimeDeps.push_back(headerName);
}

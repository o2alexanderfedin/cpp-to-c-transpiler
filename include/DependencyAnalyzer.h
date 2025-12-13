#ifndef DEPENDENCY_ANALYZER_H
#define DEPENDENCY_ANALYZER_H

#include <string>
#include <vector>

/// @brief Analyzes and tracks header file dependencies
///
/// SOLID: Single Responsibility - only tracks include dependencies.
/// This class determines which #include directives are needed in
/// generated .c files.
///
/// Dependency ordering:
/// 1. Own header (.h file) - always first
/// 2. Runtime library headers (future: exceptions, RTTI)
/// 3. Other dependencies (future expansion)
class DependencyAnalyzer {
public:
    /// @brief Constructor with own header name
    /// @param ownHeaderName Name of the header file this .c file corresponds to
    explicit DependencyAnalyzer(const std::string& ownHeaderName);

    /// @brief Get list of required #include files
    /// @return Vector of header filenames in correct order
    std::vector<std::string> getRequiredIncludes() const;

    /// @brief Generate #include directives as string
    /// @return String containing all #include directives with newlines
    std::string emitIncludes() const;

    /// @brief Add runtime library dependency (future-proofing)
    /// @param headerName Runtime library header name
    /// Note: Not implemented yet, reserved for Phase 3+ (exceptions, RTTI)
    void addRuntimeDependency(const std::string& headerName);

private:
    std::string ownHeader;  ///< Own header file (.h)
    std::vector<std::string> runtimeDeps;  ///< Runtime library headers (future)
};

#endif // DEPENDENCY_ANALYZER_H

#ifndef INCLUDE_GUARD_GENERATOR_H
#define INCLUDE_GUARD_GENERATOR_H

#include <string>

/// @brief Generates include guards for C header files
///
/// SOLID: Single Responsibility - only generates include guards.
/// Open/Closed: Open for extension (pragma once support) without modifying existing behavior.
///
/// This class creates either:
/// 1. Traditional #ifndef/#define/#endif guards (default)
/// 2. Modern #pragma once directive (optional)
///
/// Guard name format: FILENAME_H (uppercase, special chars → underscores)
/// Example: "my-class.h" → "MY_CLASS_H"
class IncludeGuardGenerator {
public:
    /// @brief Default constructor - uses traditional guards
    IncludeGuardGenerator();

    /// @brief Constructor with pragma once option
    /// @param usePragmaOnce If true, uses #pragma once; if false, uses traditional guards
    explicit IncludeGuardGenerator(bool usePragmaOnce);

    /// @brief Generate guard name from filename
    /// @param filename Input filename (e.g., "Point.h", "my-class.h")
    /// @return Guard name in UPPERCASE with special chars replaced by '_'
    ///
    /// Examples:
    /// - "Point.h" → "POINT_H"
    /// - "MyClass.h" → "MYCLASS_H"
    /// - "my-class.h" → "MY_CLASS_H"
    std::string generateGuardName(const std::string& filename);

    /// @brief Emit guard beginning
    /// @param guardName Name of the guard macro (ignored in pragma once mode)
    /// @return String containing either #pragma once or #ifndef/#define directives
    std::string emitGuardBegin(const std::string& guardName);

    /// @brief Emit guard ending
    /// @param guardName Name of the guard macro (for comment in traditional mode)
    /// @return String containing #endif directive in traditional mode, empty in pragma once mode
    std::string emitGuardEnd(const std::string& guardName);

    /// @brief Set whether to use #pragma once
    /// @param usePragmaOnce If true, uses #pragma once; if false, uses traditional guards
    void setUsePragmaOnce(bool usePragmaOnce);

    /// @brief Check if using #pragma once
    /// @return true if using #pragma once, false if using traditional guards
    bool isUsingPragmaOnce() const;

private:
    bool m_usePragmaOnce; ///< If true, use #pragma once; otherwise use traditional guards
};

#endif // INCLUDE_GUARD_GENERATOR_H

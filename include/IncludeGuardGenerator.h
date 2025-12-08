#ifndef INCLUDE_GUARD_GENERATOR_H
#define INCLUDE_GUARD_GENERATOR_H

#include <string>

/// @brief Generates include guards for C header files
///
/// SOLID: Single Responsibility - only generates include guards.
/// This class creates standard #ifndef/#define/#endif guards to prevent
/// multiple inclusion of header files.
///
/// Guard name format: FILENAME_H (uppercase, special chars → underscores)
/// Example: "my-class.h" → "MY_CLASS_H"
class IncludeGuardGenerator {
public:
    /// @brief Generate guard name from filename
    /// @param filename Input filename (e.g., "Point.h", "my-class.h")
    /// @return Guard name in UPPERCASE with special chars replaced by '_'
    ///
    /// Examples:
    /// - "Point.h" → "POINT_H"
    /// - "MyClass.h" → "MYCLASS_H"
    /// - "my-class.h" → "MY_CLASS_H"
    std::string generateGuardName(const std::string& filename);

    /// @brief Emit guard beginning (#ifndef and #define)
    /// @param guardName Name of the guard macro
    /// @return String containing #ifndef and #define directives
    std::string emitGuardBegin(const std::string& guardName);

    /// @brief Emit guard ending (#endif)
    /// @param guardName Name of the guard macro (for comment)
    /// @return String containing #endif directive with comment
    std::string emitGuardEnd(const std::string& guardName);
};

#endif // INCLUDE_GUARD_GENERATOR_H

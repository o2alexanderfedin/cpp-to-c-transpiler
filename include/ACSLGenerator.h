#ifndef ACSL_GENERATOR_H
#define ACSL_GENERATOR_H

// Epic #193: ACSL Annotation Generation for Transpiled Code
// Story #194: Design and implement ACSLGenerator base class
//
// SOLID Principles:
// - Single Responsibility: Only generates ACSL annotation formatting
// - Open/Closed: Open for extension (function/loop/class annotators) without modification
// - Dependency Inversion: Depends on abstractions (ACSLLevel, ACSLOutputMode)

#include <string>

/// @brief ACSL coverage level configuration
enum class ACSLLevel {
    Basic,  ///< Function contracts only (requires, ensures, assigns)
    Full    ///< Function contracts + loop invariants + class invariants
};

/// @brief ACSL output mode configuration
enum class ACSLOutputMode {
    Inline,    ///< Annotations inline in generated C code
    Separate   ///< Annotations in separate .acsl files
};

/// @brief Base class for ACSL annotation generation
///
/// Provides common formatting and configuration for ACSL annotation generation.
/// Extended by specific annotators (ACSLFunctionAnnotator, ACSLLoopAnnotator, etc.)
///
/// ACSL (ANSI/ISO C Specification Language) format: /*@ ... */
/// Reference: https://frama-c.com/html/acsl.html
class ACSLGenerator {
public:
    /// @brief Default constructor - Basic ACSL level, Inline output mode
    ACSLGenerator();

    /// @brief Constructor with ACSL level
    /// @param level ACSL coverage level (Basic or Full)
    explicit ACSLGenerator(ACSLLevel level);

    /// @brief Constructor with ACSL level and output mode
    /// @param level ACSL coverage level (Basic or Full)
    /// @param mode Output mode (Inline or Separate)
    ACSLGenerator(ACSLLevel level, ACSLOutputMode mode);

    /// @brief Virtual destructor for extensibility
    virtual ~ACSLGenerator() = default;

    /// @brief Format ACSL annotation as comment block
    /// @param annotation ACSL annotation content (without comment delimiters)
    /// @param indent Indentation level in spaces (default: 0)
    /// @return Formatted ACSL comment /*@ ... */
    ///
    /// Example:
    ///   input: "requires x > 0;"
    ///   output: "/*@ requires x > 0; */"
    std::string formatACSLComment(const std::string& annotation, unsigned indent = 0) const;

    /// @brief Get current ACSL level configuration
    /// @return Current ACSL level (Basic or Full)
    ACSLLevel getACSLLevel() const { return m_level; }

    /// @brief Get current output mode configuration
    /// @return Current output mode (Inline or Separate)
    ACSLOutputMode getOutputMode() const { return m_mode; }

    /// @brief Set ACSL level configuration
    /// @param level New ACSL level
    void setACSLLevel(ACSLLevel level) { m_level = level; }

    /// @brief Set output mode configuration
    /// @param mode New output mode
    void setOutputMode(ACSLOutputMode mode) { m_mode = mode; }

protected:
    /// @brief Apply indentation to a string
    /// @param text Text to indent
    /// @param indent Number of spaces for indentation
    /// @return Indented text
    std::string applyIndentation(const std::string& text, unsigned indent) const;

private:
    ACSLLevel m_level;        ///< ACSL coverage level configuration
    ACSLOutputMode m_mode;    ///< Output mode configuration
};

#endif // ACSL_GENERATOR_H

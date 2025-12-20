// Epic #193: ACSL Annotation Generation for Transpiled Code
// Story #194: Design and implement ACSLGenerator base class
//
// Implementation following KISS principle:
// - Simple string formatting for ACSL comments
// - Preserve backslashes for ACSL logic operators (\valid, \result, etc.)
// - Support multi-line annotations with proper formatting

#include "ACSLGenerator.h"
#include <sstream>

// Default constructor: Basic level, Inline mode
ACSLGenerator::ACSLGenerator()
    : m_level(ACSLLevel::Basic), m_mode(ACSLOutputMode::Inline) {
}

// Constructor with ACSL level
ACSLGenerator::ACSLGenerator(ACSLLevel level)
    : m_level(level), m_mode(ACSLOutputMode::Inline) {
}

// Constructor with ACSL level and output mode
ACSLGenerator::ACSLGenerator(ACSLLevel level, ACSLOutputMode mode)
    : m_level(level), m_mode(mode) {
}

// Format ACSL annotation as comment block
std::string ACSLGenerator::formatACSLComment(const std::string& annotation, unsigned indent) const {
    // Handle empty annotations
    if (annotation.empty()) {
        return "";
    }

    // Apply indentation
    std::string indentStr = std::string(indent, ' ');

    // Check if annotation contains newlines (multi-line)
    if (annotation.find('\n') != std::string::npos) {
        // Multi-line annotation: format with line breaks
        std::ostringstream oss;
        oss << indentStr << "/*@\n";

        // Split annotation by newlines and add proper indentation
        std::istringstream iss(annotation);
        std::string line;
        while (std::getline(iss, line)) {
            oss << indentStr << "  " << line << "\n";
        }

        oss << indentStr << "*/";
        return oss.str();
    } else {
        // Single-line annotation: compact format
        return indentStr + "/*@ " + annotation + " */";
    }
}

// Apply indentation to a string
std::string ACSLGenerator::applyIndentation(const std::string& text, unsigned indent) const {
    if (indent == 0) {
        return text;
    }

    std::string indentStr(indent, ' ');
    std::ostringstream oss;
    std::istringstream iss(text);
    std::string line;
    bool first = true;

    while (std::getline(iss, line)) {
        if (!first) {
            oss << "\n";
        }
        oss << indentStr << line;
        first = false;
    }

    return oss.str();
}

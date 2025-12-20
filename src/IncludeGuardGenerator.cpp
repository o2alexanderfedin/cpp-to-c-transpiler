#include "IncludeGuardGenerator.h"
#include <algorithm>
#include <cctype>

// Default constructor - uses traditional guards
IncludeGuardGenerator::IncludeGuardGenerator()
    : m_usePragmaOnce(false) {
}

// Constructor with pragma once option
IncludeGuardGenerator::IncludeGuardGenerator(bool usePragmaOnce)
    : m_usePragmaOnce(usePragmaOnce) {
}

std::string IncludeGuardGenerator::generateGuardName(const std::string& filename) {
    std::string result = filename;

    // Replace special characters with underscores
    // Keep only alphanumeric and underscore
    std::transform(result.begin(), result.end(), result.begin(),
                   [](char c) {
                       if (std::isalnum(c) || c == '_') {
                           return static_cast<char>(std::toupper(c));
                       }
                       return '_';
                   });

    return result;
}

std::string IncludeGuardGenerator::emitGuardBegin(const std::string& guardName) {
    if (m_usePragmaOnce) {
        // Modern #pragma once approach
        return "#pragma once\n";
    } else {
        // Traditional include guard approach
        // KISS: Simple string concatenation
        std::string result;
        result += "#ifndef " + guardName + "\n";
        result += "#define " + guardName + "\n";
        return result;
    }
}

std::string IncludeGuardGenerator::emitGuardEnd(const std::string& guardName) {
    if (m_usePragmaOnce) {
        // No closing needed for #pragma once
        return "";
    } else {
        // Add comment with guard name for clarity
        return "#endif // " + guardName + "\n";
    }
}

void IncludeGuardGenerator::setUsePragmaOnce(bool usePragmaOnce) {
    m_usePragmaOnce = usePragmaOnce;
}

bool IncludeGuardGenerator::isUsingPragmaOnce() const {
    return m_usePragmaOnce;
}

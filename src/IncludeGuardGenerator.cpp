#include "IncludeGuardGenerator.h"
#include <algorithm>
#include <cctype>

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
    // KISS: Simple string concatenation
    std::string result;
    result += "#ifndef " + guardName + "\n";
    result += "#define " + guardName + "\n";
    return result;
}

std::string IncludeGuardGenerator::emitGuardEnd(const std::string& guardName) {
    // Add comment with guard name for clarity
    return "#endif // " + guardName + "\n";
}

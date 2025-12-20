#ifndef STRING_FORMATTER_H
#define STRING_FORMATTER_H

#include <string>
#include <sstream>
#include <vector>
#include <map>
#include <iomanip>
#include <type_traits>
#include <stdexcept>
#include <cmath>
#include <memory>

namespace format {

// Format exception
class FormatError : public std::runtime_error {
public:
    explicit FormatError(const std::string& message)
        : std::runtime_error("Format Error: " + message) {}
};

// Forward declarations
template<typename T, typename Enable = void>
struct Formatter;

class FormatterBase;
class StringBuiler;

// Alignment options
enum class Align {
    Left,
    Right,
    Center
};

// Number base
enum class Base {
    Decimal = 10,
    Hexadecimal = 16,
    Octal = 8,
    Binary = 2
};

// Format specification
struct FormatSpec {
    Align align = Align::Left;
    int width = 0;
    int precision = 6;
    char fill = ' ';
    Base base = Base::Decimal;
    bool showBase = false;
    bool showPos = false;
    bool upperCase = false;
    bool scientific = false;

    FormatSpec() = default;
};

// Parse format specification from string like "{:>10.2f}"
inline FormatSpec parseFormatSpec(const std::string& spec) {
    FormatSpec result;

    if (spec.empty() || spec[0] != ':') {
        return result;
    }

    size_t i = 1;  // Skip ':'

    // Fill and align
    if (i + 1 < spec.size()) {
        if (spec[i + 1] == '<' || spec[i + 1] == '>' || spec[i + 1] == '^') {
            result.fill = spec[i];
            i++;
        }
    }

    // Align
    if (i < spec.size()) {
        switch (spec[i]) {
            case '<': result.align = Align::Left; i++; break;
            case '>': result.align = Align::Right; i++; break;
            case '^': result.align = Align::Center; i++; break;
        }
    }

    // Sign
    if (i < spec.size() && spec[i] == '+') {
        result.showPos = true;
        i++;
    }

    // Alternate form (0x, 0o, etc.)
    if (i < spec.size() && spec[i] == '#') {
        result.showBase = true;
        i++;
    }

    // Width
    while (i < spec.size() && std::isdigit(spec[i])) {
        result.width = result.width * 10 + (spec[i] - '0');
        i++;
    }

    // Precision
    if (i < spec.size() && spec[i] == '.') {
        i++;
        result.precision = 0;
        while (i < spec.size() && std::isdigit(spec[i])) {
            result.precision = result.precision * 10 + (spec[i] - '0');
            i++;
        }
    }

    // Type
    if (i < spec.size()) {
        switch (spec[i]) {
            case 'x': result.base = Base::Hexadecimal; result.upperCase = false; break;
            case 'X': result.base = Base::Hexadecimal; result.upperCase = true; break;
            case 'o': result.base = Base::Octal; break;
            case 'b': result.base = Base::Binary; break;
            case 'd': result.base = Base::Decimal; break;
            case 'e': result.scientific = true; result.upperCase = false; break;
            case 'E': result.scientific = true; result.upperCase = true; break;
            case 'f':
            case 'F': result.scientific = false; break;
        }
    }

    return result;
}

// Apply alignment to string
inline std::string applyAlignment(const std::string& str, const FormatSpec& spec) {
    if (spec.width <= static_cast<int>(str.length())) {
        return str;
    }

    int padding = spec.width - str.length();
    std::string result;

    switch (spec.align) {
        case Align::Left:
            result = str + std::string(padding, spec.fill);
            break;
        case Align::Right:
            result = std::string(padding, spec.fill) + str;
            break;
        case Align::Center: {
            int leftPad = padding / 2;
            int rightPad = padding - leftPad;
            result = std::string(leftPad, spec.fill) + str + std::string(rightPad, spec.fill);
            break;
        }
    }

    return result;
}

// Base formatter template
template<typename T, typename Enable>
struct Formatter {
    static std::string format(const T& value, const FormatSpec& spec) {
        std::ostringstream oss;
        oss << value;
        return applyAlignment(oss.str(), spec);
    }
};

// Specialization for integers
template<typename T>
struct Formatter<T, typename std::enable_if<std::is_integral<T>::value &&
                                             !std::is_same<T, bool>::value>::type> {
    static std::string format(const T& value, const FormatSpec& spec) {
        std::ostringstream oss;

        // Handle sign
        if (spec.showPos && value >= 0) {
            oss << '+';
        }

        // Handle base prefix
        if (spec.showBase) {
            switch (spec.base) {
                case Base::Hexadecimal:
                    oss << (spec.upperCase ? "0X" : "0x");
                    break;
                case Base::Octal:
                    oss << "0o";
                    break;
                case Base::Binary:
                    oss << "0b";
                    break;
                default:
                    break;
            }
        }

        // Convert to string in specified base
        std::string numStr;
        T absValue = value < 0 ? -value : value;

        if (absValue == 0) {
            numStr = "0";
        } else {
            while (absValue > 0) {
                int digit = absValue % static_cast<int>(spec.base);
                char c = digit < 10 ? '0' + digit : (spec.upperCase ? 'A' : 'a') + digit - 10;
                numStr = c + numStr;
                absValue /= static_cast<int>(spec.base);
            }
        }

        if (value < 0) {
            numStr = "-" + numStr;
        }

        oss << numStr;
        return applyAlignment(oss.str(), spec);
    }
};

// Specialization for floating point
template<typename T>
struct Formatter<T, typename std::enable_if<std::is_floating_point<T>::value>::type> {
    static std::string format(const T& value, const FormatSpec& spec) {
        std::ostringstream oss;

        oss << std::setprecision(spec.precision);

        if (spec.showPos && value >= 0) {
            oss << '+';
        }

        if (spec.scientific) {
            oss << std::scientific;
            if (spec.upperCase) {
                oss << std::uppercase;
            }
        } else {
            oss << std::fixed;
        }

        oss << value;
        return applyAlignment(oss.str(), spec);
    }
};

// Specialization for bool
template<>
struct Formatter<bool> {
    static std::string format(const bool& value, const FormatSpec& spec) {
        std::string str = value ? "true" : "false";
        return applyAlignment(str, spec);
    }
};

// Specialization for char (as character, not integer)
template<>
struct Formatter<char> {
    static std::string format(const char& value, const FormatSpec& spec) {
        std::string str(1, value);
        return applyAlignment(str, spec);
    }
};

// Specialization for C-strings
template<>
struct Formatter<const char*> {
    static std::string format(const char* const& value, const FormatSpec& spec) {
        std::string str(value);
        if (spec.precision > 0 && static_cast<int>(str.length()) > spec.precision) {
            str = str.substr(0, spec.precision);
        }
        return applyAlignment(str, spec);
    }
};

// Specialization for std::string
template<>
struct Formatter<std::string> {
    static std::string format(const std::string& value, const FormatSpec& spec) {
        std::string str = value;
        if (spec.precision > 0 && static_cast<int>(str.length()) > spec.precision) {
            str = str.substr(0, spec.precision);
        }
        return applyAlignment(str, spec);
    }
};

// Specialization for pointers
template<typename T>
struct Formatter<T*> {
    static std::string format(T* const& value, const FormatSpec& spec) {
        std::ostringstream oss;
        oss << "0x" << std::hex << reinterpret_cast<uintptr_t>(value);
        return applyAlignment(oss.str(), spec);
    }
};

// String builder with formatting
class StringBuilder {
private:
    std::ostringstream stream_;

public:
    StringBuilder() = default;

    // Append raw string
    StringBuilder& append(const std::string& str) {
        stream_ << str;
        return *this;
    }

    // Append formatted value
    template<typename T>
    StringBuilder& append(const T& value, const FormatSpec& spec = FormatSpec()) {
        stream_ << Formatter<T>::format(value, spec);
        return *this;
    }

    // Stream operator
    template<typename T>
    StringBuilder& operator<<(const T& value) {
        return append(value);
    }

    // Get result
    std::string str() const {
        return stream_.str();
    }

    // Clear
    void clear() {
        stream_.str("");
        stream_.clear();
    }

    // Check if empty
    bool empty() const {
        return stream_.str().empty();
    }

    // Get length
    size_t length() const {
        return stream_.str().length();
    }
};

// Format string with placeholders
template<typename... Args>
std::string formatString(const std::string& fmt, Args&&... args) {
    std::vector<std::string> formattedArgs;

    // Format each argument with default spec
    auto formatArg = [&formattedArgs](auto&& arg) {
        formattedArgs.push_back(Formatter<typename std::decay<decltype(arg)>::type>::format(
            std::forward<decltype(arg)>(arg), FormatSpec()));
    };

    // Use fold expression (C++17)
    (formatArg(std::forward<Args>(args)), ...);

    // Replace placeholders
    std::string result;
    size_t argIndex = 0;
    size_t i = 0;

    while (i < fmt.size()) {
        if (fmt[i] == '{') {
            if (i + 1 < fmt.size() && fmt[i + 1] == '{') {
                // Escaped brace
                result += '{';
                i += 2;
                continue;
            }

            // Find closing brace
            size_t closePos = fmt.find('}', i);
            if (closePos == std::string::npos) {
                throw FormatError("Unclosed placeholder");
            }

            // Extract placeholder content
            std::string placeholder = fmt.substr(i + 1, closePos - i - 1);

            // Parse index and format spec
            size_t colonPos = placeholder.find(':');
            size_t index = argIndex;

            if (colonPos == std::string::npos) {
                // No format spec, just index
                if (!placeholder.empty()) {
                    try {
                        index = std::stoul(placeholder);
                    } catch (...) {
                        throw FormatError("Invalid placeholder index");
                    }
                }
            } else {
                // Has format spec
                std::string indexStr = placeholder.substr(0, colonPos);
                if (!indexStr.empty()) {
                    try {
                        index = std::stoul(indexStr);
                    } catch (...) {
                        throw FormatError("Invalid placeholder index");
                    }
                }
            }

            if (index >= formattedArgs.size()) {
                throw FormatError("Placeholder index out of range");
            }

            result += formattedArgs[index];
            argIndex++;
            i = closePos + 1;
        } else if (fmt[i] == '}') {
            if (i + 1 < fmt.size() && fmt[i + 1] == '}') {
                // Escaped brace
                result += '}';
                i += 2;
                continue;
            } else {
                throw FormatError("Unmatched closing brace");
            }
        } else {
            result += fmt[i];
            i++;
        }
    }

    return result;
}

// Printf-style format (alternative interface)
template<typename... Args>
std::string printf(const char* fmt, Args&&... args) {
    // Convert printf format to our format string syntax
    // For simplicity, this is a basic implementation
    return formatString(fmt, std::forward<Args>(args)...);
}

// Convenience functions
template<typename T>
std::string toString(const T& value) {
    return Formatter<T>::format(value, FormatSpec());
}

template<typename T>
std::string toString(const T& value, const FormatSpec& spec) {
    return Formatter<T>::format(value, spec);
}

// Stream-style formatting
class FormatStream {
private:
    StringBuilder builder_;

public:
    FormatStream() = default;

    template<typename T>
    FormatStream& operator<<(const T& value) {
        builder_ << value;
        return *this;
    }

    std::string str() const {
        return builder_.str();
    }

    operator std::string() const {
        return str();
    }
};

// Helper for creating format specs
inline FormatSpec spec(Align align = Align::Left, int width = 0, int precision = 6) {
    FormatSpec s;
    s.align = align;
    s.width = width;
    s.precision = precision;
    return s;
}

// Specialized formatters for common types
namespace formatters {
    // Format as hex
    template<typename T>
    std::string hex(const T& value, bool uppercase = false, bool showBase = true) {
        FormatSpec spec;
        spec.base = Base::Hexadecimal;
        spec.upperCase = uppercase;
        spec.showBase = showBase;
        return Formatter<T>::format(value, spec);
    }

    // Format as octal
    template<typename T>
    std::string oct(const T& value, bool showBase = true) {
        FormatSpec spec;
        spec.base = Base::Octal;
        spec.showBase = showBase;
        return Formatter<T>::format(value, spec);
    }

    // Format as binary
    template<typename T>
    std::string bin(const T& value, bool showBase = true) {
        FormatSpec spec;
        spec.base = Base::Binary;
        spec.showBase = showBase;
        return Formatter<T>::format(value, spec);
    }

    // Format with scientific notation
    template<typename T>
    std::string scientific(const T& value, int precision = 6, bool uppercase = false) {
        FormatSpec spec;
        spec.scientific = true;
        spec.precision = precision;
        spec.upperCase = uppercase;
        return Formatter<T>::format(value, spec);
    }

    // Format with fixed-point notation
    template<typename T>
    std::string fixed(const T& value, int precision = 2) {
        FormatSpec spec;
        spec.scientific = false;
        spec.precision = precision;
        return Formatter<T>::format(value, spec);
    }

    // Pad string to width
    inline std::string pad(const std::string& str, int width, Align align = Align::Left, char fill = ' ') {
        FormatSpec spec;
        spec.width = width;
        spec.align = align;
        spec.fill = fill;
        return Formatter<std::string>::format(str, spec);
    }
} // namespace formatters

} // namespace format

#endif // STRING_FORMATTER_H

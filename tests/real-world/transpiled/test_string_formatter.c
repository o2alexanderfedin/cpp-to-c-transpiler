// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/string-formatter/tests/test_string_formatter.cpp
// Implementation file

#include "test_string_formatter.h"

namespace format {
        class FormatError {
        public:
                explicit FormatError(const int &message) {
                }
        };
        template <typename T, typename Enable = void> struct Formatter;
        class FormatterBase;
        class StringBuiler;
        enum class Align : int {
                Left,
                Right,
                Center
        };
        enum class Base : int {
                Decimal = 10,
                Hexadecimal = 16,
                Octal = 8,
                Binary = 2
        };
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
                FormatSpec() noexcept = default;        };
        inline FormatSpec parseFormatSpec(const int &spec) {
                FormatSpec result;
                if (<recovery-expr>(spec).empty() || <recovery-expr>()[0] != ':') {
                        return result;
                }
                int i = <recovery-expr>(1);
                if (<recovery-expr>(i) + 1 < <recovery-expr>().size()) {
                        if (<recovery-expr>(spec)[<recovery-expr>() + 1] == '<' || <recovery-expr>()[<recovery-expr>() + 1] == '>' || <recovery-expr>()[<recovery-expr>() + 1] == '^') {
                                result.fill = <recovery-expr>()[<recovery-expr>()];
                                <recovery-expr>(i)++;
                        }
                }
                if (<recovery-expr>() < <recovery-expr>().size()) {
                        switch (<recovery-expr>(spec)[<recovery-expr>()]) {
                              case '<':
                                result.align = Align::Left;
                                <recovery-expr>(i)++;
                                break;
                              case '>':
                                result.align = Align::Right;
                                <recovery-expr>(i)++;
                                break;
                              case '^':
                                result.align = Align::Center;
                                <recovery-expr>(i)++;
                                break;
                        }
                }
                if (<recovery-expr>() < <recovery-expr>().size() && <recovery-expr>()[<recovery-expr>()] == '+') {
                        result.showPos = true;
                        <recovery-expr>(i)++;
                }
                if (<recovery-expr>() < <recovery-expr>().size() && <recovery-expr>()[<recovery-expr>()] == '#') {
                        result.showBase = true;
                        <recovery-expr>(i)++;
                }
                while (<recovery-expr>())
                        {
                                result.width = result.width * 10 + (<recovery-expr>(spec)[<recovery-expr>()] - '0');
                                <recovery-expr>(i)++;
                        }
                if (<recovery-expr>() < <recovery-expr>().size() && <recovery-expr>()[<recovery-expr>()] == '.') {
                        <recovery-expr>(i)++;
                        result.precision = 0;
                        while (<recovery-expr>())
                                {
                                        result.precision = result.precision * 10 + (<recovery-expr>(spec)[<recovery-expr>()] - '0');
                                        <recovery-expr>(i)++;
                                }
                }
                if (<recovery-expr>() < <recovery-expr>().size()) {
                        switch (<recovery-expr>(spec)[<recovery-expr>()]) {
                              case 'x':
                                result.base = Base::Hexadecimal;
                                result.upperCase = false;
                                break;
                              case 'X':
                                result.base = Base::Hexadecimal;
                                result.upperCase = true;
                                break;
                              case 'o':
                                result.base = Base::Octal;
                                break;
                              case 'b':
                                result.base = Base::Binary;
                                break;
                              case 'd':
                                result.base = Base::Decimal;
                                break;
                              case 'e':
                                result.scientific = true;
                                result.upperCase = false;
                                break;
                              case 'E':
                                result.scientific = true;
                                result.upperCase = true;
                                break;
                              case 'f':
                              case 'F':
                                result.scientific = false;
                                break;
                        }
                }
                return result;
        }
        inline int applyAlignment(const int &str, const FormatSpec &spec) {
                if (spec.width <= static_cast<int>(<recovery-expr>().length())) {
                        return <recovery-expr>();
                }
                int padding = spec.width - <recovery-expr>().length();
                int result;
                switch (spec.align) {
                      case Align::Left:
                        ;
                        break;
                      case Align::Right:
                        ;
                        break;
                      case Align::Center:
                        {
                                int leftPad = padding / 2;
                                int rightPad = padding - leftPad;
                                break;
                        }
                }
                return <recovery-expr>();
        }
        template <typename T, typename Enable = void> struct Formatter {
                static int format(const T &value, const FormatSpec &spec) {
                        int oss;
                        <recovery-expr>(oss) << value;
                }
        };
        struct ;
        struct ;
        class StringBuilder {
        private:
                int stream_;
        public:
                StringBuilder() noexcept = default;
                StringBuilder &append(const int &str) {
                        return *this;
                }
                template <typename T> StringBuilder &append(const T &value, const FormatSpec &spec = FormatSpec()) {
                        return *this;
                }
                template <typename T> StringBuilder &operator<<(const T &value) {
                        return append(value);
                }
                int str() const {
                }
                void clear() {
                }
                bool empty() const {
                }
                int length() const {
                }
        };
        template <typename ...Args> int formatString(const int &fmt, Args &&...args) {
                auto formatArg = [](auto &&arg) {
                };
                int result;
                int argIndex = <recovery-expr>(0);
                int i = <recovery-expr>(0);
                while (<recovery-expr>() < <recovery-expr>().size())
                        {
                                if (<recovery-expr>(fmt)[<recovery-expr>()] == '{') {
                                        if (<recovery-expr>(i) + 1 < <recovery-expr>().size() && <recovery-expr>()[<recovery-expr>() + 1] == '{') {
                                                <recovery-expr>(result) += '{';
                                                <recovery-expr>(i) += 2;
                                                continue;
                                        }
                                        int closePos = <recovery-expr>(<recovery-expr>().find('}', <recovery-expr>()));
                                        if (<recovery-expr>()) {
                                                throw <recovery-expr>("Unclosed placeholder");
                                        }
                                        int placeholder = <recovery-expr>(<recovery-expr>().substr(<recovery-expr>() + 1, <recovery-expr>() - <recovery-expr>() - 1));
                                        int colonPos = <recovery-expr>(<recovery-expr>().find(':'));
                                        int index = <recovery-expr>(<recovery-expr>());
                                        if (<recovery-expr>()) {
                                                if (!<recovery-expr>().empty()) {
                                                        try {
                                                        } catch (...) {
                                                                throw <recovery-expr>("Invalid placeholder index");
                                                        }
                                                }
                                        } else {
                                                int indexStr = <recovery-expr>(<recovery-expr>().substr(0, <recovery-expr>()));
                                                if (!<recovery-expr>().empty()) {
                                                        try {
                                                        } catch (...) {
                                                                throw <recovery-expr>("Invalid placeholder index");
                                                        }
                                                }
                                        }
                                        if (<recovery-expr>()) {
                                                throw <recovery-expr>("Placeholder index out of range");
                                        }
                                        <recovery-expr>(argIndex)++;
                                        <recovery-expr>(i) = <recovery-expr>() + 1;
                                } else if (<recovery-expr>(fmt)[<recovery-expr>()] == '}') {
                                        if (<recovery-expr>(i) + 1 < <recovery-expr>().size() && <recovery-expr>()[<recovery-expr>() + 1] == '}') {
                                                <recovery-expr>(result) += '}';
                                                <recovery-expr>(i) += 2;
                                                continue;
                                        } else {
                                                throw <recovery-expr>("Unmatched closing brace");
                                        }
                                } else {
                                        <recovery-expr>(result) += <recovery-expr>()[<recovery-expr>()];
                                        <recovery-expr>(i)++;
                                }
                        }
                return <recovery-expr>();
        }
        template <typename ...Args> int printf(const char *fmt, Args &&...args) {
                return <recovery-expr>(formatString, fmt);
        }
        template <typename T> int toString(const T &value) {
        }
        template <typename T> int toString(const T &value, const FormatSpec &spec) {
        }
        class FormatStream {
        private:
                StringBuilder builder_;
        public:
                FormatStream() noexcept = default;
                template <typename T> FormatStream &operator<<(const T &value) {
                        return *this;
                }
                int str() const {
                }
        };
        inline FormatSpec spec(Align align = Align::Left, int width = 0, int precision = 6) {
                FormatSpec s;
                s.align = align;
                s.width = width;
                s.precision = precision;
                return s;
        }
        namespace formatters {
                template <typename T> int hex(const T &value, bool uppercase = false, bool showBase = true) {
                        FormatSpec spec;
                        spec.base = Base::Hexadecimal;
                        spec.upperCase = uppercase;
                        spec.showBase = showBase;
                }
                template <typename T> int oct(const T &value, bool showBase = true) {
                        FormatSpec spec;
                        spec.base = Base::Octal;
                        spec.showBase = showBase;
                }
                template <typename T> int bin(const T &value, bool showBase = true) {
                        FormatSpec spec;
                        spec.base = Base::Binary;
                        spec.showBase = showBase;
                }
                template <typename T> int scientific(const T &value, int precision = 6, bool uppercase = false) {
                        FormatSpec spec;
                        spec.scientific = true;
                        spec.precision = precision;
                        spec.upperCase = uppercase;
                }
                template <typename T> int fixed(const T &value, int precision = 2) {
                        FormatSpec spec;
                        spec.scientific = false;
                        spec.precision = precision;
                }
                inline int pad(const int &str, int width, Align align = Align::Left, char fill = ' ') {
                        FormatSpec spec;
                        spec.width = width;
                        spec.align = align;
                        spec.fill = fill;
                }
        }
}
using namespace format
int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString, 42), "42");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString, 3.1415899999999999).substr(0, 4), "3.14");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString, true), "true");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString, false), "false");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString), "hello");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString, "world"), "world");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString, 42), "42");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString, -123), "-123");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatters::hex, 255, false, true), "0xff");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatters::hex, 255, true, true), "0XFF");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatters::hex, 16, false, false), "10");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatters::oct, 64, true), "0o100");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatters::oct, 8, false), "10");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatters::bin, 5, true), "0b101");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatters::bin, 7, false), "111");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatters::fixed, 3.1415899999999999, 2), "3.14");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatters::fixed, 2.71828, 4), "2.7183");
}

int TEST(int, int) {
        auto sci = <recovery-expr>(formatters::scientific, 12345.6, 2, false);
        <recovery-expr>(EXPECT_TRUE);
}

int TEST(int, int) {
        auto sciUpper = <recovery-expr>(formatters::scientific, 12345.6, 2, true);
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find('E'));
}

int TEST(int, int) {
        FormatSpec leftSpec;
        leftSpec.align = Align::Left;
        leftSpec.width = 10;
        leftSpec.fill = '-';
        auto left = <recovery-expr>(toString, "hi", leftSpec);
        EXPECT_EQ(<recovery-expr>(), "hi--------");
}

int TEST(int, int) {
        FormatSpec rightSpec;
        rightSpec.align = Align::Right;
        rightSpec.width = 10;
        rightSpec.fill = '-';
        auto right = <recovery-expr>(toString, "hi", rightSpec);
        EXPECT_EQ(<recovery-expr>(), "--------hi");
}

int TEST(int, int) {
        FormatSpec centerSpec;
        centerSpec.align = Align::Center;
        centerSpec.width = 10;
        centerSpec.fill = '-';
        auto center = <recovery-expr>(toString, "hi", centerSpec);
        EXPECT_EQ(<recovery-expr>(), "----hi----");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>()("test", 10, Align::Left), "test      ");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>()("test", 10, Align::Right), "      test");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>()("test", 10, Align::Center), "   test   ");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>()("x", 5, Align::Right, '*'), "****x");
}

int TEST(int, int) {
        StringBuilder sb;
        <recovery-expr>(sb, "Hello") << " " << "World" << "!";
        EXPECT_EQ(<recovery-expr>(sb)(), "Hello World!");
}

int TEST(int, int) {
        StringBuilder sb;
        <recovery-expr>(sb, "test");
        sb.clear();
        <recovery-expr>(EXPECT_TRUE, sb.empty());
}

int TEST(int, int) {
        StringBuilder sb;
        <recovery-expr>(sb, 42) << " " << 3.1400000000000001 << " " << true;
        EXPECT_FALSE(<recovery-expr>(sb)().empty());
}

int TEST(int, int) {
        StringBuilder sb;
        <recovery-expr>(<recovery-expr>(sb.append, "Count: ").append, 100);
        <recovery-expr>(EXPECT_NE, <recovery-expr>(sb)().find("100"));
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatString, "Hello, {}!", "World"), "Hello, World!");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatString, "{} + {} = {}", 1, 2, 3), "1 + 2 = 3");
}

int TEST(int, int) {
        auto result = <recovery-expr>(formatString, "Name: {}, Age: {}, Active: {}", "Alice", 30, true);
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find("Alice"));
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatString, "{1} {0}", "World", "Hello"), "Hello World");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatString, "{0} {0} {0}", "echo"), "echo echo echo");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatString, "{{test}}"), "{test}");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatString, "{{{}}} = {}", "x", 42), "{x} = 42");
}

int TEST(int, int) {
        FormatStream fs;
        <recovery-expr>(fs, "Result: ") << 42 << ", " << 3.1400000000000001 << ", " << true;
        int result = <recovery-expr>(<recovery-expr>(fs)());
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find("42"));
}

int TEST(int, int) {
        FormatStream fs;
        <recovery-expr>(fs, "Result: ") << 42;
        <recovery-expr>(EXPECT_NE);
}

int TEST(int, int) {
        int value = 42;
        int *ptr = &value;
        int formatted = <recovery-expr>(<recovery-expr>(toString, ptr));
        EXPECT_EQ(<recovery-expr>().find("0x"), 0U);
}

int TEST(int, int) {
        FormatSpec specWithSign;
        specWithSign.showPos = true;
        <recovery-expr>(EXPECT_NE, <recovery-expr>(toString, 42, specWithSign).find('+'));
}

int TEST(int, int) {
        FormatSpec specWithSign;
        specWithSign.showPos = true;
        <recovery-expr>(EXPECT_NE, <recovery-expr>(toString, -42, specWithSign).find('-'));
}

int TEST(int, int) {
        FormatSpec hexSpec;
        hexSpec.base = Base::Hexadecimal;
        hexSpec.showBase = true;
        <recovery-expr>(EXPECT_NE, <recovery-expr>(toString, 255, hexSpec).find("0x"));
}

int TEST(int, int) {
        FormatSpec octSpec;
        octSpec.base = Base::Octal;
        octSpec.showBase = true;
        <recovery-expr>(EXPECT_NE, <recovery-expr>(toString, 64, octSpec).find("0o"));
}

int TEST(int, int) {
        FormatSpec binSpec;
        binSpec.base = Base::Binary;
        binSpec.showBase = true;
        <recovery-expr>(EXPECT_NE, <recovery-expr>(toString, 5, binSpec).find("0b"));
}

int TEST(int, int) {
        FormatSpec spec;
        spec.precision = 2;
        auto result = <recovery-expr>(toString, 3.1415899999999999, spec);
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find("3.14"));
}

int TEST(int, int) {
        FormatSpec strSpec;
        strSpec.precision = 5;
        EXPECT_EQ(<recovery-expr>(toString, strSpec), "Hello");
}

int TEST(int, int) {
        StringBuilder sb;
        sb << <recovery-expr>()("Name", 20, Align::Left) << " | ";
        sb << <recovery-expr>()("Age", 5, Align::Right) << " | ";
        sb << <recovery-expr>()("Score", 10, Align::Right) << "\n";
        sb << <recovery-expr>()("Alice", 20, Align::Left) << " | ";
        sb << <recovery-expr>()("30", 5, Align::Right) << " | ";
        sb << <recovery-expr>()(<recovery-expr>(formatters::fixed, 95.5, 1), 10, Align::Right) << "\n";
        int table = <recovery-expr>(<recovery-expr>(sb)());
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find("Alice"));
}

int TEST(int, int) {
        StringBuilder sb;
        sb << <recovery-expr>()("Name", 20, Align::Left) << " | ";
        sb << <recovery-expr>()("Age", 5, Align::Right) << " | ";
        sb << <recovery-expr>()("Score", 10, Align::Right) << "\n";
        sb << <recovery-expr>()("Alice", 20, Align::Left) << " | ";
        sb << <recovery-expr>()("30", 5, Align::Right) << " | ";
        sb << <recovery-expr>()(<recovery-expr>(formatters::fixed, 95.5, 1), 10, Align::Right) << "\n";
        int table = <recovery-expr>(<recovery-expr>(sb)());
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find("95.5"));
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString, 0), "0");
}

int TEST(int, int) {
        <recovery-expr>(EXPECT_NE, <recovery-expr>(toString, 1000000).find("1000000"));
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString, -1), "-1");
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(formatters::fixed, 0., 2), "0.00");
}

int TEST(int, int) {
        <recovery-expr>(EXPECT_NE, <recovery-expr>(formatters::fixed, -1.5, 1).find("-1.5"));
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString), "");
}

int TEST(int, int) {
        FormatSpec wide;
        wide.width = 50;
        wide.align = Align::Center;
        EXPECT_EQ(<recovery-expr>(toString, "x", wide).length(), 50U);
}

int TEST(int, int) {
        EXPECT_EQ(<recovery-expr>(toString, 42, FormatSpec()), "42");
}

int TEST(int, int) {
        auto result = <recovery-expr>(formatString, "Values: {}, {}, {}, {}, {}", 1, 2.5, true, "test", 'x');
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find("1"));
}

int TEST(int, int) {
        auto result = <recovery-expr>(formatString, "Values: {}, {}, {}, {}, {}", 1, 2.5, true, "test", 'x');
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find("2.5"));
}

int TEST(int, int) {
        auto result = <recovery-expr>(formatString, "Values: {}, {}, {}, {}, {}", 1, 2.5, true, "test", 'x');
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find("true"));
}

int TEST(int, int) {
        auto result = <recovery-expr>(formatString, "Values: {}, {}, {}, {}, {}", 1, 2.5, true, "test", 'x');
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find("test"));
}

int TEST(int, int) {
        auto result = <recovery-expr>(formatString, "Values: {}, {}, {}, {}, {}", 1, 2.5, true, "test", 'x');
        <recovery-expr>(EXPECT_NE, <recovery-expr>().find("x"));
}


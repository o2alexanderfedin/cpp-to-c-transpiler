#include "StringFormatter.h"
#include <iostream>
#include <cassert>
#include <cmath>

using namespace format;

void test(const std::string& name, bool condition) {
    if (condition) {
        std::cout << "[PASS] " << name << std::endl;
    } else {
        std::cout << "[FAIL] " << name << std::endl;
        throw std::runtime_error("Test failed: " + name);
    }
}

void testBasicFormatting() {
    test("Format integer", toString(42) == "42");
    test("Format double", toString(3.14159).substr(0, 4) == "3.14");
    test("Format bool true", toString(true) == "true");
    test("Format bool false", toString(false) == "false");
    test("Format string", toString(std::string("hello")) == "hello");
    test("Format c-string", toString("world") == "world");
}

void testIntegerFormatting() {
    // Decimal
    test("Integer decimal", toString(42) == "42");
    test("Negative integer", toString(-123) == "-123");

    // Hexadecimal
    test("Integer hex", formatters::hex(255, false, true) == "0xff");
    test("Integer HEX uppercase", formatters::hex(255, true, true) == "0XFF");
    test("Integer hex no prefix", formatters::hex(16, false, false) == "10");

    // Octal
    test("Integer octal", formatters::oct(64, true) == "0o100");
    test("Integer octal no prefix", formatters::oct(8, false) == "10");

    // Binary
    test("Integer binary", formatters::bin(5, true) == "0b101");
    test("Integer binary no prefix", formatters::bin(7, false) == "111");
}

void testFloatingPointFormatting() {
    // Fixed notation
    test("Float fixed 2 decimals", formatters::fixed(3.14159, 2) == "3.14");
    test("Float fixed 4 decimals", formatters::fixed(2.71828, 4) == "2.7183");

    // Scientific notation
    auto sci = formatters::scientific(12345.6, 2, false);
    test("Float scientific", sci.find("e+") != std::string::npos || sci.find("e0") != std::string::npos);

    auto sciUpper = formatters::scientific(12345.6, 2, true);
    test("Float scientific uppercase", sciUpper.find('E') != std::string::npos);
}

void testAlignment() {
    FormatSpec leftSpec;
    leftSpec.align = Align::Left;
    leftSpec.width = 10;
    leftSpec.fill = '-';

    auto left = toString("hi", leftSpec);
    test("Left alignment", left == "hi--------");

    FormatSpec rightSpec;
    rightSpec.align = Align::Right;
    rightSpec.width = 10;
    rightSpec.fill = '-';

    auto right = toString("hi", rightSpec);
    test("Right alignment", right == "--------hi");

    FormatSpec centerSpec;
    centerSpec.align = Align::Center;
    centerSpec.width = 10;
    centerSpec.fill = '-';

    auto center = toString("hi", centerSpec);
    test("Center alignment", center == "----hi----");
}

void testPadding() {
    test("Pad left", formatters::pad("test", 10, Align::Left) == "test      ");
    test("Pad right", formatters::pad("test", 10, Align::Right) == "      test");
    test("Pad center", formatters::pad("test", 10, Align::Center) == "   test   ");
    test("Pad with char", formatters::pad("x", 5, Align::Right, '*') == "****x");
}

void testStringBuilder() {
    StringBuilder sb;
    sb << "Hello" << " " << "World" << "!";
    test("StringBuilder basic", sb.str() == "Hello World!");

    sb.clear();
    test("StringBuilder clear", sb.empty());

    sb << 42 << " " << 3.14 << " " << true;
    test("StringBuilder mixed types", !sb.str().empty());

    sb.clear();
    sb.append("Count: ").append(100);
    test("StringBuilder append", sb.str().find("100") != std::string::npos);
}

void testFormatString() {
    test("Format string basic", formatString("Hello, {}!", "World") == "Hello, World!");
    test("Format string multiple", formatString("{} + {} = {}", 1, 2, 3) == "1 + 2 = 3");
    test("Format string mixed", formatString("Name: {}, Age: {}, Active: {}",
                                           "Alice", 30, true).find("Alice") != std::string::npos);
}

void testFormatStringIndexed() {
    test("Format indexed", formatString("{1} {0}", "World", "Hello") == "Hello World");
    test("Format repeated index", formatString("{0} {0} {0}", "echo") == "echo echo echo");
}

void testEscapedBraces() {
    test("Escaped opening brace", formatString("{{test}}") == "{test}");
    test("Escaped with placeholder", formatString("{{{}}} = {}", "x", 42) == "{x} = 42");
}

void testFormatStream() {
    FormatStream fs;
    fs << "Result: " << 42 << ", " << 3.14 << ", " << true;
    std::string result = fs.str();

    test("FormatStream basic", result.find("42") != std::string::npos);
    test("FormatStream implicit conversion", std::string(fs).find("Result") != std::string::npos);
}

void testPointerFormatting() {
    int value = 42;
    int* ptr = &value;

    std::string formatted = toString(ptr);
    test("Pointer formatting", formatted.find("0x") == 0);
}

void testSignDisplay() {
    FormatSpec specWithSign;
    specWithSign.showPos = true;

    test("Positive sign", toString(42, specWithSign).find('+') != std::string::npos);
    test("Negative sign", toString(-42, specWithSign).find('-') != std::string::npos);
}

void testBasePrefix() {
    FormatSpec hexSpec;
    hexSpec.base = Base::Hexadecimal;
    hexSpec.showBase = true;

    test("Hex prefix", toString(255, hexSpec).find("0x") != std::string::npos);

    FormatSpec octSpec;
    octSpec.base = Base::Octal;
    octSpec.showBase = true;

    test("Octal prefix", toString(64, octSpec).find("0o") != std::string::npos);

    FormatSpec binSpec;
    binSpec.base = Base::Binary;
    binSpec.showBase = true;

    test("Binary prefix", toString(5, binSpec).find("0b") != std::string::npos);
}

void testPrecision() {
    FormatSpec spec;
    spec.precision = 2;

    auto result = toString(3.14159, spec);
    test("Float precision", result.find("3.14") != std::string::npos);

    // String precision (truncation)
    FormatSpec strSpec;
    strSpec.precision = 5;

    test("String precision", toString(std::string("Hello, World!"), strSpec) == "Hello");
}

void testComplexFormatting() {
    StringBuilder sb;

    // Table formatting
    sb << formatters::pad("Name", 20, Align::Left) << " | ";
    sb << formatters::pad("Age", 5, Align::Right) << " | ";
    sb << formatters::pad("Score", 10, Align::Right) << "\n";

    sb << formatters::pad("Alice", 20, Align::Left) << " | ";
    sb << formatters::pad("30", 5, Align::Right) << " | ";
    sb << formatters::pad(formatters::fixed(95.5, 1), 10, Align::Right) << "\n";

    std::string table = sb.str();
    test("Table formatting", table.find("Alice") != std::string::npos);
    test("Table numbers aligned", table.find("95.5") != std::string::npos);
}

void testNumberFormats() {
    // Test various number formats
    test("Small integer", toString(0) == "0");
    test("Large integer", toString(1000000).find("1000000") != std::string::npos);
    test("Small negative", toString(-1) == "-1");

    test("Float zero", formatters::fixed(0.0, 2) == "0.00");
    test("Float negative", formatters::fixed(-1.5, 1).find("-1.5") != std::string::npos);
}

void testEdgeCases() {
    // Empty string
    test("Empty string", toString(std::string("")) == "");

    // Wide formatting
    FormatSpec wide;
    wide.width = 50;
    wide.align = Align::Center;

    test("Wide formatting", toString("x", wide).length() == 50);

    // No width specified
    test("No width", toString(42, FormatSpec()) == "42");
}

void testMultipleArguments() {
    auto result = formatString("Values: {}, {}, {}, {}, {}",
                              1, 2.5, true, "test", 'x');

    test("Multiple args 1", result.find("1") != std::string::npos);
    test("Multiple args 2.5", result.find("2.5") != std::string::npos);
    test("Multiple args true", result.find("true") != std::string::npos);
    test("Multiple args test", result.find("test") != std::string::npos);
    test("Multiple args x", result.find("x") != std::string::npos);
}

int main() {
    try {
        std::cout << "=== String Formatter Tests ===" << std::endl;

        testBasicFormatting();
        testIntegerFormatting();
        testFloatingPointFormatting();
        testAlignment();
        testPadding();
        testStringBuilder();
        testFormatString();
        testFormatStringIndexed();
        testEscapedBraces();
        testFormatStream();
        testPointerFormatting();
        testSignDisplay();
        testBasePrefix();
        testPrecision();
        testComplexFormatting();
        testNumberFormats();
        testEdgeCases();
        testMultipleArguments();

        std::cout << "\n=== All tests passed! ===" << std::endl;
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Test failed with exception: " << e.what() << std::endl;
        return 1;
    }
}

#include "StringFormatter.h"
#include <gtest/gtest.h>
#include <cmath>

using namespace format;

// ============================================================================
// Basic Formatting Tests
// ============================================================================

TEST(BasicFormattingTest, FormatInteger) {
    EXPECT_EQ(toString(42), "42");
}

TEST(BasicFormattingTest, FormatDouble) {
    EXPECT_EQ(toString(3.14159).substr(0, 4), "3.14");
}

TEST(BasicFormattingTest, FormatBoolTrue) {
    EXPECT_EQ(toString(true), "true");
}

TEST(BasicFormattingTest, FormatBoolFalse) {
    EXPECT_EQ(toString(false), "false");
}

TEST(BasicFormattingTest, FormatString) {
    EXPECT_EQ(toString(std::string("hello")), "hello");
}

TEST(BasicFormattingTest, FormatCString) {
    EXPECT_EQ(toString("world"), "world");
}

// ============================================================================
// Integer Formatting Tests
// ============================================================================

TEST(IntegerFormattingTest, IntegerDecimal) {
    EXPECT_EQ(toString(42), "42");
}

TEST(IntegerFormattingTest, NegativeInteger) {
    EXPECT_EQ(toString(-123), "-123");
}

TEST(IntegerFormattingTest, IntegerHex) {
    EXPECT_EQ(formatters::hex(255, false, true), "0xff");
}

TEST(IntegerFormattingTest, IntegerHexUppercase) {
    EXPECT_EQ(formatters::hex(255, true, true), "0XFF");
}

TEST(IntegerFormattingTest, IntegerHexNoPrefix) {
    EXPECT_EQ(formatters::hex(16, false, false), "10");
}

TEST(IntegerFormattingTest, IntegerOctal) {
    EXPECT_EQ(formatters::oct(64, true), "0o100");
}

TEST(IntegerFormattingTest, IntegerOctalNoPrefix) {
    EXPECT_EQ(formatters::oct(8, false), "10");
}

TEST(IntegerFormattingTest, IntegerBinary) {
    EXPECT_EQ(formatters::bin(5, true), "0b101");
}

TEST(IntegerFormattingTest, IntegerBinaryNoPrefix) {
    EXPECT_EQ(formatters::bin(7, false), "111");
}

// ============================================================================
// Floating Point Formatting Tests
// ============================================================================

TEST(FloatingPointFormattingTest, FloatFixed2Decimals) {
    EXPECT_EQ(formatters::fixed(3.14159, 2), "3.14");
}

TEST(FloatingPointFormattingTest, FloatFixed4Decimals) {
    EXPECT_EQ(formatters::fixed(2.71828, 4), "2.7183");
}

TEST(FloatingPointFormattingTest, FloatScientific) {
    auto sci = formatters::scientific(12345.6, 2, false);
    EXPECT_TRUE(sci.find("e+") != std::string::npos || sci.find("e0") != std::string::npos);
}

TEST(FloatingPointFormattingTest, FloatScientificUppercase) {
    auto sciUpper = formatters::scientific(12345.6, 2, true);
    EXPECT_NE(sciUpper.find('E'), std::string::npos);
}

// ============================================================================
// Alignment Tests
// ============================================================================

TEST(AlignmentTest, LeftAlignment) {
    FormatSpec leftSpec;
    leftSpec.align = Align::Left;
    leftSpec.width = 10;
    leftSpec.fill = '-';

    auto left = toString("hi", leftSpec);
    EXPECT_EQ(left, "hi--------");
}

TEST(AlignmentTest, RightAlignment) {
    FormatSpec rightSpec;
    rightSpec.align = Align::Right;
    rightSpec.width = 10;
    rightSpec.fill = '-';

    auto right = toString("hi", rightSpec);
    EXPECT_EQ(right, "--------hi");
}

TEST(AlignmentTest, CenterAlignment) {
    FormatSpec centerSpec;
    centerSpec.align = Align::Center;
    centerSpec.width = 10;
    centerSpec.fill = '-';

    auto center = toString("hi", centerSpec);
    EXPECT_EQ(center, "----hi----");
}

// ============================================================================
// Padding Tests
// ============================================================================

TEST(PaddingTest, PadLeft) {
    EXPECT_EQ(formatters::pad("test", 10, Align::Left), "test      ");
}

TEST(PaddingTest, PadRight) {
    EXPECT_EQ(formatters::pad("test", 10, Align::Right), "      test");
}

TEST(PaddingTest, PadCenter) {
    EXPECT_EQ(formatters::pad("test", 10, Align::Center), "   test   ");
}

TEST(PaddingTest, PadWithChar) {
    EXPECT_EQ(formatters::pad("x", 5, Align::Right, '*'), "****x");
}

// ============================================================================
// StringBuilder Tests
// ============================================================================

TEST(StringBuilderTest, StringBuilderBasic) {
    StringBuilder sb;
    sb << "Hello" << " " << "World" << "!";
    EXPECT_EQ(sb.str(), "Hello World!");
}

TEST(StringBuilderTest, StringBuilderClear) {
    StringBuilder sb;
    sb << "test";
    sb.clear();
    EXPECT_TRUE(sb.empty());
}

TEST(StringBuilderTest, StringBuilderMixedTypes) {
    StringBuilder sb;
    sb << 42 << " " << 3.14 << " " << true;
    EXPECT_FALSE(sb.str().empty());
}

TEST(StringBuilderTest, StringBuilderAppend) {
    StringBuilder sb;
    sb.append("Count: ").append(100);
    EXPECT_NE(sb.str().find("100"), std::string::npos);
}

// ============================================================================
// Format String Tests
// ============================================================================

TEST(FormatStringTest, FormatStringBasic) {
    EXPECT_EQ(formatString("Hello, {}!", "World"), "Hello, World!");
}

TEST(FormatStringTest, FormatStringMultiple) {
    EXPECT_EQ(formatString("{} + {} = {}", 1, 2, 3), "1 + 2 = 3");
}

TEST(FormatStringTest, FormatStringMixed) {
    auto result = formatString("Name: {}, Age: {}, Active: {}", "Alice", 30, true);
    EXPECT_NE(result.find("Alice"), std::string::npos);
}

TEST(FormatStringTest, FormatIndexed) {
    EXPECT_EQ(formatString("{1} {0}", "World", "Hello"), "Hello World");
}

TEST(FormatStringTest, FormatRepeatedIndex) {
    EXPECT_EQ(formatString("{0} {0} {0}", "echo"), "echo echo echo");
}

TEST(FormatStringTest, EscapedOpeningBrace) {
    EXPECT_EQ(formatString("{{test}}"), "{test}");
}

TEST(FormatStringTest, EscapedWithPlaceholder) {
    EXPECT_EQ(formatString("{{{}}} = {}", "x", 42), "{x} = 42");
}

// ============================================================================
// FormatStream Tests
// ============================================================================

TEST(FormatStreamTest, FormatStreamBasic) {
    FormatStream fs;
    fs << "Result: " << 42 << ", " << 3.14 << ", " << true;
    std::string result = fs.str();
    EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(FormatStreamTest, FormatStreamImplicitConversion) {
    FormatStream fs;
    fs << "Result: " << 42;
    EXPECT_NE(std::string(fs).find("Result"), std::string::npos);
}

// ============================================================================
// Pointer Formatting Tests
// ============================================================================

TEST(PointerFormattingTest, PointerFormatting) {
    int value = 42;
    int* ptr = &value;

    std::string formatted = toString(ptr);
    EXPECT_EQ(formatted.find("0x"), 0u);
}

// ============================================================================
// Sign Display Tests
// ============================================================================

TEST(SignDisplayTest, PositiveSign) {
    FormatSpec specWithSign;
    specWithSign.showPos = true;

    EXPECT_NE(toString(42, specWithSign).find('+'), std::string::npos);
}

TEST(SignDisplayTest, NegativeSign) {
    FormatSpec specWithSign;
    specWithSign.showPos = true;

    EXPECT_NE(toString(-42, specWithSign).find('-'), std::string::npos);
}

// ============================================================================
// Base Prefix Tests
// ============================================================================

TEST(BasePrefixTest, HexPrefix) {
    FormatSpec hexSpec;
    hexSpec.base = Base::Hexadecimal;
    hexSpec.showBase = true;

    EXPECT_NE(toString(255, hexSpec).find("0x"), std::string::npos);
}

TEST(BasePrefixTest, OctalPrefix) {
    FormatSpec octSpec;
    octSpec.base = Base::Octal;
    octSpec.showBase = true;

    EXPECT_NE(toString(64, octSpec).find("0o"), std::string::npos);
}

TEST(BasePrefixTest, BinaryPrefix) {
    FormatSpec binSpec;
    binSpec.base = Base::Binary;
    binSpec.showBase = true;

    EXPECT_NE(toString(5, binSpec).find("0b"), std::string::npos);
}

// ============================================================================
// Precision Tests
// ============================================================================

TEST(PrecisionTest, FloatPrecision) {
    FormatSpec spec;
    spec.precision = 2;

    auto result = toString(3.14159, spec);
    EXPECT_NE(result.find("3.14"), std::string::npos);
}

TEST(PrecisionTest, StringPrecision) {
    FormatSpec strSpec;
    strSpec.precision = 5;

    EXPECT_EQ(toString(std::string("Hello, World!"), strSpec), "Hello");
}

// ============================================================================
// Complex Formatting Tests
// ============================================================================

TEST(ComplexFormattingTest, TableFormatting) {
    StringBuilder sb;

    sb << formatters::pad("Name", 20, Align::Left) << " | ";
    sb << formatters::pad("Age", 5, Align::Right) << " | ";
    sb << formatters::pad("Score", 10, Align::Right) << "\n";

    sb << formatters::pad("Alice", 20, Align::Left) << " | ";
    sb << formatters::pad("30", 5, Align::Right) << " | ";
    sb << formatters::pad(formatters::fixed(95.5, 1), 10, Align::Right) << "\n";

    std::string table = sb.str();
    EXPECT_NE(table.find("Alice"), std::string::npos);
}

TEST(ComplexFormattingTest, TableNumbersAligned) {
    StringBuilder sb;

    sb << formatters::pad("Name", 20, Align::Left) << " | ";
    sb << formatters::pad("Age", 5, Align::Right) << " | ";
    sb << formatters::pad("Score", 10, Align::Right) << "\n";

    sb << formatters::pad("Alice", 20, Align::Left) << " | ";
    sb << formatters::pad("30", 5, Align::Right) << " | ";
    sb << formatters::pad(formatters::fixed(95.5, 1), 10, Align::Right) << "\n";

    std::string table = sb.str();
    EXPECT_NE(table.find("95.5"), std::string::npos);
}

// ============================================================================
// Number Format Tests
// ============================================================================

TEST(NumberFormatsTest, SmallInteger) {
    EXPECT_EQ(toString(0), "0");
}

TEST(NumberFormatsTest, LargeInteger) {
    EXPECT_NE(toString(1000000).find("1000000"), std::string::npos);
}

TEST(NumberFormatsTest, SmallNegative) {
    EXPECT_EQ(toString(-1), "-1");
}

TEST(NumberFormatsTest, FloatZero) {
    EXPECT_EQ(formatters::fixed(0.0, 2), "0.00");
}

TEST(NumberFormatsTest, FloatNegative) {
    EXPECT_NE(formatters::fixed(-1.5, 1).find("-1.5"), std::string::npos);
}

// ============================================================================
// Edge Cases Tests
// ============================================================================

TEST(EdgeCasesTest, EmptyString) {
    EXPECT_EQ(toString(std::string("")), "");
}

TEST(EdgeCasesTest, WideFormatting) {
    FormatSpec wide;
    wide.width = 50;
    wide.align = Align::Center;

    EXPECT_EQ(toString("x", wide).length(), 50u);
}

TEST(EdgeCasesTest, NoWidth) {
    EXPECT_EQ(toString(42, FormatSpec()), "42");
}

// ============================================================================
// Multiple Arguments Tests
// ============================================================================

TEST(MultipleArgumentsTest, MultipleArgs1) {
    auto result = formatString("Values: {}, {}, {}, {}, {}",
                              1, 2.5, true, "test", 'x');
    EXPECT_NE(result.find("1"), std::string::npos);
}

TEST(MultipleArgumentsTest, MultipleArgs2_5) {
    auto result = formatString("Values: {}, {}, {}, {}, {}",
                              1, 2.5, true, "test", 'x');
    EXPECT_NE(result.find("2.5"), std::string::npos);
}

TEST(MultipleArgumentsTest, MultipleArgsTrue) {
    auto result = formatString("Values: {}, {}, {}, {}, {}",
                              1, 2.5, true, "test", 'x');
    EXPECT_NE(result.find("true"), std::string::npos);
}

TEST(MultipleArgumentsTest, MultipleArgsTest) {
    auto result = formatString("Values: {}, {}, {}, {}, {}",
                              1, 2.5, true, "test", 'x');
    EXPECT_NE(result.find("test"), std::string::npos);
}

TEST(MultipleArgumentsTest, MultipleArgsX) {
    auto result = formatString("Values: {}, {}, {}, {}, {}",
                              1, 2.5, true, "test", 'x');
    EXPECT_NE(result.find("x"), std::string::npos);
}

#include "TestFramework.h"
#include <vector>
#include <map>
#include <cmath>
#include <algorithm>

using namespace test;

// Calculator class for testing
class Calculator {
public:
    int add(int a, int b) { return a + b; }
    int subtract(int a, int b) { return a - b; }
    int multiply(int a, int b) { return a * b; }
    double divide(double a, double b) {
        if (b == 0) throw std::invalid_argument("Division by zero");
        return a / b;
    }
    int factorial(int n) {
        if (n < 0) throw std::invalid_argument("Negative number");
        if (n == 0 || n == 1) return 1;
        return n * factorial(n - 1);
    }
    bool isPrime(int n) {
        if (n <= 1) return false;
        for (int i = 2; i * i <= n; ++i) {
            if (n % i == 0) return false;
        }
        return true;
    }
};

// String utilities for testing
class StringUtils {
public:
    static std::string toUpper(const std::string& str) {
        std::string result = str;
        std::transform(result.begin(), result.end(), result.begin(), ::toupper);
        return result;
    }
    static std::string toLower(const std::string& str) {
        std::string result = str;
        std::transform(result.begin(), result.end(), result.begin(), ::tolower);
        return result;
    }
    static std::string trim(const std::string& str) {
        size_t start = str.find_first_not_of(" \t\n\r");
        if (start == std::string::npos) return "";
        size_t end = str.find_last_not_of(" \t\n\r");
        return str.substr(start, end - start + 1);
    }
    static std::vector<std::string> split(const std::string& str, char delimiter) {
        std::vector<std::string> result;
        std::string current;
        for (char c : str) {
            if (c == delimiter) {
                if (!current.empty()) {
                    result.push_back(current);
                    current.clear();
                }
            } else {
                current += c;
            }
        }
        if (!current.empty()) {
            result.push_back(current);
        }
        return result;
    }
};

// Tests for Calculator
class CalculatorAdditionTest : public TestCase {
public:
    CalculatorAdditionTest() : TestCase("CalculatorAddition") {}
    void run() override {
        Calculator calc;
        ASSERT_EQ(calc.add(2, 3), 5);
        ASSERT_EQ(calc.add(-1, 1), 0);
        ASSERT_EQ(calc.add(-5, -3), -8);
        ASSERT_EQ(calc.add(0, 0), 0);
        ASSERT_EQ(calc.add(100, 200), 300);
    }
};

class CalculatorSubtractionTest : public TestCase {
public:
    CalculatorSubtractionTest() : TestCase("CalculatorSubtraction") {}
    void run() override {
        Calculator calc;
        ASSERT_EQ(calc.subtract(5, 3), 2);
        ASSERT_EQ(calc.subtract(10, 10), 0);
        ASSERT_EQ(calc.subtract(0, 5), -5);
        ASSERT_EQ(calc.subtract(-5, -3), -2);
    }
};

class CalculatorMultiplicationTest : public TestCase {
public:
    CalculatorMultiplicationTest() : TestCase("CalculatorMultiplication") {}
    void run() override {
        Calculator calc;
        ASSERT_EQ(calc.multiply(3, 4), 12);
        ASSERT_EQ(calc.multiply(0, 100), 0);
        ASSERT_EQ(calc.multiply(-2, 3), -6);
        ASSERT_EQ(calc.multiply(-4, -5), 20);
    }
};

class CalculatorDivisionTest : public TestCase {
public:
    CalculatorDivisionTest() : TestCase("CalculatorDivision") {}
    void run() override {
        Calculator calc;
        ASSERT_EQ(calc.divide(10.0, 2.0), 5.0);
        ASSERT_GT(calc.divide(7.0, 3.0), 2.3);
        ASSERT_LT(calc.divide(7.0, 3.0), 2.4);
        ASSERT_THROW(calc.divide(10.0, 0.0));
    }
};

class CalculatorFactorialTest : public TestCase {
public:
    CalculatorFactorialTest() : TestCase("CalculatorFactorial") {}
    void run() override {
        Calculator calc;
        ASSERT_EQ(calc.factorial(0), 1);
        ASSERT_EQ(calc.factorial(1), 1);
        ASSERT_EQ(calc.factorial(5), 120);
        ASSERT_EQ(calc.factorial(6), 720);
        ASSERT_THROW(calc.factorial(-1));
    }
};

class CalculatorPrimeTest : public TestCase {
public:
    CalculatorPrimeTest() : TestCase("CalculatorPrime") {}
    void run() override {
        Calculator calc;
        ASSERT_FALSE(calc.isPrime(0));
        ASSERT_FALSE(calc.isPrime(1));
        ASSERT_TRUE(calc.isPrime(2));
        ASSERT_TRUE(calc.isPrime(3));
        ASSERT_FALSE(calc.isPrime(4));
        ASSERT_TRUE(calc.isPrime(5));
        ASSERT_TRUE(calc.isPrime(7));
        ASSERT_FALSE(calc.isPrime(9));
        ASSERT_TRUE(calc.isPrime(11));
        ASSERT_TRUE(calc.isPrime(13));
        ASSERT_FALSE(calc.isPrime(15));
        ASSERT_TRUE(calc.isPrime(17));
        ASSERT_TRUE(calc.isPrime(19));
        ASSERT_FALSE(calc.isPrime(20));
    }
};

// Tests for StringUtils
class StringUpperCaseTest : public TestCase {
public:
    StringUpperCaseTest() : TestCase("StringUpperCase") {}
    void run() override {
        ASSERT_EQ(StringUtils::toUpper("hello"), "HELLO");
        ASSERT_EQ(StringUtils::toUpper("World"), "WORLD");
        ASSERT_EQ(StringUtils::toUpper("123"), "123");
        ASSERT_EQ(StringUtils::toUpper(""), "");
    }
};

class StringLowerCaseTest : public TestCase {
public:
    StringLowerCaseTest() : TestCase("StringLowerCase") {}
    void run() override {
        ASSERT_EQ(StringUtils::toLower("HELLO"), "hello");
        ASSERT_EQ(StringUtils::toLower("WoRlD"), "world");
        ASSERT_EQ(StringUtils::toLower("123"), "123");
        ASSERT_EQ(StringUtils::toLower(""), "");
    }
};

class StringTrimTest : public TestCase {
public:
    StringTrimTest() : TestCase("StringTrim") {}
    void run() override {
        ASSERT_EQ(StringUtils::trim("  hello  "), "hello");
        ASSERT_EQ(StringUtils::trim("\tworld\n"), "world");
        ASSERT_EQ(StringUtils::trim("  "), "");
        ASSERT_EQ(StringUtils::trim("nospace"), "nospace");
    }
};

class StringSplitTest : public TestCase {
public:
    StringSplitTest() : TestCase("StringSplit") {}
    void run() override {
        auto result1 = StringUtils::split("a,b,c", ',');
        ASSERT_EQ(result1.size(), 3);
        ASSERT_EQ(result1[0], "a");
        ASSERT_EQ(result1[1], "b");
        ASSERT_EQ(result1[2], "c");

        auto result2 = StringUtils::split("hello world", ' ');
        ASSERT_EQ(result2.size(), 2);
        ASSERT_EQ(result2[0], "hello");
        ASSERT_EQ(result2[1], "world");

        auto result3 = StringUtils::split("single", ',');
        ASSERT_EQ(result3.size(), 1);
        ASSERT_EQ(result3[0], "single");
    }
};

// Vector tests
class VectorBasicTest : public TestCase {
public:
    VectorBasicTest() : TestCase("VectorBasic") {}
    void run() override {
        std::vector<int> vec;
        ASSERT_TRUE(vec.empty());
        ASSERT_EQ(vec.size(), 0);

        vec.push_back(1);
        vec.push_back(2);
        vec.push_back(3);

        ASSERT_FALSE(vec.empty());
        ASSERT_EQ(vec.size(), 3);
        ASSERT_EQ(vec[0], 1);
        ASSERT_EQ(vec[1], 2);
        ASSERT_EQ(vec[2], 3);
    }
};

class VectorIterationTest : public TestCase {
public:
    VectorIterationTest() : TestCase("VectorIteration") {}
    void run() override {
        std::vector<int> vec = {1, 2, 3, 4, 5};
        int sum = 0;
        for (int val : vec) {
            sum += val;
        }
        ASSERT_EQ(sum, 15);
    }
};

class VectorAccessTest : public TestCase {
public:
    VectorAccessTest() : TestCase("VectorAccess") {}
    void run() override {
        std::vector<int> vec = {10, 20, 30};
        ASSERT_EQ(vec.front(), 10);
        ASSERT_EQ(vec.back(), 30);
        ASSERT_EQ(vec.at(1), 20);
    }
};

// Map tests
class MapBasicTest : public TestCase {
public:
    MapBasicTest() : TestCase("MapBasic") {}
    void run() override {
        std::map<std::string, int> ages;
        ASSERT_TRUE(ages.empty());

        ages["Alice"] = 30;
        ages["Bob"] = 25;

        ASSERT_FALSE(ages.empty());
        ASSERT_EQ(ages.size(), 2);
        ASSERT_EQ(ages["Alice"], 30);
        ASSERT_EQ(ages["Bob"], 25);
    }
};

class MapFindTest : public TestCase {
public:
    MapFindTest() : TestCase("MapFind") {}
    void run() override {
        std::map<std::string, int> scores;
        scores["test1"] = 95;
        scores["test2"] = 87;

        ASSERT_NE(scores.find("test1"), scores.end());
        ASSERT_EQ(scores.find("test3"), scores.end());
    }
};

// Edge case tests
class EdgeCaseZeroTest : public TestCase {
public:
    EdgeCaseZeroTest() : TestCase("EdgeCaseZero") {}
    void run() override {
        Calculator calc;
        ASSERT_EQ(calc.add(0, 0), 0);
        ASSERT_EQ(calc.multiply(5, 0), 0);
        ASSERT_EQ(calc.multiply(0, 5), 0);
    }
};

class EdgeCaseNegativeTest : public TestCase {
public:
    EdgeCaseNegativeTest() : TestCase("EdgeCaseNegative") {}
    void run() override {
        Calculator calc;
        ASSERT_EQ(calc.add(-1, -1), -2);
        ASSERT_EQ(calc.multiply(-2, -3), 6);
        ASSERT_EQ(calc.subtract(-5, -3), -2);
    }
};

class EdgeCaseLargeNumbersTest : public TestCase {
public:
    EdgeCaseLargeNumbersTest() : TestCase("EdgeCaseLargeNumbers") {}
    void run() override {
        Calculator calc;
        ASSERT_EQ(calc.add(1000000, 2000000), 3000000);
        ASSERT_EQ(calc.multiply(1000, 1000), 1000000);
    }
};

// Boundary tests
class BoundaryMinMaxTest : public TestCase {
public:
    BoundaryMinMaxTest() : TestCase("BoundaryMinMax") {}
    void run() override {
        std::vector<int> vec = {3, 1, 4, 1, 5, 9, 2, 6};
        int minVal = *std::min_element(vec.begin(), vec.end());
        int maxVal = *std::max_element(vec.begin(), vec.end());

        ASSERT_EQ(minVal, 1);
        ASSERT_EQ(maxVal, 9);
    }
};

class BoundaryEmptyTest : public TestCase {
public:
    BoundaryEmptyTest() : TestCase("BoundaryEmpty") {}
    void run() override {
        std::vector<int> empty;
        ASSERT_TRUE(empty.empty());
        ASSERT_EQ(empty.size(), 0);

        std::string emptyStr = "";
        ASSERT_EQ(emptyStr.length(), 0);
        ASSERT_TRUE(emptyStr.empty());
    }
};

// Performance tests
class PerformanceVectorTest : public TestCase {
public:
    PerformanceVectorTest() : TestCase("PerformanceVector") {}
    void run() override {
        std::vector<int> vec;
        for (int i = 0; i < 10000; ++i) {
            vec.push_back(i);
        }
        ASSERT_EQ(vec.size(), 10000);
        ASSERT_EQ(vec[5000], 5000);
    }
};

class PerformanceMapTest : public TestCase {
public:
    PerformanceMapTest() : TestCase("PerformanceMap") {}
    void run() override {
        std::map<int, int> map;
        for (int i = 0; i < 1000; ++i) {
            map[i] = i * 2;
        }
        ASSERT_EQ(map.size(), 1000);
        ASSERT_EQ(map[500], 1000);
    }
};

// Complex logic tests
class ComplexLogicTest1 : public TestCase {
public:
    ComplexLogicTest1() : TestCase("ComplexLogic1") {}
    void run() override {
        Calculator calc;
        int result = calc.add(calc.multiply(2, 3), calc.subtract(10, 5));
        ASSERT_EQ(result, 11); // (2*3) + (10-5) = 6 + 5 = 11
    }
};

class ComplexLogicTest2 : public TestCase {
public:
    ComplexLogicTest2() : TestCase("ComplexLogic2") {}
    void run() override {
        std::vector<int> primes;
        Calculator calc;
        for (int i = 1; i <= 20; ++i) {
            if (calc.isPrime(i)) {
                primes.push_back(i);
            }
        }
        std::vector<int> expected = {2, 3, 5, 7, 11, 13, 17, 19};
        ASSERT_EQ(primes.size(), expected.size());
        for (size_t i = 0; i < primes.size(); ++i) {
            ASSERT_EQ(primes[i], expected[i]);
        }
    }
};

class ComplexLogicTest3 : public TestCase {
public:
    ComplexLogicTest3() : TestCase("ComplexLogic3") {}
    void run() override {
        std::map<std::string, int> wordCount;
        std::string text = "hello world hello test world hello";
        auto words = StringUtils::split(text, ' ');

        for (const auto& word : words) {
            wordCount[word]++;
        }

        ASSERT_EQ(wordCount["hello"], 3);
        ASSERT_EQ(wordCount["world"], 2);
        ASSERT_EQ(wordCount["test"], 1);
    }
};

int main() {
    auto suite = std::make_unique<TestSuite>("ExampleTests");

    // Calculator tests
    suite->addTest(std::make_unique<CalculatorAdditionTest>());
    suite->addTest(std::make_unique<CalculatorSubtractionTest>());
    suite->addTest(std::make_unique<CalculatorMultiplicationTest>());
    suite->addTest(std::make_unique<CalculatorDivisionTest>());
    suite->addTest(std::make_unique<CalculatorFactorialTest>());
    suite->addTest(std::make_unique<CalculatorPrimeTest>());

    // String tests
    suite->addTest(std::make_unique<StringUpperCaseTest>());
    suite->addTest(std::make_unique<StringLowerCaseTest>());
    suite->addTest(std::make_unique<StringTrimTest>());
    suite->addTest(std::make_unique<StringSplitTest>());

    // Container tests
    suite->addTest(std::make_unique<VectorBasicTest>());
    suite->addTest(std::make_unique<VectorIterationTest>());
    suite->addTest(std::make_unique<VectorAccessTest>());
    suite->addTest(std::make_unique<MapBasicTest>());
    suite->addTest(std::make_unique<MapFindTest>());

    // Edge case tests
    suite->addTest(std::make_unique<EdgeCaseZeroTest>());
    suite->addTest(std::make_unique<EdgeCaseNegativeTest>());
    suite->addTest(std::make_unique<EdgeCaseLargeNumbersTest>());

    // Boundary tests
    suite->addTest(std::make_unique<BoundaryMinMaxTest>());
    suite->addTest(std::make_unique<BoundaryEmptyTest>());

    // Performance tests
    suite->addTest(std::make_unique<PerformanceVectorTest>());
    suite->addTest(std::make_unique<PerformanceMapTest>());

    // Complex logic tests
    suite->addTest(std::make_unique<ComplexLogicTest1>());
    suite->addTest(std::make_unique<ComplexLogicTest2>());
    suite->addTest(std::make_unique<ComplexLogicTest3>());

    TestRegistry::getInstance().addSuite("ExampleTests", std::move(suite));
    return RUN_ALL_TESTS();
}

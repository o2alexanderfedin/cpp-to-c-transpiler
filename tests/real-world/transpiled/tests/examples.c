#include "transpiled.h"

/* Calculator method implementations */

/* StringUtils method implementations */

int subtract(int a, int b) {
    return a - b;
}

int multiply(int a, int b) {
    return a * b;
}

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

string toLower(const std) {
    std::string result = str;
    std::transform(result.begin(), result.end(), result.begin(), ::tolower);
    return result;
}

string trim(const std) {
    size_t start = str.find_first_not_of(" \t\n\r");
    if (start == std::string::npos) return "";
    size_t end = str.find_last_not_of(" \t\n\r");
    return str.substr(start, end - start + 1);
}

int main(void) {
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


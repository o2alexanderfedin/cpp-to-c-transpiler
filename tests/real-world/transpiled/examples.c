// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp
// Implementation file

#include "examples.h"

namespace test {
        class TestFailure {
        private:
                int file_;
                int line_;
        public:
                TestFailure(const int &message, const int &file, int line) : line_(line) {
                }
                const int &getFile() const {
                }
                int getLine() const {
                        return this->line_;
                }
                int fullMessage() const {
                        int oss;
                        return <recovery-expr>().str();
                }
        };
        struct TestResult {
                int name;
                bool passed;
                int message;
                double duration_ms;
                TestResult() : passed(false), duration_ms(0.) {
                }
        };
        class TestCase {
        protected:
                int name_;
                virtual void setUp() {
                }
                virtual void tearDown() {
                }
        public:
                explicit TestCase(const int &name) {
                }
                virtual ~TestCase() = default;
                virtual void run() = 0;
                const int &getName() const {
                }
                TestResult execute() {
                        TestResult result;
                        try {
                                this->setUp();
                                this->run();
                                this->tearDown();
                                result.passed = true;
                        } catch (const TestFailure &e) {
                                result.passed = false;
                                <recovery-expr>(result) = <recovery-expr>(e)();
                        } catch (const int &e) {
                                result.passed = false;
                        } catch (...) {
                                result.passed = false;
                                <recovery-expr>(result) = "Unknown exception";
                        }
                        return result;
                }
        };
        class TestSuite {
        private:
                int name_;
        public:
                explicit TestSuite(const int &name) {
                }
                void addTest(int test) {
                }
                int run() {
                }
                const int &getName() const {
                }
                int size() const {
                }
        };
        class TestRegistry {
        private:
                static TestRegistry *instance_;
                TestRegistry() noexcept = default;
        public:
                static TestRegistry &getInstance() {
                        if (!instance_) {
                                instance_ = new TestRegistry();
                        }
                        return *instance_;
                }
                void addSuite(const int &name, int suite) {
                }
                TestSuite *getSuite(const int &name) {
                        auto it;
                        if (<recovery-expr>()) {
                                return <recovery-expr>()->second.get();
                        }
                        return nullptr;
                }
                int getSuiteNames() const {
                }
                int runAll() {
                        int totalTests = 0;
                        int passedTests = 0;
                        if (passedTests == totalTests) {
                                return 0;
                        } else {
                                return 1;
                        }
                }
        };
        inline void assertTrue(bool condition, const int &message, const int &file, int line) {
                if (!condition) {
                        throw TestFailure("Assertion failed: " + <recovery-expr>(), <recovery-expr>(), line);
                }
        }
        inline void assertFalse(bool condition, const int &message, const int &file, int line) {
                if (condition) {
                        throw TestFailure("Assertion failed: " + <recovery-expr>(), <recovery-expr>(), line);
                }
        }
        template <typename T1, typename T2> inline void assertEqual(const T1 &actual, const T2 &expected, const int &file, int line) {
                if (!(actual == expected)) {
                        int oss;
                        <recovery-expr>(oss) << "Expected: " << expected << ", Actual: " << actual;
                        throw TestFailure(<recovery-expr>().str(), <recovery-expr>(), line);
                }
        }
        template <typename T1, typename T2> inline void assertNotEqual(const T1 &actual, const T2 &expected, const int &file, int line) {
                if (actual == expected) {
                        int oss;
                        <recovery-expr>(oss) << "Values should not be equal: " << actual;
                        throw TestFailure(<recovery-expr>().str(), <recovery-expr>(), line);
                }
        }
        template <typename T1, typename T2> inline void assertLess(const T1 &actual, const T2 &limit, const int &file, int line) {
                if (!(actual < limit)) {
                        int oss;
                        <recovery-expr>(oss) << "Expected " << actual << " < " << limit;
                        throw TestFailure(<recovery-expr>().str(), <recovery-expr>(), line);
                }
        }
        template <typename T1, typename T2> inline void assertGreater(const T1 &actual, const T2 &limit, const int &file, int line) {
                if (!(actual > limit)) {
                        int oss;
                        <recovery-expr>(oss) << "Expected " << actual << " > " << limit;
                        throw TestFailure(<recovery-expr>().str(), <recovery-expr>(), line);
                }
        }
        inline void assertNull(const void *ptr, const int &file, int line) {
                if (ptr != nullptr) {
                        throw TestFailure("Expected null pointer", <recovery-expr>(), line);
                }
        }
        inline void assertNotNull(const void *ptr, const int &file, int line) {
                if (ptr == nullptr) {
                        throw TestFailure("Expected non-null pointer", <recovery-expr>(), line);
                }
        }
        template <typename Func> inline void assertThrows(Func func, const int &file, int line) {
                bool threw = false;
                try {
                        func();
                } catch (...) {
                        threw = true;
                }
                if (!threw) {
                        throw TestFailure("Expected exception was not thrown", <recovery-expr>(), line);
                }
        }
        template <typename Exception, typename Func> inline void assertThrowsType(Func func, const int &file, int line) {
                bool threw = false;
                try {
                        func();
                } catch (const Exception &) {
                        threw = true;
                } catch (...) {
                        throw TestFailure("Wrong exception type thrown", <recovery-expr>(), line);
                }
                if (!threw) {
                        throw TestFailure("Expected exception was not thrown", <recovery-expr>(), line);
                }
        }
}
using namespace test
class Calculator {
public:
        int add(int a, int b) {
                return a + b;
        }
        int subtract(int a, int b) {
                return a - b;
        }
        int multiply(int a, int b) {
                return a * b;
        }
        double divide(double a, double b) {
                return a / b;
        }
        int factorial(int n) {
                if (n == 0 || n == 1)
                        return 1;
                return n * this->factorial(n - 1);
        }
        bool isPrime(int n) {
                if (n <= 1)
                        return false;
                for (int i = 2; i * i <= n; ++i) {
                        if (n % i == 0)
                                return false;
                }
                return true;
        }
};
class StringUtils {
public:
        static int toUpper(const int &str) {
                int result = <recovery-expr>(<recovery-expr>());
                return <recovery-expr>();
        }
        static int toLower(const int &str) {
                int result = <recovery-expr>(<recovery-expr>());
                return <recovery-expr>();
        }
        static int trim(const int &str) {
                int start = <recovery-expr>(<recovery-expr>().find_first_not_of(" \t\n\r"));
                if (<recovery-expr>())
                        return <recovery-expr>("");
                int end = <recovery-expr>(<recovery-expr>().find_last_not_of(" \t\n\r"));
                return <recovery-expr>().substr(<recovery-expr>(), <recovery-expr>() - <recovery-expr>() + 1);
        }
        static int split(const int &str, char delimiter) {
                int current;
                if (!<recovery-expr>().empty()) {
                }
        }
};
class CalculatorAdditionTest : public TestCase {
public:
        CalculatorAdditionTest() : TestCase(<recovery-expr>("CalculatorAddition")) {
        }
        void run() override {
                Calculator calc;
                <recovery-expr>(test::assertEqual, (calc.add(2, 3)), (5), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 78);
                <recovery-expr>(test::assertEqual, (calc.add(-1, 1)), (0), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 79);
                <recovery-expr>(test::assertEqual, (calc.add(-5, -3)), (-8), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 80);
                <recovery-expr>(test::assertEqual, (calc.add(0, 0)), (0), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 81);
                <recovery-expr>(test::assertEqual, (calc.add(100, 200)), (300), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 82);
        }
};
class CalculatorSubtractionTest : public TestCase {
public:
        CalculatorSubtractionTest() : TestCase(<recovery-expr>("CalculatorSubtraction")) {
        }
        void run() override {
                Calculator calc;
                <recovery-expr>(test::assertEqual, (calc.subtract(5, 3)), (2), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 91);
                <recovery-expr>(test::assertEqual, (calc.subtract(10, 10)), (0), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 92);
                <recovery-expr>(test::assertEqual, (calc.subtract(0, 5)), (-5), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 93);
                <recovery-expr>(test::assertEqual, (calc.subtract(-5, -3)), (-2), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 94);
        }
};
class CalculatorMultiplicationTest : public TestCase {
public:
        CalculatorMultiplicationTest() : TestCase(<recovery-expr>("CalculatorMultiplication")) {
        }
        void run() override {
                Calculator calc;
                <recovery-expr>(test::assertEqual, (calc.multiply(3, 4)), (12), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 103);
                <recovery-expr>(test::assertEqual, (calc.multiply(0, 100)), (0), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 104);
                <recovery-expr>(test::assertEqual, (calc.multiply(-2, 3)), (-6), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 105);
                <recovery-expr>(test::assertEqual, (calc.multiply(-4, -5)), (20), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 106);
        }
};
class CalculatorDivisionTest : public TestCase {
public:
        CalculatorDivisionTest() : TestCase(<recovery-expr>("CalculatorDivision")) {
        }
        void run() override {
                Calculator calc;
                <recovery-expr>(test::assertEqual, (calc.divide(10., 2.)), (5.), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 115);
                <recovery-expr>(test::assertGreater, (calc.divide(7., 3.)), (2.2999999999999998), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 116);
                <recovery-expr>(test::assertLess, (calc.divide(7., 3.)), (2.3999999999999999), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 117);
                <recovery-expr>(test::assertThrows, [&]() {
                        calc.divide(10., 0.);
                }, "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 118);
        }
};
class CalculatorFactorialTest : public TestCase {
public:
        CalculatorFactorialTest() : TestCase(<recovery-expr>("CalculatorFactorial")) {
        }
        void run() override {
                Calculator calc;
                <recovery-expr>(test::assertEqual, (calc.factorial(0)), (1), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 127);
                <recovery-expr>(test::assertEqual, (calc.factorial(1)), (1), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 128);
                <recovery-expr>(test::assertEqual, (calc.factorial(5)), (120), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 129);
                <recovery-expr>(test::assertEqual, (calc.factorial(6)), (720), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 130);
                <recovery-expr>(test::assertThrows, [&]() {
                        calc.factorial(-1);
                }, "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 131);
        }
};
class CalculatorPrimeTest : public TestCase {
public:
        CalculatorPrimeTest() : TestCase(<recovery-expr>("CalculatorPrime")) {
        }
        void run() override {
                Calculator calc;
                <recovery-expr>(test::assertFalse)((calc.isPrime(0)), "calc.isPrime(0)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 140);
                <recovery-expr>(test::assertFalse)((calc.isPrime(1)), "calc.isPrime(1)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 141);
                <recovery-expr>(test::assertTrue)((calc.isPrime(2)), "calc.isPrime(2)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 142);
                <recovery-expr>(test::assertTrue)((calc.isPrime(3)), "calc.isPrime(3)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 143);
                <recovery-expr>(test::assertFalse)((calc.isPrime(4)), "calc.isPrime(4)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 144);
                <recovery-expr>(test::assertTrue)((calc.isPrime(5)), "calc.isPrime(5)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 145);
                <recovery-expr>(test::assertTrue)((calc.isPrime(7)), "calc.isPrime(7)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 146);
                <recovery-expr>(test::assertFalse)((calc.isPrime(9)), "calc.isPrime(9)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 147);
                <recovery-expr>(test::assertTrue)((calc.isPrime(11)), "calc.isPrime(11)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 148);
                <recovery-expr>(test::assertTrue)((calc.isPrime(13)), "calc.isPrime(13)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 149);
                <recovery-expr>(test::assertFalse)((calc.isPrime(15)), "calc.isPrime(15)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 150);
                <recovery-expr>(test::assertTrue)((calc.isPrime(17)), "calc.isPrime(17)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 151);
                <recovery-expr>(test::assertTrue)((calc.isPrime(19)), "calc.isPrime(19)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 152);
                <recovery-expr>(test::assertFalse)((calc.isPrime(20)), "calc.isPrime(20)", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 153);
        }
};
class StringUpperCaseTest : public TestCase {
public:
        StringUpperCaseTest() : TestCase(<recovery-expr>("StringUpperCase")) {
        }
        void run() override {
                test::assertEqual((<recovery-expr>()("hello")), ("HELLO"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 162);
                test::assertEqual((<recovery-expr>()("World")), ("WORLD"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 163);
                test::assertEqual((<recovery-expr>()("123")), ("123"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 164);
                test::assertEqual((<recovery-expr>()("")), (""), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 165);
        }
};
class StringLowerCaseTest : public TestCase {
public:
        StringLowerCaseTest() : TestCase(<recovery-expr>("StringLowerCase")) {
        }
        void run() override {
                test::assertEqual((<recovery-expr>()("HELLO")), ("hello"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 173);
                test::assertEqual((<recovery-expr>()("WoRlD")), ("world"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 174);
                test::assertEqual((<recovery-expr>()("123")), ("123"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 175);
                test::assertEqual((<recovery-expr>()("")), (""), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 176);
        }
};
class StringTrimTest : public TestCase {
public:
        StringTrimTest() : TestCase(<recovery-expr>("StringTrim")) {
        }
        void run() override {
                test::assertEqual((<recovery-expr>()("  hello  ")), ("hello"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 184);
                test::assertEqual((<recovery-expr>()("\tworld\n")), ("world"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 185);
                test::assertEqual((<recovery-expr>()("  ")), (""), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 186);
                test::assertEqual((<recovery-expr>()("nospace")), ("nospace"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 187);
        }
};
class StringSplitTest : public TestCase {
public:
        StringSplitTest() : TestCase(<recovery-expr>("StringSplit")) {
        }
        void run() override {
                auto result1 = <recovery-expr>()("a,b,c", ',');
                test::assertEqual((<recovery-expr>(result1).size()), (3), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 196);
                test::assertEqual((<recovery-expr>(result1)[0]), ("a"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 197);
                test::assertEqual((<recovery-expr>(result1)[1]), ("b"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 198);
                test::assertEqual((<recovery-expr>(result1)[2]), ("c"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 199);
                auto result2 = <recovery-expr>()("hello world", ' ');
                test::assertEqual((<recovery-expr>(result2).size()), (2), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 202);
                test::assertEqual((<recovery-expr>(result2)[0]), ("hello"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 203);
                test::assertEqual((<recovery-expr>(result2)[1]), ("world"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 204);
                auto result3 = <recovery-expr>()("single", ',');
                test::assertEqual((<recovery-expr>(result3).size()), (1), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 207);
                test::assertEqual((<recovery-expr>(result3)[0]), ("single"), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 208);
        }
};
class VectorBasicTest : public TestCase {
public:
        VectorBasicTest() : TestCase(<recovery-expr>("VectorBasic")) {
        }
        void run() override {
                <recovery-expr>(<recovery-expr>(test::assertTrue), "vec.empty()", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 218);
                <recovery-expr>(test::assertEqual, (0), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 219);
                <recovery-expr>(<recovery-expr>(test::assertFalse), "vec.empty()", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 225);
                <recovery-expr>(test::assertEqual, (3), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 226);
                <recovery-expr>(test::assertEqual, (1), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 227);
                <recovery-expr>(test::assertEqual, (2), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 228);
                <recovery-expr>(test::assertEqual, (3), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 229);
        }
};
class VectorIterationTest : public TestCase {
public:
        VectorIterationTest() : TestCase(<recovery-expr>("VectorIteration")) {
        }
        void run() override {
                int sum = 0;
                <recovery-expr>(test::assertEqual, (sum), (15), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 242);
        }
};
class VectorAccessTest : public TestCase {
public:
        VectorAccessTest() : TestCase(<recovery-expr>("VectorAccess")) {
        }
        void run() override {
                <recovery-expr>(test::assertEqual, (10), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 251);
                <recovery-expr>(test::assertEqual, (30), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 252);
                <recovery-expr>(test::assertEqual, (20), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 253);
        }
};
class MapBasicTest : public TestCase {
public:
        MapBasicTest() : TestCase(<recovery-expr>("MapBasic")) {
        }
        void run() override {
                <recovery-expr>(<recovery-expr>(test::assertTrue), "ages.empty()", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 263);
                <recovery-expr>(<recovery-expr>(test::assertFalse), "ages.empty()", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 268);
                <recovery-expr>(test::assertEqual, (2), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 269);
                <recovery-expr>(test::assertEqual, (30), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 270);
                <recovery-expr>(test::assertEqual, (25), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 271);
        }
};
class MapFindTest : public TestCase {
public:
        MapFindTest() : TestCase(<recovery-expr>("MapFind")) {
        }
        void run() override {
                <recovery-expr>(test::assertNotEqual, "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 283);
                <recovery-expr>(test::assertEqual, "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 284);
        }
};
class EdgeCaseZeroTest : public TestCase {
public:
        EdgeCaseZeroTest() : TestCase(<recovery-expr>("EdgeCaseZero")) {
        }
        void run() override {
                Calculator calc;
                <recovery-expr>(test::assertEqual, (calc.add(0, 0)), (0), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 294);
                <recovery-expr>(test::assertEqual, (calc.multiply(5, 0)), (0), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 295);
                <recovery-expr>(test::assertEqual, (calc.multiply(0, 5)), (0), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 296);
        }
};
class EdgeCaseNegativeTest : public TestCase {
public:
        EdgeCaseNegativeTest() : TestCase(<recovery-expr>("EdgeCaseNegative")) {
        }
        void run() override {
                Calculator calc;
                <recovery-expr>(test::assertEqual, (calc.add(-1, -1)), (-2), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 305);
                <recovery-expr>(test::assertEqual, (calc.multiply(-2, -3)), (6), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 306);
                <recovery-expr>(test::assertEqual, (calc.subtract(-5, -3)), (-2), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 307);
        }
};
class EdgeCaseLargeNumbersTest : public TestCase {
public:
        EdgeCaseLargeNumbersTest() : TestCase(<recovery-expr>("EdgeCaseLargeNumbers")) {
        }
        void run() override {
                Calculator calc;
                <recovery-expr>(test::assertEqual, (calc.add(1000000, 2000000)), (3000000), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 316);
                <recovery-expr>(test::assertEqual, (calc.multiply(1000, 1000)), (1000000), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 317);
        }
};
class BoundaryMinMaxTest : public TestCase {
public:
        BoundaryMinMaxTest() : TestCase(<recovery-expr>("BoundaryMinMax")) {
        }
        void run() override {
                int minVal;
                int maxVal;
                <recovery-expr>(test::assertEqual, (minVal), (1), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 330);
                <recovery-expr>(test::assertEqual, (maxVal), (9), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 331);
        }
};
class BoundaryEmptyTest : public TestCase {
public:
        BoundaryEmptyTest() : TestCase(<recovery-expr>("BoundaryEmpty")) {
        }
        void run() override {
                <recovery-expr>(<recovery-expr>(test::assertTrue), "empty.empty()", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 340);
                <recovery-expr>(test::assertEqual, (0), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 341);
                int emptyStr = <recovery-expr>("");
                test::assertEqual((<recovery-expr>(emptyStr).length()), (0), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 344);
                <recovery-expr>(test::assertTrue)((<recovery-expr>(emptyStr).empty()), "emptyStr.empty()", "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 345);
        }
};
class PerformanceVectorTest : public TestCase {
public:
        PerformanceVectorTest() : TestCase(<recovery-expr>("PerformanceVector")) {
        }
        void run() override {
                for (int i = 0; i < 10000; ++i) {
                }
                <recovery-expr>(test::assertEqual, (10000), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 358);
                <recovery-expr>(test::assertEqual, (5000), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 359);
        }
};
class PerformanceMapTest : public TestCase {
public:
        PerformanceMapTest() : TestCase(<recovery-expr>("PerformanceMap")) {
        }
        void run() override {
                for (int i = 0; i < 1000; ++i) {
                }
                <recovery-expr>(test::assertEqual, (1000), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 371);
                <recovery-expr>(test::assertEqual, (1000), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 372);
        }
};
class ComplexLogicTest1 : public TestCase {
public:
        ComplexLogicTest1() : TestCase(<recovery-expr>("ComplexLogic1")) {
        }
        void run() override {
                Calculator calc;
                int result = calc.add(calc.multiply(2, 3), calc.subtract(10, 5));
                <recovery-expr>(test::assertEqual, (result), (11), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 383);
        }
};
class ComplexLogicTest2 : public TestCase {
public:
        ComplexLogicTest2() : TestCase(<recovery-expr>("ComplexLogic2")) {
        }
        void run() override {
                Calculator calc;
                for (int i = 1; i <= 20; ++i) {
                        if (calc.isPrime(i)) {
                        }
                }
                <recovery-expr>(test::assertEqual, "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 399);
                for (int i = <recovery-expr>(0); <recovery-expr>(); ++<recovery-expr>()) {
                        <recovery-expr>(test::assertEqual, "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 401);
                }
        }
};
class ComplexLogicTest3 : public TestCase {
public:
        ComplexLogicTest3() : TestCase(<recovery-expr>("ComplexLogic3")) {
        }
        void run() override {
                int text = <recovery-expr>("hello world hello test world hello");
                auto words = <recovery-expr>()(<recovery-expr>(), ' ');
                <recovery-expr>(test::assertEqual, (3), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 418);
                <recovery-expr>(test::assertEqual, (2), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 419);
                <recovery-expr>(test::assertEqual, (1), "/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/examples.cpp", 420);
        }
};
int main() {
        auto suite;
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(suite)->addTest);
        <recovery-expr>(<recovery-expr>(TestRegistry::getInstance()), "ExampleTests");
        return test::TestRegistry::getInstance().runAll();
}


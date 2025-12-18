#include "TestFramework.h"
#include <memory>

using namespace test;

// Sample test fixture
class MathFixture : public TestCase {
protected:
    int value;

    void setUp() override {
        value = 0;
    }

    void tearDown() override {
        value = -1;
    }

public:
    explicit MathFixture(const std::string& name) : TestCase(name) {}
};

// Test basic assertions
class BasicAssertionsTest : public TestCase {
public:
    BasicAssertionsTest() : TestCase("BasicAssertions") {}

    void run() override {
        // assertTrue
        ASSERT_TRUE(true);
        ASSERT_TRUE(1 == 1);
        ASSERT_TRUE(5 > 3);

        // assertFalse
        ASSERT_FALSE(false);
        ASSERT_FALSE(1 == 2);

        // assertEqual
        ASSERT_EQ(42, 42);
        ASSERT_EQ("hello", std::string("hello"));
        ASSERT_EQ(3.14, 3.14);

        // assertNotEqual
        ASSERT_NE(1, 2);
        ASSERT_NE("foo", std::string("bar"));

        // assertLess
        ASSERT_LT(1, 2);
        ASSERT_LT(-5, 0);

        // assertGreater
        ASSERT_GT(10, 5);
        ASSERT_GT(0, -1);
    }
};

// Test pointer assertions
class PointerAssertionsTest : public TestCase {
public:
    PointerAssertionsTest() : TestCase("PointerAssertions") {}

    void run() override {
        int* nullPtr = nullptr;
        int value = 42;
        int* nonNullPtr = &value;

        ASSERT_NULL(nullPtr);
        ASSERT_NOT_NULL(nonNullPtr);
    }
};

// Test exception assertions
class ExceptionAssertionsTest : public TestCase {
public:
    ExceptionAssertionsTest() : TestCase("ExceptionAssertions") {}

    void run() override {
        // assertThrows
        ASSERT_THROW(throw std::runtime_error("test"));

        // assertThrowsType
        ASSERT_THROW_TYPE(
            throw std::invalid_argument("test"),
            std::invalid_argument
        );

        // This should pass - function throws exception
        ASSERT_THROW({
            if (true) {
                throw std::logic_error("expected");
            }
        });
    }
};

// Test fixture setup/teardown
class FixtureTest : public MathFixture {
public:
    FixtureTest() : MathFixture("FixtureSetupTeardown") {}

    void run() override {
        // setUp should have initialized value to 0
        ASSERT_EQ(value, 0);

        value = 100;
        ASSERT_EQ(value, 100);

        // tearDown will set it to -1 after this test
    }
};

// Test string comparisons
class StringTest : public TestCase {
public:
    StringTest() : TestCase("StringComparisons") {}

    void run() override {
        std::string s1 = "hello";
        std::string s2 = "hello";
        std::string s3 = "world";

        ASSERT_EQ(s1, s2);
        ASSERT_NE(s1, s3);
        ASSERT_TRUE(s1 < s3);  // "hello" < "world"
    }
};

// Test arithmetic operations
class ArithmeticTest : public TestCase {
public:
    ArithmeticTest() : TestCase("ArithmeticOperations") {}

    void run() override {
        int a = 10;
        int b = 5;

        ASSERT_EQ(a + b, 15);
        ASSERT_EQ(a - b, 5);
        ASSERT_EQ(a * b, 50);
        ASSERT_EQ(a / b, 2);
        ASSERT_EQ(a % b, 0);
    }
};

// Test floating point comparisons
class FloatTest : public TestCase {
public:
    FloatTest() : TestCase("FloatingPoint") {}

    void run() override {
        double pi = 3.14159;
        double e = 2.71828;

        ASSERT_GT(pi, e);
        ASSERT_LT(e, pi);
        ASSERT_GT(pi, 3.0);
        ASSERT_LT(pi, 3.2);
    }
};

// Test boolean logic
class BooleanTest : public TestCase {
public:
    BooleanTest() : TestCase("BooleanLogic") {}

    void run() override {
        bool t = true;
        bool f = false;

        ASSERT_TRUE(t);
        ASSERT_FALSE(f);
        ASSERT_TRUE(t && t);
        ASSERT_FALSE(t && f);
        ASSERT_TRUE(t || f);
        ASSERT_FALSE(f || f);
        ASSERT_TRUE(!f);
        ASSERT_FALSE(!t);
    }
};

// Test container operations
class ContainerTest : public TestCase {
public:
    ContainerTest() : TestCase("ContainerOperations") {}

    void run() override {
        std::vector<int> vec = {1, 2, 3, 4, 5};

        ASSERT_EQ(vec.size(), 5);
        ASSERT_FALSE(vec.empty());
        ASSERT_EQ(vec[0], 1);
        ASSERT_EQ(vec[4], 5);

        vec.push_back(6);
        ASSERT_EQ(vec.size(), 6);
        ASSERT_EQ(vec.back(), 6);
    }
};

// Main test runner
int main() {
    try {
        // Create test suite
        auto suite = std::make_unique<TestSuite>("CoreTests");

        // Add tests
        suite->addTest(std::make_unique<BasicAssertionsTest>());
        suite->addTest(std::make_unique<PointerAssertionsTest>());
        suite->addTest(std::make_unique<ExceptionAssertionsTest>());
        suite->addTest(std::make_unique<FixtureTest>());
        suite->addTest(std::make_unique<StringTest>());
        suite->addTest(std::make_unique<ArithmeticTest>());
        suite->addTest(std::make_unique<FloatTest>());
        suite->addTest(std::make_unique<BooleanTest>());
        suite->addTest(std::make_unique<ContainerTest>());

        // Register suite
        TestRegistry::getInstance().addSuite("CoreTests", std::move(suite));

        // Run all tests
        return RUN_ALL_TESTS();

    } catch (const std::exception& e) {
        std::cerr << "Fatal error: " << e.what() << std::endl;
        return 1;
    }
}

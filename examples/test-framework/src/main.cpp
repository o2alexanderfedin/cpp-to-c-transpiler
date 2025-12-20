// Unit Test Framework Example
// Demonstrates templates, exceptions, and multiple inheritance

#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <exception>

// ============================================================================
// Test Framework Core
// ============================================================================

class AssertionError : public std::exception {
    char message[256];
    const char* file;
    int line;

public:
    AssertionError(const char* msg, const char* f, int l)
        : file(f), line(l) {
        snprintf(message, sizeof(message), "%s:%d: %s", file, line, msg);
    }

    const char* what() const noexcept override {
        return message;
    }

    const char* getFile() const { return file; }
    int getLine() const { return line; }
};

// ============================================================================
// Assertion Macros
// ============================================================================

#define ASSERT_EQ(expected, actual) \
    do { \
        if ((expected) != (actual)) { \
            char msg[256]; \
            snprintf(msg, sizeof(msg), "Expected %d but got %d", \
                    (int)(expected), (int)(actual)); \
            throw AssertionError(msg, __FILE__, __LINE__); \
        } \
    } while(0)

#define ASSERT_NE(expected, actual) \
    do { \
        if ((expected) == (actual)) { \
            throw AssertionError("Values should not be equal", __FILE__, __LINE__); \
        } \
    } while(0)

#define ASSERT_LT(a, b) \
    do { \
        if ((a) >= (b)) { \
            char msg[256]; \
            snprintf(msg, sizeof(msg), "Expected %d < %d", (int)(a), (int)(b)); \
            throw AssertionError(msg, __FILE__, __LINE__); \
        } \
    } while(0)

#define ASSERT_TRUE(condition) \
    do { \
        if (!(condition)) { \
            throw AssertionError("Expected true", __FILE__, __LINE__); \
        } \
    } while(0)

#define ASSERT_FALSE(condition) \
    do { \
        if (condition) { \
            throw AssertionError("Expected false", __FILE__, __LINE__); \
        } \
    } while(0)

// ============================================================================
// TestCase Base Class
// ============================================================================

class TestCase {
protected:
    const char* name;
    const char* suite_name;
    bool passed;
    char error_message[256];

public:
    TestCase(const char* test_name, const char* suite)
        : name(test_name), suite_name(suite), passed(false) {
        error_message[0] = '\0';
    }

    virtual ~TestCase() {}

    virtual void SetUp() {}
    virtual void TearDown() {}
    virtual void Run() = 0;

    void Execute() {
        printf("[ RUN      ] %s.%s\n", suite_name, name);

        try {
            SetUp();
            Run();
            TearDown();
            passed = true;
            printf("[       OK ] %s.%s\n", suite_name, name);
        } catch (const AssertionError& e) {
            passed = false;
            snprintf(error_message, sizeof(error_message), "%s", e.what());
            printf("[  FAILED  ] %s.%s\n", suite_name, name);
            printf("             %s\n", error_message);
        } catch (const std::exception& e) {
            passed = false;
            snprintf(error_message, sizeof(error_message),
                    "Unexpected exception: %s", e.what());
            printf("[  FAILED  ] %s.%s\n", suite_name, name);
            printf("             %s\n", error_message);
        }
    }

    bool hasPassed() const { return passed; }
    const char* getName() const { return name; }
    const char* getSuiteName() const { return suite_name; }
};

// ============================================================================
// Test Fixture (with setup/teardown)
// ============================================================================

class TestFixture : public TestCase {
public:
    TestFixture(const char* name, const char* suite)
        : TestCase(name, suite) {}

    // Subclasses override SetUp and TearDown
};

// ============================================================================
// Test Suite
// ============================================================================

class TestSuite {
    TestCase* tests[32];
    int test_count;
    const char* name;

public:
    TestSuite(const char* suite_name) : test_count(0), name(suite_name) {}

    void addTest(TestCase* test) {
        if (test_count < 32) {
            tests[test_count++] = test;
        }
    }

    void runAll() {
        printf("[----------] %d tests from %s\n", test_count, name);

        int passed = 0;
        for (int i = 0; i < test_count; i++) {
            tests[i]->Execute();
            if (tests[i]->hasPassed()) {
                passed++;
            }
        }

        printf("[----------] %d tests from %s (%d passed, %d failed)\n\n",
               test_count, name, passed, test_count - passed);
    }

    int getPassedCount() const {
        int count = 0;
        for (int i = 0; i < test_count; i++) {
            if (tests[i]->hasPassed()) count++;
        }
        return count;
    }

    int getTestCount() const { return test_count; }
    const char* getName() const { return name; }
};

// ============================================================================
// Concrete Test Cases
// ============================================================================

// Math Tests
class AdditionTest : public TestCase {
public:
    AdditionTest() : TestCase("Addition", "MathTests") {}

    void Run() override {
        ASSERT_EQ(2 + 2, 4);
        ASSERT_EQ(10 + 5, 15);
        ASSERT_EQ(0 + 0, 0);
        ASSERT_EQ(-5 + 5, 0);
    }
};

class SubtractionTest : public TestCase {
public:
    SubtractionTest() : TestCase("Subtraction", "MathTests") {}

    void Run() override {
        ASSERT_EQ(10 - 5, 5);
        ASSERT_EQ(0 - 5, -5);
        ASSERT_EQ(5 - 5, 0);
    }
};

class MultiplicationTest : public TestCase {
public:
    MultiplicationTest() : TestCase("Multiplication", "MathTests") {}

    void Run() override {
        ASSERT_EQ(3 * 4, 12);
        ASSERT_EQ(0 * 5, 0);
        ASSERT_EQ(-2 * 3, -6);
    }
};

class ComparisonTest : public TestCase {
public:
    ComparisonTest() : TestCase("Comparisons", "MathTests") {}

    void Run() override {
        ASSERT_LT(5, 10);
        ASSERT_LT(0, 1);
        ASSERT_LT(-10, 0);
        ASSERT_TRUE(5 == 5);
        ASSERT_FALSE(5 == 6);
    }
};

// String Tests
class StringLengthTest : public TestCase {
public:
    StringLengthTest() : TestCase("Length", "StringTests") {}

    void Run() override {
        ASSERT_EQ(strlen("hello"), 5);
        ASSERT_EQ(strlen(""), 0);
        ASSERT_EQ(strlen("test"), 4);
    }
};

class StringCompareTest : public TestCase {
public:
    StringCompareTest() : TestCase("Compare", "StringTests") {}

    void Run() override {
        ASSERT_EQ(strcmp("hello", "hello"), 0);
        ASSERT_NE(strcmp("hello", "world"), 0);
        ASSERT_TRUE(strcmp("abc", "abc") == 0);
    }
};

// Fixture Test Example
class ResourceTest : public TestFixture {
    int* resource;

public:
    ResourceTest() : TestFixture("ResourceManagement", "FixtureTests"),
                     resource(nullptr) {}

    void SetUp() override {
        resource = (int*)malloc(sizeof(int) * 10);
        for (int i = 0; i < 10; i++) {
            resource[i] = i;
        }
    }

    void TearDown() override {
        if (resource) {
            free(resource);
            resource = nullptr;
        }
    }

    void Run() override {
        ASSERT_TRUE(resource != nullptr);
        ASSERT_EQ(resource[0], 0);
        ASSERT_EQ(resource[5], 5);
        ASSERT_EQ(resource[9], 9);
    }
};

// ============================================================================
// Test Runner
// ============================================================================

int main() {
    printf("Test Framework Example\n");
    printf("======================\n\n");

    // Create test suites
    TestSuite math_suite("MathTests");
    TestSuite string_suite("StringTests");
    TestSuite fixture_suite("FixtureTests");

    // Add math tests
    AdditionTest addition;
    SubtractionTest subtraction;
    MultiplicationTest multiplication;
    ComparisonTest comparison;

    math_suite.addTest(&addition);
    math_suite.addTest(&subtraction);
    math_suite.addTest(&multiplication);
    math_suite.addTest(&comparison);

    // Add string tests
    StringLengthTest string_length;
    StringCompareTest string_compare;

    string_suite.addTest(&string_length);
    string_suite.addTest(&string_compare);

    // Add fixture tests
    ResourceTest resource_test;
    fixture_suite.addTest(&resource_test);

    // Run all tests
    printf("Running tests...\n\n");

    int total_tests = 0;
    int total_passed = 0;

    printf("[==========] Running tests\n");

    math_suite.runAll();
    total_tests += math_suite.getTestCount();
    total_passed += math_suite.getPassedCount();

    string_suite.runAll();
    total_tests += string_suite.getTestCount();
    total_passed += string_suite.getPassedCount();

    fixture_suite.runAll();
    total_tests += fixture_suite.getTestCount();
    total_passed += fixture_suite.getPassedCount();

    // Summary
    printf("[==========] %d tests ran\n", total_tests);
    printf("[  PASSED  ] %d tests\n", total_passed);

    if (total_passed < total_tests) {
        printf("[  FAILED  ] %d tests\n", total_tests - total_passed);
        return 1;
    }

    printf("\n=== All tests passed! ===\n");
    return 0;
}

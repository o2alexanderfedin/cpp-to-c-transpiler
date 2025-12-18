#ifndef TEST_FRAMEWORK_H
#define TEST_FRAMEWORK_H

#include <string>
#include <vector>
#include <functional>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <memory>
#include <map>

namespace test {

// Test failure exception
class TestFailure : public std::runtime_error {
private:
    std::string file_;
    int line_;

public:
    TestFailure(const std::string& message, const std::string& file, int line)
        : std::runtime_error(message), file_(file), line_(line) {}

    const std::string& getFile() const { return file_; }
    int getLine() const { return line_; }

    std::string fullMessage() const {
        std::ostringstream oss;
        oss << file_ << ":" << line_ << ": " << what();
        return oss.str();
    }
};

// Test result
struct TestResult {
    std::string name;
    bool passed;
    std::string message;
    double duration_ms;

    TestResult() : passed(false), duration_ms(0.0) {}
};

// Test case base class
class TestCase {
protected:
    std::string name_;

    virtual void setUp() {}
    virtual void tearDown() {}

public:
    explicit TestCase(const std::string& name) : name_(name) {}
    virtual ~TestCase() = default;

    virtual void run() = 0;

    const std::string& getName() const { return name_; }

    TestResult execute() {
        TestResult result;
        result.name = name_;

        try {
            setUp();
            run();
            tearDown();
            result.passed = true;
        } catch (const TestFailure& e) {
            result.passed = false;
            result.message = e.fullMessage();
        } catch (const std::exception& e) {
            result.passed = false;
            result.message = std::string("Unexpected exception: ") + e.what();
        } catch (...) {
            result.passed = false;
            result.message = "Unknown exception";
        }

        return result;
    }
};

// Test suite
class TestSuite {
private:
    std::string name_;
    std::vector<std::unique_ptr<TestCase>> tests_;

public:
    explicit TestSuite(const std::string& name) : name_(name) {}

    void addTest(std::unique_ptr<TestCase> test) {
        tests_.push_back(std::move(test));
    }

    std::vector<TestResult> run() {
        std::vector<TestResult> results;
        for (auto& test : tests_) {
            results.push_back(test->execute());
        }
        return results;
    }

    const std::string& getName() const { return name_; }
    size_t size() const { return tests_.size(); }
};

// Test registry (singleton)
class TestRegistry {
private:
    std::map<std::string, std::unique_ptr<TestSuite>> suites_;
    static TestRegistry* instance_;

    TestRegistry() = default;

public:
    static TestRegistry& getInstance() {
        if (!instance_) {
            instance_ = new TestRegistry();
        }
        return *instance_;
    }

    void addSuite(const std::string& name, std::unique_ptr<TestSuite> suite) {
        suites_[name] = std::move(suite);
    }

    TestSuite* getSuite(const std::string& name) {
        auto it = suites_.find(name);
        if (it != suites_.end()) {
            return it->second.get();
        }
        return nullptr;
    }

    std::vector<std::string> getSuiteNames() const {
        std::vector<std::string> names;
        for (const auto& pair : suites_) {
            names.push_back(pair.first);
        }
        return names;
    }

    int runAll() {
        int totalTests = 0;
        int passedTests = 0;

        std::cout << "Running all test suites..." << std::endl;
        std::cout << "=====================================" << std::endl;

        for (auto& pair : suites_) {
            std::cout << "\nSuite: " << pair.first << std::endl;
            auto results = pair.second->run();

            for (const auto& result : results) {
                totalTests++;
                if (result.passed) {
                    passedTests++;
                    std::cout << "  [PASS] " << result.name << std::endl;
                } else {
                    std::cout << "  [FAIL] " << result.name << std::endl;
                    std::cout << "    " << result.message << std::endl;
                }
            }
        }

        std::cout << "\n=====================================" << std::endl;
        std::cout << "Results: " << passedTests << "/" << totalTests << " passed";

        if (passedTests == totalTests) {
            std::cout << " ✓" << std::endl;
            return 0;
        } else {
            std::cout << " ✗" << std::endl;
            return 1;
        }
    }
};

// Assertion functions
inline void assertTrue(bool condition, const std::string& message,
                       const std::string& file, int line) {
    if (!condition) {
        throw TestFailure("Assertion failed: " + message, file, line);
    }
}

inline void assertFalse(bool condition, const std::string& message,
                        const std::string& file, int line) {
    if (condition) {
        throw TestFailure("Assertion failed: " + message, file, line);
    }
}

template<typename T1, typename T2>
inline void assertEqual(const T1& actual, const T2& expected,
                        const std::string& file, int line) {
    if (!(actual == expected)) {
        std::ostringstream oss;
        oss << "Expected: " << expected << ", Actual: " << actual;
        throw TestFailure(oss.str(), file, line);
    }
}

template<typename T1, typename T2>
inline void assertNotEqual(const T1& actual, const T2& expected,
                           const std::string& file, int line) {
    if (actual == expected) {
        std::ostringstream oss;
        oss << "Values should not be equal: " << actual;
        throw TestFailure(oss.str(), file, line);
    }
}

template<typename T1, typename T2>
inline void assertLess(const T1& actual, const T2& limit,
                       const std::string& file, int line) {
    if (!(actual < limit)) {
        std::ostringstream oss;
        oss << "Expected " << actual << " < " << limit;
        throw TestFailure(oss.str(), file, line);
    }
}

template<typename T1, typename T2>
inline void assertGreater(const T1& actual, const T2& limit,
                          const std::string& file, int line) {
    if (!(actual > limit)) {
        std::ostringstream oss;
        oss << "Expected " << actual << " > " << limit;
        throw TestFailure(oss.str(), file, line);
    }
}

inline void assertNull(const void* ptr, const std::string& file, int line) {
    if (ptr != nullptr) {
        throw TestFailure("Expected null pointer", file, line);
    }
}

inline void assertNotNull(const void* ptr, const std::string& file, int line) {
    if (ptr == nullptr) {
        throw TestFailure("Expected non-null pointer", file, line);
    }
}

template<typename Func>
inline void assertThrows(Func func, const std::string& file, int line) {
    bool threw = false;
    try {
        func();
    } catch (...) {
        threw = true;
    }

    if (!threw) {
        throw TestFailure("Expected exception was not thrown", file, line);
    }
}

template<typename Exception, typename Func>
inline void assertThrowsType(Func func, const std::string& file, int line) {
    bool threw = false;
    try {
        func();
    } catch (const Exception&) {
        threw = true;
    } catch (...) {
        throw TestFailure("Wrong exception type thrown", file, line);
    }

    if (!threw) {
        throw TestFailure("Expected exception was not thrown", file, line);
    }
}

} // namespace test

// Macros for test definition
#define TEST_SUITE(name) \
    class TestSuite_##name : public test::TestSuite { \
    public: \
        TestSuite_##name() : TestSuite(#name) {} \
    };

#define TEST_CASE(suite, name) \
    class TestCase_##suite##_##name : public test::TestCase { \
    public: \
        TestCase_##suite##_##name() : TestCase(#name) {} \
        void run() override; \
    }; \
    void TestCase_##suite##_##name::run()

#define TEST_FIXTURE(suite, name, fixture) \
    class TestCase_##suite##_##name : public fixture { \
    private: \
        std::string name_; \
    public: \
        TestCase_##suite##_##name() : name_(#name) {} \
        void run(); \
        const std::string& getName() const { return name_; } \
    }; \
    void TestCase_##suite##_##name::run()

// Assertion macros
#define ASSERT_TRUE(condition) \
    test::assertTrue((condition), #condition, __FILE__, __LINE__)

#define ASSERT_FALSE(condition) \
    test::assertFalse((condition), #condition, __FILE__, __LINE__)

#define ASSERT_EQ(actual, expected) \
    test::assertEqual((actual), (expected), __FILE__, __LINE__)

#define ASSERT_NE(actual, expected) \
    test::assertNotEqual((actual), (expected), __FILE__, __LINE__)

#define ASSERT_LT(actual, limit) \
    test::assertLess((actual), (limit), __FILE__, __LINE__)

#define ASSERT_GT(actual, limit) \
    test::assertGreater((actual), (limit), __FILE__, __LINE__)

#define ASSERT_NULL(ptr) \
    test::assertNull((ptr), __FILE__, __LINE__)

#define ASSERT_NOT_NULL(ptr) \
    test::assertNotNull((ptr), __FILE__, __LINE__)

#define ASSERT_THROW(expression) \
    test::assertThrows([&]() { expression; }, __FILE__, __LINE__)

#define ASSERT_THROW_TYPE(expression, exception_type) \
    test::assertThrowsType<exception_type>([&]() { expression; }, __FILE__, __LINE__)

#define RUN_ALL_TESTS() \
    test::TestRegistry::getInstance().runAll()

#endif // TEST_FRAMEWORK_H

// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/src/TestRegistry.cpp
// Implementation file

#include "TestRegistry.h"

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
namespace test {
        TestRegistry *instance_ = nullptr;
}

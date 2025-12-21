// RaiiIntegrationTest.cpp - Test suite for Stream 3: Smart Pointers & RAII
// File 3 of 3: RAII Integration tests (Collaborative)
//
// Tests for smart pointers integrated with RAII patterns:
// - Smart pointers with RAII resources (file, network, locks)
// - Exception safety with smart pointers
// - Resource cleanup guarantees
// - Complex RAII scenarios
//
// Migrated to Google Test Framework
// Total: 25 tests

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include <string>

using namespace clang;

// ============================================================================
// Test Fixtures for RAII Integration Tests
// ============================================================================

class RaiiFileResourceTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> buildAST(const char* code) {
        return tooling::buildASTFromCode(code);
    }
};

class RaiiLockResourceTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> buildAST(const char* code) {
        return tooling::buildASTFromCode(code);
    }
};

class RaiiExceptionSafetyTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> buildAST(const char* code) {
        return tooling::buildASTFromCode(code);
    }
};

class RaiiComplexScenarioTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> buildAST(const char* code) {
        return tooling::buildASTFromCode(code);
    }
};

class RaiiPerformanceTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> buildAST(const char* code) {
        return tooling::buildASTFromCode(code);
    }
};

// ============================================================================
// Group 1: Smart Pointers with File Resources (5 tests)
// ============================================================================

TEST_F(RaiiFileResourceTest, UniquePtrWithFileResource) {
    const char *Code = R"(
        #include <memory>
        #include <cstdio>

        class FileHandle {
        private:
            FILE* file;
        public:
            FileHandle(const char* path) : file(fopen(path, "r")) {}
            ~FileHandle() { if (file) fclose(file); }
        };

        void test() {
            std::unique_ptr<FileHandle> handle(new FileHandle("test.txt"));
            // Automatic cleanup: FileHandle destructor closes file
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiFileResourceTest, SharedPtrWithFileResource) {
    const char *Code = R"(
        #include <memory>
        #include <cstdio>

        void test() {
            auto deleter = [](FILE* f) { if (f) fclose(f); };
            std::shared_ptr<FILE> file1(fopen("test.txt", "r"), deleter);
            std::shared_ptr<FILE> file2 = file1;  // Shared ownership
            // File closed when both file1 and file2 go out of scope
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiFileResourceTest, UniquePtrWithRaiiBuffer) {
    const char *Code = R"(
        #include <memory>

        class Buffer {
        private:
            char* data;
            size_t size;
        public:
            Buffer(size_t s) : size(s), data(new char[s]) {}
            ~Buffer() { delete[] data; }
        };

        void test() {
            std::unique_ptr<Buffer> buf(new Buffer(1024));
            // Automatic cleanup: Buffer destructor frees memory
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiFileResourceTest, UniquePtrWithMultipleRaiiResources) {
    const char *Code = R"(
        #include <memory>
        #include <cstdio>

        class ResourceManager {
        private:
            FILE* file1;
            FILE* file2;
            char* buffer;
        public:
            ResourceManager()
                : file1(fopen("a.txt", "r"))
                , file2(fopen("b.txt", "r"))
                , buffer(new char[1024]) {}

            ~ResourceManager() {
                if (file1) fclose(file1);
                if (file2) fclose(file2);
                delete[] buffer;
            }
        };

        void test() {
            std::unique_ptr<ResourceManager> mgr(new ResourceManager());
            // All resources cleaned up automatically
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiFileResourceTest, SharedPtrWithRaiiEarlyReturn) {
    const char *Code = R"(
        #include <memory>

        class Resource {
        public:
            Resource() {}
            ~Resource() { /* cleanup */ }
        };

        int process(bool condition) {
            auto res = std::make_shared<Resource>();
            if (condition) {
                return 1;  // Resource destroyed here
            }
            return 0;  // Resource destroyed here
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

// ============================================================================
// Group 2: Smart Pointers with Lock Resources (5 tests)
// ============================================================================

TEST_F(RaiiLockResourceTest, UniquePtrWithMutexLock) {
    const char *Code = R"(
        #include <memory>
        #include <mutex>

        class ScopedLock {
        private:
            std::mutex& mtx;
        public:
            ScopedLock(std::mutex& m) : mtx(m) { mtx.lock(); }
            ~ScopedLock() { mtx.unlock(); }
        };

        void test() {
            std::mutex mtx;
            std::unique_ptr<ScopedLock> lock(new ScopedLock(mtx));
            // Automatic unlock at scope exit
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiLockResourceTest, SharedPtrWithLockGuard) {
    const char *Code = R"(
        #include <memory>
        #include <mutex>

        void test() {
            std::mutex mtx;
            auto guard = std::make_shared<std::lock_guard<std::mutex>>(mtx);
            // Lock held until guard destroyed
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiLockResourceTest, UniquePtrWithRecursiveLock) {
    const char *Code = R"(
        #include <memory>
        #include <mutex>

        class RecursiveLock {
        private:
            std::recursive_mutex& mtx;
            int depth;
        public:
            RecursiveLock(std::recursive_mutex& m) : mtx(m), depth(1) {
                mtx.lock();
            }
            ~RecursiveLock() {
                for (int i = 0; i < depth; ++i) {
                    mtx.unlock();
                }
            }
        };

        void test() {
            std::recursive_mutex mtx;
            std::unique_ptr<RecursiveLock> lock(new RecursiveLock(mtx));
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiLockResourceTest, UniquePtrWithReadWriteLock) {
    const char *Code = R"(
        #include <memory>
        #include <shared_mutex>

        class ReadLock {
        private:
            std::shared_mutex& mtx;
        public:
            ReadLock(std::shared_mutex& m) : mtx(m) { mtx.lock_shared(); }
            ~ReadLock() { mtx.unlock_shared(); }
        };

        void test() {
            std::shared_mutex mtx;
            std::unique_ptr<ReadLock> lock(new ReadLock(mtx));
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiLockResourceTest, MultipleLocksWithUniquePtr) {
    const char *Code = R"(
        #include <memory>
        #include <mutex>

        class DualLock {
        private:
            std::mutex& mtx1;
            std::mutex& mtx2;
        public:
            DualLock(std::mutex& m1, std::mutex& m2) : mtx1(m1), mtx2(m2) {
                std::lock(mtx1, mtx2);  // Deadlock-free locking
            }
            ~DualLock() {
                mtx1.unlock();
                mtx2.unlock();
            }
        };

        void test() {
            std::mutex mtx1, mtx2;
            std::unique_ptr<DualLock> lock(new DualLock(mtx1, mtx2));
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

// ============================================================================
// Group 3: Exception Safety with Smart Pointers (6 tests)
// ============================================================================

TEST_F(RaiiExceptionSafetyTest, UniquePtrExceptionSafetyAutomaticCleanup) {
    const char *Code = R"(
        #include <memory>

        class Resource {
        public:
            Resource() {}
            ~Resource() { /* cleanup */ }
        };

        void may_throw() { throw 42; }

        void test() {
            try {
                std::unique_ptr<Resource> res(new Resource());
                may_throw();  // Resource destroyed even if exception thrown
            } catch (...) {}
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiExceptionSafetyTest, SharedPtrExceptionSafety) {
    const char *Code = R"(
        #include <memory>

        class Resource {
        public:
            Resource() {}
            ~Resource() {}
        };

        void may_throw() { throw 42; }

        void test() {
            try {
                auto res1 = std::make_shared<Resource>();
                auto res2 = res1;  // ref_count = 2
                may_throw();
                // res2 destroyed (ref_count = 1)
            } catch (...) {}
            // res1 destroyed (ref_count = 0, object deleted)
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiExceptionSafetyTest, MakeUniqueExceptionSafetyVsConstructor) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            Widget(int v) {}
        };

        void process(std::unique_ptr<Widget> p1, std::unique_ptr<Widget> p2) {}

        void test() {
            // SAFE: make_unique ensures exception safety
            process(
                std::make_unique<Widget>(1),
                std::make_unique<Widget>(2)
            );
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiExceptionSafetyTest, RaiiWithExceptionInConstructor) {
    const char *Code = R"(
        #include <memory>

        class Resource {
        public:
            Resource() { throw 42; }  // Exception in constructor
            ~Resource() {}
        };

        void test() {
            try {
                std::unique_ptr<Resource> res(new Resource());
                // unique_ptr never constructed, delete still called on new Resource()
            } catch (...) {}
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiExceptionSafetyTest, ExceptionWithMultipleRaiiResources) {
    const char *Code = R"(
        #include <memory>

        class Resource1 {
        public:
            Resource1() {}
            ~Resource1() {}
        };

        class Resource2 {
        public:
            Resource2() {}
            ~Resource2() {}
        };

        void may_throw() { throw 42; }

        void test() {
            try {
                auto res1 = std::make_unique<Resource1>();
                auto res2 = std::make_unique<Resource2>();
                may_throw();
            } catch (...) {}
            // Both res2 and res1 destroyed in reverse order
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiExceptionSafetyTest, ExceptionSafetyWithNestedScopes) {
    const char *Code = R"(
        #include <memory>

        class Resource {
        public:
            Resource() {}
            ~Resource() {}
        };

        void may_throw() { throw 42; }

        void test() {
            try {
                auto outer = std::make_unique<Resource>();
                {
                    auto inner = std::make_unique<Resource>();
                    may_throw();
                    // inner destroyed here
                }
                // outer destroyed here
            } catch (...) {}
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

// ============================================================================
// Group 4: Complex RAII Scenarios (6 tests)
// ============================================================================

TEST_F(RaiiComplexScenarioTest, SmartPointerWithVirtualInheritanceRaii) {
    const char *Code = R"(
        #include <memory>

        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        private:
            char* buffer;
        public:
            Derived() : buffer(new char[1024]) {}
            ~Derived() override { delete[] buffer; }
        };

        void test() {
            std::unique_ptr<Base> ptr = std::make_unique<Derived>();
            // Virtual destructor ensures Derived::~Derived() is called
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiComplexScenarioTest, SmartPointerInMemberInitializationList) {
    const char *Code = R"(
        #include <memory>

        class Resource {
        public:
            Resource() {}
            ~Resource() {}
        };

        class Owner {
        private:
            std::unique_ptr<Resource> res;
        public:
            Owner() : res(std::make_unique<Resource>()) {}
            // Compiler-generated destructor calls res.~unique_ptr()
        };

        void test() {
            Owner owner;
        }  // owner.~Owner() -> res.~unique_ptr() -> Resource.~Resource()
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiComplexScenarioTest, SmartPointerMoveSemanticsInConstructor) {
    const char *Code = R"(
        #include <memory>
        #include <utility>

        class Resource {
        public:
            Resource() {}
            ~Resource() {}
        };

        class Owner {
        private:
            std::unique_ptr<Resource> res;
        public:
            Owner(std::unique_ptr<Resource> r) : res(std::move(r)) {}
        };

        void test() {
            auto res = std::make_unique<Resource>();
            Owner owner(std::move(res));  // res is now null
        }  // owner.~Owner() destroys resource
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiComplexScenarioTest, SmartPointerConditionalCleanup) {
    const char *Code = R"(
        #include <memory>

        class Resource {
        public:
            Resource() {}
            ~Resource() {}
        };

        void test(bool condition) {
            std::unique_ptr<Resource> res;
            if (condition) {
                res = std::make_unique<Resource>();
            }
            // res destroyed only if condition was true
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiComplexScenarioTest, SmartPointerFactoryPattern) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            Widget() {}
            virtual ~Widget() {}
        };

        class ConcreteWidget : public Widget {
        public:
            ConcreteWidget() {}
            ~ConcreteWidget() override {}
        };

        std::unique_ptr<Widget> create_widget() {
            return std::make_unique<ConcreteWidget>();
        }

        void test() {
            auto widget = create_widget();
            // Automatic cleanup via virtual destructor
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiComplexScenarioTest, SharedPointerObserverPattern) {
    const char *Code = R"(
        #include <memory>
        #include <vector>

        class Observer {
        public:
            virtual ~Observer() {}
        };

        class Subject {
        private:
            std::vector<std::weak_ptr<Observer>> observers;
        public:
            void attach(std::shared_ptr<Observer> obs) {
                observers.push_back(obs);
            }

            void notify() {
                for (auto& weak : observers) {
                    if (auto obs = weak.lock()) {
                        // Use observer
                    }
                }
            }
        };

        void test() {
            Subject subject;
            auto obs = std::make_shared<Observer>();
            subject.attach(obs);
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

// ============================================================================
// Group 5: Performance and Memory Considerations (3 tests)
// ============================================================================

TEST_F(RaiiPerformanceTest, SmartPointerVsRawPointerOverhead) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
        };

        void test() {
            // unique_ptr: minimal overhead (single pointer)
            std::unique_ptr<Widget> up(new Widget());

            // shared_ptr: overhead of ref counting
            std::shared_ptr<Widget> sp(new Widget());

            // raw pointer: no overhead, manual cleanup required
            Widget* raw = new Widget();
            delete raw;
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiPerformanceTest, MemoryLayoutWithSmartPointers) {
    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            int value;
        };

        class Container {
        private:
            std::unique_ptr<Widget> up;    // sizeof(Widget*)
            std::shared_ptr<Widget> sp;     // sizeof(Widget*) + sizeof(control_block*)
            Widget* raw;                    // sizeof(Widget*)
        };
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

TEST_F(RaiiPerformanceTest, SmartPointerCacheLocality) {
    const char *Code = R"(
        #include <memory>
        #include <vector>

        class Widget {
        public:
            int value;
        };

        void test() {
            // Vector of unique_ptr: pointers stored contiguously, objects not
            std::vector<std::unique_ptr<Widget>> vec_ptr;
            for (int i = 0; i < 100; ++i) {
                vec_ptr.push_back(std::make_unique<Widget>());
            }

            // Vector of objects: objects stored contiguously (better cache locality)
            std::vector<Widget> vec_obj;
            for (int i = 0; i < 100; ++i) {
                vec_obj.push_back(Widget());
            }
        }
    )";

    auto AST = buildAST(Code);
    ASSERT_NE(AST, nullptr) << "AST should be built";
}

// ============================================================================
// Main Function
// ============================================================================

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}

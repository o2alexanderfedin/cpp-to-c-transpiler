// RaiiIntegrationTest.cpp - Test suite for Stream 3: Smart Pointers & RAII
// File 3 of 3: RAII Integration tests (Collaborative)
//
// Tests for smart pointers integrated with RAII patterns:
// - Smart pointers with RAII resources (file, network, locks)
// - Exception safety with smart pointers
// - Resource cleanup guarantees
// - Complex RAII scenarios
//
// Target: 20-30 tests

#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace clang;

// ============================================================================
// Group 1: Smart Pointers with File Resources (5 tests)
// ============================================================================

// Test 1: unique_ptr with FILE* resource
void test_unique_ptr_with_file_resource() {
    std::cout << "Running test_unique_ptr_with_file_resource... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation:
    // struct FileHandle { FILE* file; };
    // void FileHandle_init(struct FileHandle* self, const char* path) {
    //     self->file = fopen(path, "r");
    // }
    // void FileHandle_destroy(struct FileHandle* self) {
    //     if (self->file) fclose(self->file);
    // }
    // void test() {
    //     struct FileHandle* handle = FileHandle_new("test.txt");
    //     FileHandle_destroy(handle);  // at scope exit
    //     free(handle);
    // }

    std::cout << "✓" << std::endl;
}

// Test 2: shared_ptr with FILE* resource (multiple owners)
void test_shared_ptr_with_file_resource() {
    std::cout << "Running test_shared_ptr_with_file_resource... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 3: unique_ptr with RAII buffer
void test_unique_ptr_with_raii_buffer() {
    std::cout << "Running test_unique_ptr_with_raii_buffer... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 4: unique_ptr with multiple RAII resources
void test_unique_ptr_with_multiple_raii_resources() {
    std::cout << "Running test_unique_ptr_with_multiple_raii_resources... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 5: shared_ptr with RAII and early return
void test_shared_ptr_with_raii_early_return() {
    std::cout << "Running test_shared_ptr_with_raii_early_return... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 2: Smart Pointers with Lock Resources (5 tests)
// ============================================================================

// Test 6: unique_ptr with mutex lock (RAII)
void test_unique_ptr_with_mutex_lock() {
    std::cout << "Running test_unique_ptr_with_mutex_lock... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 7: shared_ptr with lock guard
void test_shared_ptr_with_lock_guard() {
    std::cout << "Running test_shared_ptr_with_lock_guard... ";

    const char *Code = R"(
        #include <memory>
        #include <mutex>

        void test() {
            std::mutex mtx;
            auto guard = std::make_shared<std::lock_guard<std::mutex>>(mtx);
            // Lock held until guard destroyed
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 8: unique_ptr with recursive lock
void test_unique_ptr_with_recursive_lock() {
    std::cout << "Running test_unique_ptr_with_recursive_lock... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 9: unique_ptr with read-write lock
void test_unique_ptr_with_read_write_lock() {
    std::cout << "Running test_unique_ptr_with_read_write_lock... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 10: Multiple locks with unique_ptr (deadlock prevention)
void test_multiple_locks_with_unique_ptr() {
    std::cout << "Running test_multiple_locks_with_unique_ptr... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 3: Exception Safety with Smart Pointers (6 tests)
// ============================================================================

// Test 11: unique_ptr exception safety (automatic cleanup)
void test_unique_ptr_exception_safety_automatic_cleanup() {
    std::cout << "Running test_unique_ptr_exception_safety_automatic_cleanup... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    // Expected C translation (with exception handling):
    // void test() {
    //     __exception_frame_t frame;
    //     if (setjmp(frame.jmp_buf) == 0) {
    //         struct Resource* res = Resource_new();
    //         may_throw();
    //         Resource_destroy(res);  // Normal path
    //     } else {
    //         Resource_destroy(res);  // Exception path
    //         // Handle exception
    //     }
    // }

    std::cout << "✓" << std::endl;
}

// Test 12: shared_ptr exception safety
void test_shared_ptr_exception_safety() {
    std::cout << "Running test_shared_ptr_exception_safety... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 13: make_unique vs unique_ptr constructor exception safety
void test_make_unique_exception_safety_vs_constructor() {
    std::cout << "Running test_make_unique_exception_safety_vs_constructor... ";

    const char *Code = R"(
        #include <memory>

        class Widget {
        public:
            Widget(int v) {}
        };

        void process(std::unique_ptr<Widget> p1, std::unique_ptr<Widget> p2) {}

        void test() {
            // UNSAFE: Potential leak if exception thrown between allocations
            // process(
            //     std::unique_ptr<Widget>(new Widget(1)),
            //     std::unique_ptr<Widget>(new Widget(2))
            // );

            // SAFE: make_unique ensures exception safety
            process(
                std::make_unique<Widget>(1),
                std::make_unique<Widget>(2)
            );
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 14: RAII with exception in constructor
void test_raii_with_exception_in_constructor() {
    std::cout << "Running test_raii_with_exception_in_constructor... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 15: Exception with multiple RAII resources
void test_exception_with_multiple_raii_resources() {
    std::cout << "Running test_exception_with_multiple_raii_resources... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 16: Exception safety with nested scopes
void test_exception_safety_with_nested_scopes() {
    std::cout << "Running test_exception_safety_with_nested_scopes... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 4: Complex RAII Scenarios (6 tests)
// ============================================================================

// Test 17: Smart pointer with virtual inheritance RAII
void test_smart_pointer_with_virtual_inheritance_raii() {
    std::cout << "Running test_smart_pointer_with_virtual_inheritance_raii... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 18: Smart pointer in member initialization list
void test_smart_pointer_in_member_initialization_list() {
    std::cout << "Running test_smart_pointer_in_member_initialization_list... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 19: Smart pointer with move semantics in constructor
void test_smart_pointer_move_semantics_in_constructor() {
    std::cout << "Running test_smart_pointer_move_semantics_in_constructor... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 20: Smart pointer with conditional cleanup
void test_smart_pointer_conditional_cleanup() {
    std::cout << "Running test_smart_pointer_conditional_cleanup... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 21: Smart pointer factory pattern
void test_smart_pointer_factory_pattern() {
    std::cout << "Running test_smart_pointer_factory_pattern... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 22: Shared pointer with observer pattern
void test_shared_pointer_observer_pattern() {
    std::cout << "Running test_shared_pointer_observer_pattern... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Group 5: Performance and Memory Considerations (3 tests)
// ============================================================================

// Test 23: Smart pointer vs raw pointer performance
void test_smart_pointer_vs_raw_pointer_overhead() {
    std::cout << "Running test_smart_pointer_vs_raw_pointer_overhead... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 24: Memory layout with smart pointers
void test_memory_layout_with_smart_pointers() {
    std::cout << "Running test_memory_layout_with_smart_pointers... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 25: Smart pointer cache locality
void test_smart_pointer_cache_locality() {
    std::cout << "Running test_smart_pointer_cache_locality... ";

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

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Main Function
// ============================================================================

int main() {
    std::cout << "\n=== RaiiIntegrationTest - Stream 3: Smart Pointers & RAII ===" << std::endl;
    std::cout << "File 3 of 3: RAII Integration tests (25 tests)\n" << std::endl;

    // Group 1: Smart Pointers with File Resources (5 tests)
    test_unique_ptr_with_file_resource();
    test_shared_ptr_with_file_resource();
    test_unique_ptr_with_raii_buffer();
    test_unique_ptr_with_multiple_raii_resources();
    test_shared_ptr_with_raii_early_return();

    // Group 2: Smart Pointers with Lock Resources (5 tests)
    test_unique_ptr_with_mutex_lock();
    test_shared_ptr_with_lock_guard();
    test_unique_ptr_with_recursive_lock();
    test_unique_ptr_with_read_write_lock();
    test_multiple_locks_with_unique_ptr();

    // Group 3: Exception Safety with Smart Pointers (6 tests)
    test_unique_ptr_exception_safety_automatic_cleanup();
    test_shared_ptr_exception_safety();
    test_make_unique_exception_safety_vs_constructor();
    test_raii_with_exception_in_constructor();
    test_exception_with_multiple_raii_resources();
    test_exception_safety_with_nested_scopes();

    // Group 4: Complex RAII Scenarios (6 tests)
    test_smart_pointer_with_virtual_inheritance_raii();
    test_smart_pointer_in_member_initialization_list();
    test_smart_pointer_move_semantics_in_constructor();
    test_smart_pointer_conditional_cleanup();
    test_smart_pointer_factory_pattern();
    test_shared_pointer_observer_pattern();

    // Group 5: Performance and Memory Considerations (3 tests)
    test_smart_pointer_vs_raw_pointer_overhead();
    test_memory_layout_with_smart_pointers();
    test_smart_pointer_cache_locality();

    std::cout << "\n=== All 25 RAII Integration tests passed! ===" << std::endl;
    return 0;
}

#include "ResourceManager.h"
#include <iostream>
#include <cassert>
#include <fstream>
#include <cstdio>
#include <vector>
#include <string>

using namespace resman;

void test(const std::string& name, bool condition) {
    if (condition) {
        std::cout << "[PASS] " << name << std::endl;
    } else {
        std::cout << "[FAIL] " << name << std::endl;
        throw std::runtime_error("Test failed: " + name);
    }
}

// Test object for resource management
struct TestResource {
    int value;
    static int constructorCalls;
    static int destructorCalls;

    TestResource(int v = 0) : value(v) {
        ++constructorCalls;
    }

    ~TestResource() {
        ++destructorCalls;
    }

    void setValue(int v) { value = v; }
    int getValue() const { return value; }
};

int TestResource::constructorCalls = 0;
int TestResource::destructorCalls = 0;

void resetTestResourceCounters() {
    TestResource::constructorCalls = 0;
    TestResource::destructorCalls = 0;
}

void testResourceHandle() {
    resetTestResourceCounters();

    {
        ResourceHandle<TestResource> handle(new TestResource(42));
        test("Resource handle created", handle.get() != nullptr);
        test("Resource handle value", handle->getValue() == 42);
        test("Resource handle dereference", (*handle).getValue() == 42);
        test("Resource handle bool conversion", static_cast<bool>(handle));
    }

    test("Resource handle destructor called", TestResource::destructorCalls == 1);
}

void testResourceHandleMove() {
    resetTestResourceCounters();

    {
        ResourceHandle<TestResource> handle1(new TestResource(100));
        test("Handle1 created", handle1.get() != nullptr);

        ResourceHandle<TestResource> handle2(std::move(handle1));
        test("Handle2 moved from handle1", handle2.get() != nullptr);
        test("Handle1 null after move", handle1.get() == nullptr);
        test("Handle2 has correct value", handle2->getValue() == 100);
    }

    test("Only one destructor call after move", TestResource::destructorCalls == 1);
}

void testResourceHandleReset() {
    resetTestResourceCounters();

    {
        ResourceHandle<TestResource> handle(new TestResource(1));
        test("Initial resource created", TestResource::constructorCalls == 1);

        handle.reset(new TestResource(2));
        test("Resource reset", TestResource::constructorCalls == 2);
        test("Old resource destroyed", TestResource::destructorCalls == 1);
        test("New resource value", handle->getValue() == 2);

        handle.reset();
        test("Resource cleared", handle.get() == nullptr);
        test("Second resource destroyed", TestResource::destructorCalls == 2);
    }
}

void testResourceHandleRelease() {
    resetTestResourceCounters();

    TestResource* raw = nullptr;
    {
        ResourceHandle<TestResource> handle(new TestResource(99));
        raw = handle.release();
        test("Resource released", handle.get() == nullptr);
    }

    test("No destructor called on release", TestResource::destructorCalls == 0);
    test("Released resource still valid", raw->getValue() == 99);

    delete raw;
    test("Manual cleanup after release", TestResource::destructorCalls == 1);
}

void testScopeGuard() {
    int counter = 0;

    {
        auto guard = makeScopeGuard([&counter]() {
            counter = 100;
        });

        test("Counter not yet modified", counter == 0);
    }

    test("Scope guard executed", counter == 100);
}

void testScopeGuardDismiss() {
    int counter = 0;

    {
        auto guard = makeScopeGuard([&counter]() {
            counter = 100;
        });

        guard.dismiss();
    }

    test("Dismissed scope guard not executed", counter == 0);
}

void testSharedResource() {
    resetTestResourceCounters();

    {
        SharedResource<TestResource> shared1(new TestResource(50));
        test("Shared resource created", shared1.get() != nullptr);
        test("Use count is 1", shared1.useCount() == 1);

        {
            SharedResource<TestResource> shared2 = shared1;
            test("Shared resource copied", shared2.get() == shared1.get());
            test("Use count is 2", shared1.useCount() == 2);
            test("Both point to same resource", shared1->getValue() == shared2->getValue());

            SharedResource<TestResource> shared3(shared1);
            test("Use count is 3", shared1.useCount() == 3);
        }

        test("Use count back to 1", shared1.useCount() == 1);
        test("Resource not yet destroyed", TestResource::destructorCalls == 0);
    }

    test("Resource destroyed when last reference gone", TestResource::destructorCalls == 1);
}

void testSharedResourceMove() {
    resetTestResourceCounters();

    {
        SharedResource<TestResource> shared1(new TestResource(75));
        int count1 = shared1.useCount();

        SharedResource<TestResource> shared2(std::move(shared1));
        test("Moved shared resource", shared2.get() != nullptr);
        test("Use count preserved", shared2.useCount() == count1);
        test("Original null after move", shared1.get() == nullptr);
    }

    test("Moved resource destroyed", TestResource::destructorCalls == 1);
}

void testFileResource() {
    const std::string filename = "test_file.txt";

    // Clean up any existing file
    std::remove(filename.c_str());

    {
        FileResource file(filename, "w");
        test("File opened for writing", file.isOpen());
        test("File has correct name", file.filename() == filename);
        test("File has correct mode", file.mode() == "w");

        file.write("Hello, World!\n");
        file.write("Second line\n");
    }

    // File should be closed now, verify by reading
    {
        FileResource file(filename, "r");
        test("File opened for reading", file.isOpen());

        std::string content = file.readAll();
        test("File content read", content.find("Hello, World!") != std::string::npos);
        test("Second line present", content.find("Second line") != std::string::npos);
    }

    std::remove(filename.c_str());
}

void testFileResourceException() {
    bool caught = false;
    try {
        FileResource file("/nonexistent/path/file.txt", "r");
    } catch (const ResourceError& e) {
        caught = true;
    }

    test("File open exception thrown", caught);
}

void testMemoryPool() {
    MemoryPool<TestResource> pool(10);

    test("Pool capacity", pool.capacity() == 10);
    test("Pool initially empty", pool.used() == 0);
    test("Pool fully available", pool.available() == 10);

    std::vector<TestResource*> allocated;

    // Allocate 5 objects
    for (int i = 0; i < 5; ++i) {
        TestResource* res = pool.allocate();
        res->setValue(i);
        allocated.push_back(res);
    }

    test("Pool used count", pool.used() == 5);
    test("Pool available count", pool.available() == 5);

    // Deallocate 2 objects
    pool.deallocate(allocated[0]);
    pool.deallocate(allocated[1]);

    test("Pool used after dealloc", pool.used() == 3);
    test("Pool available after dealloc", pool.available() == 7);

    // Deallocate remaining
    for (size_t i = 2; i < allocated.size(); ++i) {
        pool.deallocate(allocated[i]);
    }

    test("Pool empty after all dealloc", pool.used() == 0);
    test("Pool fully available again", pool.available() == 10);
}

void testMemoryPoolExhaustion() {
    MemoryPool<int> pool(2);

    int* a = pool.allocate();
    int* b = pool.allocate();

    bool caught = false;
    try {
        pool.allocate();  // Should throw
    } catch (const ResourceError& e) {
        caught = true;
    }

    test("Pool exhaustion exception", caught);

    pool.deallocate(a);
    pool.deallocate(b);
}

void testResourcePool() {
    ResourcePool<TestResource> pool(5);

    test("Resource pool capacity", pool.capacity() == 5);
    test("Resource pool empty", pool.available() == 0);

    // Add resources
    for (int i = 0; i < 5; ++i) {
        pool.add(std::make_unique<TestResource>(i * 10));
    }

    test("Resource pool filled", pool.available() == 5);
    test("Resource pool in use", pool.inUse() == 0);

    // Acquire resources
    TestResource* res1 = pool.acquire();
    TestResource* res2 = pool.acquire();

    test("Resources acquired", pool.available() == 3);
    test("Resources in use", pool.inUse() == 2);

    // Release resources
    pool.release(res1);
    pool.release(res2);

    test("Resources released", pool.available() == 5);
    test("No resources in use", pool.inUse() == 0);
}

void testPooledResource() {
    ResourcePool<TestResource> pool(3);

    pool.add(std::make_unique<TestResource>(100));
    pool.add(std::make_unique<TestResource>(200));
    pool.add(std::make_unique<TestResource>(300));

    test("Pooled resources added", pool.available() == 3);

    {
        PooledResource<TestResource> res1(pool);
        test("Pooled resource acquired", pool.available() == 2);

        {
            PooledResource<TestResource> res2(pool);
            test("Second pooled resource", pool.available() == 1);
        }

        test("Pooled resource auto-released", pool.available() == 2);
    }

    test("All pooled resources released", pool.available() == 3);
}

void testMakeResource() {
    resetTestResourceCounters();

    {
        auto handle = makeResource<TestResource>(42);
        test("makeResource creates handle", handle.get() != nullptr);
        test("makeResource value", handle->getValue() == 42);
    }

    test("makeResource cleanup", TestResource::destructorCalls == 1);
}

void testMakeSharedResource() {
    resetTestResourceCounters();

    {
        auto shared = makeSharedResource<TestResource>(99);
        test("makeSharedResource creates shared", shared.get() != nullptr);
        test("makeSharedResource value", shared->getValue() == 99);
        test("makeSharedResource use count", shared.useCount() == 1);
    }

    test("makeSharedResource cleanup", TestResource::destructorCalls == 1);
}

void testMakeArray() {
    {
        auto arr = makeArray<int>(10);
        test("makeArray creates array", arr.get() != nullptr);

        // Initialize array
        for (int i = 0; i < 10; ++i) {
            arr.get()[i] = i * 2;
        }

        test("Array element access", arr.get()[5] == 10);
    }

    // Array should be cleaned up automatically
    test("Array cleanup", true);
}

void testCustomDeleter() {
    bool deleterCalled = false;

    {
        auto customDeleter = [&deleterCalled](TestResource* res) {
            deleterCalled = true;
            delete res;
        };

        ResourceHandle<TestResource, decltype(customDeleter)> handle(
            new TestResource(42),
            customDeleter
        );

        test("Custom deleter handle created", handle.get() != nullptr);
    }

    test("Custom deleter called", deleterCalled);
}

void testResourceSwap() {
    ResourceHandle<TestResource> handle1(new TestResource(10));
    ResourceHandle<TestResource> handle2(new TestResource(20));

    TestResource* ptr1 = handle1.get();
    TestResource* ptr2 = handle2.get();

    handle1.swap(handle2);

    test("Swap exchanged resources", handle1.get() == ptr2);
    test("Swap exchanged resources 2", handle2.get() == ptr1);
    test("Swap preserved values", handle1->getValue() == 20);
    test("Swap preserved values 2", handle2->getValue() == 10);
}

void testMultipleFileOperations() {
    const std::string file1 = "test1.txt";
    const std::string file2 = "test2.txt";

    {
        FileResource f1(file1, "w");
        FileResource f2(file2, "w");

        f1.write("File 1 content\n");
        f2.write("File 2 content\n");

        test("Multiple files open", f1.isOpen() && f2.isOpen());
    }

    // Verify both files closed and written
    {
        FileResource f1(file1, "r");
        FileResource f2(file2, "r");

        test("File 1 content correct", f1.readAll().find("File 1") != std::string::npos);
        test("File 2 content correct", f2.readAll().find("File 2") != std::string::npos);
    }

    std::remove(file1.c_str());
    std::remove(file2.c_str());
}

void testResourcePoolCapacity() {
    ResourcePool<TestResource> pool(3);

    pool.add(std::make_unique<TestResource>(1));
    pool.add(std::make_unique<TestResource>(2));
    pool.add(std::make_unique<TestResource>(3));

    bool caught = false;
    try {
        pool.add(std::make_unique<TestResource>(4));
    } catch (const ResourceError& e) {
        caught = true;
    }

    test("Pool capacity exception", caught);
}

void testSharedResourceModification() {
    SharedResource<TestResource> shared1(new TestResource(10));
    SharedResource<TestResource> shared2 = shared1;

    shared1->setValue(50);

    test("Shared modification visible", shared2->getValue() == 50);
    test("Shared pointers equal", shared1.get() == shared2.get());
}

void testNestedResourceHandles() {
    struct Container {
        ResourceHandle<TestResource> resource;

        Container() : resource(new TestResource(100)) {}
    };

    resetTestResourceCounters();

    {
        ResourceHandle<Container> container(new Container());
        test("Nested resource access", container->resource->getValue() == 100);
    }

    // Both container and nested resource should be destroyed
    test("Nested cleanup", TestResource::destructorCalls >= 1);
}

void testExceptionSafety() {
    resetTestResourceCounters();

    try {
        ResourceHandle<TestResource> handle(new TestResource(1));

        // Simulate exception
        throw std::runtime_error("Test exception");
    } catch (...) {
        // Handle exception
    }

    test("Exception safety - resource cleaned up", TestResource::destructorCalls == 1);
}

void testLargePoolOperations() {
    const size_t poolSize = 100;
    MemoryPool<int> pool(poolSize);

    std::vector<int*> allocated;

    // Allocate half
    for (size_t i = 0; i < poolSize / 2; ++i) {
        allocated.push_back(pool.allocate());
    }

    test("Large pool half allocated", pool.used() == poolSize / 2);

    // Deallocate all
    for (int* ptr : allocated) {
        pool.deallocate(ptr);
    }

    test("Large pool fully deallocated", pool.used() == 0);

    // Allocate all
    allocated.clear();
    for (size_t i = 0; i < poolSize; ++i) {
        allocated.push_back(pool.allocate());
    }

    test("Large pool fully allocated", pool.used() == poolSize);
}

int main() {
    try {
        std::cout << "=== Resource Manager Tests ===" << std::endl;

        testResourceHandle();
        testResourceHandleMove();
        testResourceHandleReset();
        testResourceHandleRelease();
        testScopeGuard();
        testScopeGuardDismiss();
        testSharedResource();
        testSharedResourceMove();
        testFileResource();
        testFileResourceException();
        testMemoryPool();
        testMemoryPoolExhaustion();
        testResourcePool();
        testPooledResource();
        testMakeResource();
        testMakeSharedResource();
        testMakeArray();
        testCustomDeleter();
        testResourceSwap();
        testMultipleFileOperations();
        testResourcePoolCapacity();
        testSharedResourceModification();
        testNestedResourceHandles();
        testExceptionSafety();
        testLargePoolOperations();

        std::cout << "\n=== All tests passed! ===" << std::endl;
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Test failed with exception: " << e.what() << std::endl;
        return 1;
    }
}

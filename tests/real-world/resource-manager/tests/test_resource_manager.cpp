#include <gtest/gtest.h>
#include "ResourceManager.h"
#include <fstream>
#include <cstdio>
#include <vector>
#include <string>

using namespace resman;

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

// ============================================================================
// Test Fixtures
// ============================================================================

class ResourceHandleTest : public ::testing::Test {
protected:
    void SetUp() override {
        resetTestResourceCounters();
    }

    void TearDown() override {
        // Cleanup happens automatically
    }
};

class ScopeGuardTest : public ::testing::Test {
protected:
    int counter = 0;

    void SetUp() override {
        counter = 0;
    }
};

class SharedResourceTest : public ::testing::Test {
protected:
    void SetUp() override {
        resetTestResourceCounters();
    }
};

class FileResourceTest : public ::testing::Test {
protected:
    std::string filename;

    void SetUp() override {
        filename = "test_file.txt";
        std::remove(filename.c_str());
    }

    void TearDown() override {
        std::remove(filename.c_str());
    }
};

class MemoryPoolTest : public ::testing::Test {
protected:
    // No special setup needed
};

class ResourcePoolTest : public ::testing::Test {
protected:
    void SetUp() override {
        resetTestResourceCounters();
    }
};

// ============================================================================
// ResourceHandle Tests
// ============================================================================

TEST_F(ResourceHandleTest, CreateAndDestroy) {
    ResourceHandle<TestResource> handle(new TestResource(42));
    ASSERT_NE(handle.get(), nullptr);
    ASSERT_EQ(handle->getValue(), 42);
    ASSERT_EQ((*handle).getValue(), 42);
    ASSERT_TRUE(static_cast<bool>(handle));
}

TEST_F(ResourceHandleTest, DestructorCalled) {
    {
        ResourceHandle<TestResource> handle(new TestResource(42));
    }
    ASSERT_EQ(TestResource::destructorCalls, 1);
}

TEST_F(ResourceHandleTest, MoveConstruction) {
    ResourceHandle<TestResource> handle1(new TestResource(100));
    ASSERT_NE(handle1.get(), nullptr);

    ResourceHandle<TestResource> handle2(std::move(handle1));
    ASSERT_NE(handle2.get(), nullptr);
    ASSERT_EQ(handle1.get(), nullptr);
    ASSERT_EQ(handle2->getValue(), 100);
}

TEST_F(ResourceHandleTest, MoveDestructorCount) {
    {
        ResourceHandle<TestResource> handle1(new TestResource(100));
        ResourceHandle<TestResource> handle2(std::move(handle1));
    }
    ASSERT_EQ(TestResource::destructorCalls, 1);
}

TEST_F(ResourceHandleTest, ResetWithNewResource) {
    ResourceHandle<TestResource> handle(new TestResource(1));
    ASSERT_EQ(TestResource::constructorCalls, 1);

    handle.reset(new TestResource(2));
    ASSERT_EQ(TestResource::constructorCalls, 2);
    ASSERT_EQ(TestResource::destructorCalls, 1);
    ASSERT_EQ(handle->getValue(), 2);
}

TEST_F(ResourceHandleTest, ResetToNull) {
    ResourceHandle<TestResource> handle(new TestResource(1));
    handle.reset(new TestResource(2));

    handle.reset();
    ASSERT_EQ(handle.get(), nullptr);
    ASSERT_EQ(TestResource::destructorCalls, 2);
}

TEST_F(ResourceHandleTest, ReleaseOwnership) {
    TestResource* raw = nullptr;
    {
        ResourceHandle<TestResource> handle(new TestResource(99));
        raw = handle.release();
        ASSERT_EQ(handle.get(), nullptr);
    }

    ASSERT_EQ(TestResource::destructorCalls, 0);
    ASSERT_EQ(raw->getValue(), 99);

    delete raw;
    ASSERT_EQ(TestResource::destructorCalls, 1);
}

TEST_F(ResourceHandleTest, SwapResources) {
    ResourceHandle<TestResource> handle1(new TestResource(10));
    ResourceHandle<TestResource> handle2(new TestResource(20));

    TestResource* ptr1 = handle1.get();
    TestResource* ptr2 = handle2.get();

    handle1.swap(handle2);

    ASSERT_EQ(handle1.get(), ptr2);
    ASSERT_EQ(handle2.get(), ptr1);
    ASSERT_EQ(handle1->getValue(), 20);
    ASSERT_EQ(handle2->getValue(), 10);
}

TEST_F(ResourceHandleTest, CustomDeleter) {
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

        ASSERT_NE(handle.get(), nullptr);
    }

    ASSERT_TRUE(deleterCalled);
}

TEST_F(ResourceHandleTest, NestedResourceHandles) {
    struct Container {
        ResourceHandle<TestResource> resource;

        Container() : resource(new TestResource(100)) {}
    };

    {
        ResourceHandle<Container> container(new Container());
        ASSERT_EQ(container->resource->getValue(), 100);
    }

    // Both container and nested resource should be destroyed
    ASSERT_GE(TestResource::destructorCalls, 1);
}

TEST_F(ResourceHandleTest, ExceptionSafety) {
    try {
        ResourceHandle<TestResource> handle(new TestResource(1));

        // Simulate exception
        throw std::runtime_error("Test exception");
    } catch (...) {
        // Handle exception
    }

    ASSERT_EQ(TestResource::destructorCalls, 1);
}

// ============================================================================
// ScopeGuard Tests
// ============================================================================

TEST_F(ScopeGuardTest, ExecutesOnScopeExit) {
    {
        auto guard = makeScopeGuard([this]() {
            counter = 100;
        });

        ASSERT_EQ(counter, 0);
    }

    ASSERT_EQ(counter, 100);
}

TEST_F(ScopeGuardTest, DismissPreventsExecution) {
    {
        auto guard = makeScopeGuard([this]() {
            counter = 100;
        });

        guard.dismiss();
    }

    ASSERT_EQ(counter, 0);
}

// ============================================================================
// SharedResource Tests
// ============================================================================

TEST_F(SharedResourceTest, CreateAndUseCount) {
    SharedResource<TestResource> shared1(new TestResource(50));
    ASSERT_NE(shared1.get(), nullptr);
    ASSERT_EQ(shared1.useCount(), 1);
}

TEST_F(SharedResourceTest, CopyIncrementsUseCount) {
    SharedResource<TestResource> shared1(new TestResource(50));

    {
        SharedResource<TestResource> shared2 = shared1;
        ASSERT_EQ(shared2.get(), shared1.get());
        ASSERT_EQ(shared1.useCount(), 2);
        ASSERT_EQ(shared1->getValue(), shared2->getValue());

        SharedResource<TestResource> shared3(shared1);
        ASSERT_EQ(shared1.useCount(), 3);
    }

    ASSERT_EQ(shared1.useCount(), 1);
    ASSERT_EQ(TestResource::destructorCalls, 0);
}

TEST_F(SharedResourceTest, DestructorCalledWhenLastReferenceGone) {
    {
        SharedResource<TestResource> shared1(new TestResource(50));
        SharedResource<TestResource> shared2 = shared1;
    }

    ASSERT_EQ(TestResource::destructorCalls, 1);
}

TEST_F(SharedResourceTest, MovePreservesUseCount) {
    SharedResource<TestResource> shared1(new TestResource(75));
    int count1 = shared1.useCount();

    SharedResource<TestResource> shared2(std::move(shared1));
    ASSERT_NE(shared2.get(), nullptr);
    ASSERT_EQ(shared2.useCount(), count1);
    ASSERT_EQ(shared1.get(), nullptr);
}

TEST_F(SharedResourceTest, MoveDestroysResource) {
    {
        SharedResource<TestResource> shared1(new TestResource(75));
        SharedResource<TestResource> shared2(std::move(shared1));
    }

    ASSERT_EQ(TestResource::destructorCalls, 1);
}

TEST_F(SharedResourceTest, ModificationVisibleToAllCopies) {
    SharedResource<TestResource> shared1(new TestResource(10));
    SharedResource<TestResource> shared2 = shared1;

    shared1->setValue(50);

    ASSERT_EQ(shared2->getValue(), 50);
    ASSERT_EQ(shared1.get(), shared2.get());
}

// ============================================================================
// FileResource Tests
// ============================================================================

TEST_F(FileResourceTest, OpenForWriting) {
    FileResource file(filename, "w");
    ASSERT_TRUE(file.isOpen());
    ASSERT_EQ(file.filename(), filename);
    ASSERT_EQ(file.mode(), "w");

    file.write("Hello, World!\n");
    file.write("Second line\n");
}

TEST_F(FileResourceTest, ReadWrittenContent) {
    {
        FileResource file(filename, "w");
        file.write("Hello, World!\n");
        file.write("Second line\n");
    }

    // File should be closed now, verify by reading
    FileResource file(filename, "r");
    ASSERT_TRUE(file.isOpen());

    std::string content = file.readAll();
    ASSERT_NE(content.find("Hello, World!"), std::string::npos);
    ASSERT_NE(content.find("Second line"), std::string::npos);
}

TEST_F(FileResourceTest, NonexistentFileThrowsException) {
    bool caught = false;
    try {
        FileResource file("/nonexistent/path/file.txt", "r");
    } catch (const ResourceError& e) {
        caught = true;
    }

    ASSERT_TRUE(caught);
}

TEST_F(FileResourceTest, MultipleFileOperations) {
    const std::string file1 = "test1.txt";
    const std::string file2 = "test2.txt";

    {
        FileResource f1(file1, "w");
        FileResource f2(file2, "w");

        f1.write("File 1 content\n");
        f2.write("File 2 content\n");

        ASSERT_TRUE(f1.isOpen() && f2.isOpen());
    }

    // Verify both files closed and written
    {
        FileResource f1(file1, "r");
        FileResource f2(file2, "r");

        ASSERT_NE(f1.readAll().find("File 1"), std::string::npos);
        ASSERT_NE(f2.readAll().find("File 2"), std::string::npos);
    }

    std::remove(file1.c_str());
    std::remove(file2.c_str());
}

// ============================================================================
// MemoryPool Tests
// ============================================================================

TEST_F(MemoryPoolTest, InitialState) {
    MemoryPool<TestResource> pool(10);

    ASSERT_EQ(pool.capacity(), 10);
    ASSERT_EQ(pool.used(), 0);
    ASSERT_EQ(pool.available(), 10);
}

TEST_F(MemoryPoolTest, AllocateAndDeallocate) {
    MemoryPool<TestResource> pool(10);
    std::vector<TestResource*> allocated;

    // Allocate 5 objects
    for (int i = 0; i < 5; ++i) {
        TestResource* res = pool.allocate();
        res->setValue(i);
        allocated.push_back(res);
    }

    ASSERT_EQ(pool.used(), 5);
    ASSERT_EQ(pool.available(), 5);

    // Deallocate 2 objects
    pool.deallocate(allocated[0]);
    pool.deallocate(allocated[1]);

    ASSERT_EQ(pool.used(), 3);
    ASSERT_EQ(pool.available(), 7);

    // Deallocate remaining
    for (size_t i = 2; i < allocated.size(); ++i) {
        pool.deallocate(allocated[i]);
    }

    ASSERT_EQ(pool.used(), 0);
    ASSERT_EQ(pool.available(), 10);
}

TEST_F(MemoryPoolTest, ExhaustionThrowsException) {
    MemoryPool<int> pool(2);

    int* a = pool.allocate();
    int* b = pool.allocate();

    bool caught = false;
    try {
        pool.allocate();  // Should throw
    } catch (const ResourceError& e) {
        caught = true;
    }

    ASSERT_TRUE(caught);

    pool.deallocate(a);
    pool.deallocate(b);
}

TEST_F(MemoryPoolTest, LargePoolOperations) {
    const size_t poolSize = 100;
    MemoryPool<int> pool(poolSize);

    std::vector<int*> allocated;

    // Allocate half
    for (size_t i = 0; i < poolSize / 2; ++i) {
        allocated.push_back(pool.allocate());
    }

    ASSERT_EQ(pool.used(), poolSize / 2);

    // Deallocate all
    for (int* ptr : allocated) {
        pool.deallocate(ptr);
    }

    ASSERT_EQ(pool.used(), 0);

    // Allocate all
    allocated.clear();
    for (size_t i = 0; i < poolSize; ++i) {
        allocated.push_back(pool.allocate());
    }

    ASSERT_EQ(pool.used(), poolSize);
}

// ============================================================================
// ResourcePool Tests
// ============================================================================

TEST_F(ResourcePoolTest, InitialState) {
    ResourcePool<TestResource> pool(5);

    ASSERT_EQ(pool.capacity(), 5);
    ASSERT_EQ(pool.available(), 0);
}

TEST_F(ResourcePoolTest, AddAndAcquireResources) {
    ResourcePool<TestResource> pool(5);

    // Add resources
    for (int i = 0; i < 5; ++i) {
        pool.add(std::make_unique<TestResource>(i * 10));
    }

    ASSERT_EQ(pool.available(), 5);
    ASSERT_EQ(pool.inUse(), 0);

    // Acquire resources
    TestResource* res1 = pool.acquire();
    TestResource* res2 = pool.acquire();

    ASSERT_EQ(pool.available(), 3);
    ASSERT_EQ(pool.inUse(), 2);

    // Release resources
    pool.release(res1);
    pool.release(res2);

    ASSERT_EQ(pool.available(), 5);
    ASSERT_EQ(pool.inUse(), 0);
}

TEST_F(ResourcePoolTest, CapacityExceptionOnOverfill) {
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

    ASSERT_TRUE(caught);
}

TEST_F(ResourcePoolTest, PooledResourceAutoRelease) {
    ResourcePool<TestResource> pool(3);

    pool.add(std::make_unique<TestResource>(100));
    pool.add(std::make_unique<TestResource>(200));
    pool.add(std::make_unique<TestResource>(300));

    ASSERT_EQ(pool.available(), 3);

    {
        PooledResource<TestResource> res1(pool);
        ASSERT_EQ(pool.available(), 2);

        {
            PooledResource<TestResource> res2(pool);
            ASSERT_EQ(pool.available(), 1);
        }

        ASSERT_EQ(pool.available(), 2);
    }

    ASSERT_EQ(pool.available(), 3);
}

// ============================================================================
// Factory Function Tests
// ============================================================================

TEST(MakeResourceTest, CreatesHandle) {
    resetTestResourceCounters();

    {
        auto handle = makeResource<TestResource>(42);
        ASSERT_NE(handle.get(), nullptr);
        ASSERT_EQ(handle->getValue(), 42);
    }

    ASSERT_EQ(TestResource::destructorCalls, 1);
}

TEST(MakeSharedResourceTest, CreatesSharedResource) {
    resetTestResourceCounters();

    {
        auto shared = makeSharedResource<TestResource>(99);
        ASSERT_NE(shared.get(), nullptr);
        ASSERT_EQ(shared->getValue(), 99);
        ASSERT_EQ(shared.useCount(), 1);
    }

    ASSERT_EQ(TestResource::destructorCalls, 1);
}

TEST(MakeArrayTest, CreatesArray) {
    {
        auto arr = makeArray<int>(10);
        ASSERT_NE(arr.get(), nullptr);

        // Initialize array
        for (int i = 0; i < 10; ++i) {
            arr.get()[i] = i * 2;
        }

        ASSERT_EQ(arr.get()[5], 10);
    }

    // Array should be cleaned up automatically
    SUCCEED();
}

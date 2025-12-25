// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/resource-manager/tests/test_resource_manager.cpp
// Implementation file

#include "test_resource_manager.h"

namespace resman {
        class ResourceError {
        public:
                explicit ResourceError(const int &message) {
                }
        };
        template <typename T> class IResource {
        public:
                virtual ~IResource<T>() = default;
                virtual T &get() = 0;
                virtual const T &get() const = 0;
                virtual bool isValid() const = 0;
                virtual void release() = 0;
        };
        template <typename T, typename Deleter> class ResourceHandle {
        private:
                T *resource_;
                Deleter deleter_;
                bool owns_;
        public:
                explicit ResourceHandle<T, Deleter>(T *resource = nullptr, Deleter deleter = Deleter()) : resource_(resource), owns_(true) {
                }
                ResourceHandle<T, Deleter>(ResourceHandle<T, Deleter> &&other) noexcept : resource_(other.resource_), owns_(other.owns_) {
                        other.resource_ = nullptr;
                        other.owns_ = false;
                }
                ResourceHandle<T, Deleter> &operator=(ResourceHandle<T, Deleter> &&other) noexcept {
                        if (this != &other) {
                                this->reset();
                                this->resource_ = other.resource_;
                                this->owns_ = other.owns_;
                                other.resource_ = nullptr;
                                other.owns_ = false;
                        }
                        return *this;
                }
                ResourceHandle<T, Deleter>(const ResourceHandle<T, Deleter> &) = delete;
                ResourceHandle<T, Deleter> &operator=(const ResourceHandle<T, Deleter> &) = delete;
                ~ResourceHandle<T, Deleter>() {
                        this->reset();
                }
                void reset(T *newResource = nullptr) {
                        if (this->resource_ && this->owns_) {
                                this->deleter_(this->resource_);
                        }
                        this->resource_ = newResource;
                        this->owns_ = (newResource != nullptr);
                }
                T *release() {
                        T *temp = this->resource_;
                        this->resource_ = nullptr;
                        this->owns_ = false;
                        return temp;
                }
                T *get() const {
                        return this->resource_;
                }
                T &operator*() const {
                        if (!this->resource_) {
                                throw <recovery-expr>("Dereferencing null resource");
                        }
                        return *this->resource_;
                }
                T *operator->() const {
                        if (!this->resource_) {
                                throw <recovery-expr>("Accessing null resource");
                        }
                        return this->resource_;
                }
                explicit operator bool() const {
                        return this->resource_ != nullptr;
                }
                void swap(ResourceHandle<T, Deleter> &other) noexcept {
                }
        };
        template <typename Func> class ScopeGuard {
        private:
                Func func_;
                bool active_;
        public:
                explicit ScopeGuard<Func>(Func func) : active_(true) {
                }
                ~ScopeGuard<Func>() {
                        if (this->active_) {
                                try {
                                        this->func_();
                                } catch (...) {
                                }
                        }
                }
                void dismiss() {
                        this->active_ = false;
                }
                ScopeGuard<Func>(const ScopeGuard<Func> &) = delete;
                ScopeGuard<Func> &operator=(const ScopeGuard<Func> &) = delete;
                ScopeGuard<Func>(ScopeGuard<Func> &&) = delete;
                ScopeGuard<Func> &operator=(ScopeGuard<Func> &&) = delete;
        };
        template <typename Func> ScopeGuard<Func> makeScopeGuard(Func func) {
        }
        class RefCounter {
        private:
                int *count_;
        public:
                RefCounter() : count_(new int(1)) {
                }
                RefCounter(const RefCounter &other) : count_(other.count_) {
                        if (this->count_) {
                                ++(*this->count_);
                        }
                }
                RefCounter(RefCounter &&other) noexcept : count_(other.count_) {
                        other.count_ = nullptr;
                }
                RefCounter &operator=(const RefCounter &other) {
                        if (this != &other) {
                                this->release();
                                this->count_ = other.count_;
                                if (this->count_) {
                                        ++(*this->count_);
                                }
                        }
                        return *this;
                }
                RefCounter &operator=(RefCounter &&other) noexcept {
                        if (this != &other) {
                                this->release();
                                this->count_ = other.count_;
                                other.count_ = nullptr;
                        }
                        return *this;
                }
                ~RefCounter() noexcept {
                        this->release();
                }
                int count() const {
                        return this->count_ ? *this->count_ : 0;
                }
                void release() {
                        if (this->count_) {
                                if (--(*this->count_) == 0) {
                                        delete this->count_;
                                }
                                this->count_ = nullptr;
                        }
                }
        };
        template <typename T, typename Deleter> class SharedResource {
        private:
                T *resource_;
                RefCounter refCount_;
                Deleter deleter_;
        public:
                explicit SharedResource<T, Deleter>(T *resource = nullptr, Deleter deleter = Deleter()) : resource_(resource), refCount_() {
                }
                SharedResource<T, Deleter>(const SharedResource<T, Deleter> &other) : resource_(other.resource_), refCount_(other.refCount_), deleter_(other.deleter_) {
                }
                SharedResource<T, Deleter>(SharedResource<T, Deleter> &&other) noexcept : resource_(other.resource_) {
                        other.resource_ = nullptr;
                }
                SharedResource<T, Deleter> &operator=(const SharedResource<T, Deleter> &other) {
                        if (this != &other) {
                                this->reset();
                                this->resource_ = other.resource_;
                                this->refCount_ = other.refCount_;
                                this->deleter_ = other.deleter_;
                        }
                        return *this;
                }
                SharedResource<T, Deleter> &operator=(SharedResource<T, Deleter> &&other) noexcept {
                        if (this != &other) {
                                this->reset();
                                this->resource_ = other.resource_;
                                other.resource_ = nullptr;
                        }
                        return *this;
                }
                ~SharedResource<T, Deleter>() {
                        this->reset();
                }
                void reset(T *newResource = nullptr) {
                        if (this->resource_ && this->refCount_.count() == 1) {
                                this->deleter_(this->resource_);
                        }
                        this->resource_ = newResource;
                        if (newResource) {
                                this->refCount_ = RefCounter();
                        }
                }
                T *get() const {
                        return this->resource_;
                }
                T &operator*() const {
                        if (!this->resource_) {
                                throw <recovery-expr>("Dereferencing null shared resource");
                        }
                        return *this->resource_;
                }
                T *operator->() const {
                        if (!this->resource_) {
                                throw <recovery-expr>("Accessing null shared resource");
                        }
                        return this->resource_;
                }
                explicit operator bool() const {
                        return this->resource_ != nullptr;
                }
                int useCount() const {
                        return this->refCount_.count();
                }
        };
        struct FileDeleter {
                void operator()(int *file) const {
                        if (<recovery-expr>(file)) {
                                int (file);
                        }
                }
        };
        struct MemoryDeleter {
                void operator()(void *ptr) const {
                        if (ptr) {
                                int (ptr);
                        }
                }
        };
        template <typename T> struct ArrayDeleter {
                void operator()(T *ptr) const {
                        if (ptr) {
                                delete [] ptr;
                        }
                }
        };
        using MemoryHandle = ResourceHandle<void, MemoryDeleter>;
        template <typename T> using ArrayHandle = ResourceHandle<T, ArrayDeleter<T> >;
        class FileResource {
        private:
                int handle_;
                int filename_;
                int mode_;
        public:
                FileResource(const int &filename, const int &mode) {
                        int *file;
                        if (!<recovery-expr>()) {
                                throw ResourceError("Failed to open file: " + <recovery-expr>());
                        }
                }
                int *get() const {
                }
                bool isOpen() const {
                }
                void close() {
                }
                const int &filename() const {
                }
                const int &mode() const {
                }
                void write(const int &data) {
                        if (!this->isOpen()) {
                                throw <recovery-expr>("File not open");
                        }
                }
                int readAll() {
                        if (!this->isOpen()) {
                                throw <recovery-expr>("File not open");
                        }
                        long size;
                }
        };
        template <typename T> class MemoryPool {
        private:
                struct Block {
                        T data;
                        bool inUse;
                        Block *next;
                        Block() : inUse(false), next(nullptr) {
                        }
                };
                int blocks_;
                Block *freeList_;
                int capacity_;
                int used_;
        public:
                explicit MemoryPool<T>(int capacity = 100) : freeList_(nullptr) {
                        for (int i = <recovery-expr>(0); <recovery-expr>() < <recovery-expr>(); ++<recovery-expr>()) {
                                Block *block = new Block();
                                block->next = this->freeList_;
                                this->freeList_ = block;
                        }
                }
                ~MemoryPool<T>() {
                }
                T *allocate() {
                        if (!this->freeList_) {
                                throw <recovery-expr>("Memory pool exhausted");
                        }
                        Block *block = this->freeList_;
                        this->freeList_ = block->next;
                        block->inUse = true;
                        block->next = nullptr;
                        return &block->data;
                }
                void deallocate(T *ptr) {
                        if (!ptr)
                                return;
                        Block *block = reinterpret_cast<Block *>(reinterpret_cast<char *>(ptr) - <recovery-expr>(offsetof));
                        if (!block->inUse) {
                                throw <recovery-expr>("Double free detected");
                        }
                        block->inUse = false;
                        block->next = this->freeList_;
                        this->freeList_ = block;
                }
                int capacity() const {
                }
                int used() const {
                }
                int available() const {
                }
                MemoryPool<T>(const MemoryPool<T> &) = delete;
                MemoryPool<T> &operator=(const MemoryPool<T> &) = delete;
        };
        template <typename T> class ResourcePool {
        private:
                int available_;
                int capacity_;
        public:
                explicit ResourcePool<T>(int capacity) {
                }
                virtual ~ResourcePool<T>() = default;
                void add(int resource) {
                        if (<recovery-expr>()) {
                                throw <recovery-expr>("Resource pool at capacity");
                        }
                }
                T *acquire() {
                        if (<recovery-expr>()) {
                                throw <recovery-expr>("No available resources in pool");
                        }
                        T *resource;
                        return resource;
                }
                void release(T *resource) {
                        if (!resource)
                                return;
                        bool found = false;
                        if (!found) {
                                throw <recovery-expr>("Resource does not belong to this pool");
                        }
                }
                int capacity() const {
                }
                int available() const {
                }
                int inUse() const {
                }
        };
        template <typename T> class PooledResource {
        private:
                ResourcePool<T> *pool_;
                T *resource_;
        public:
                PooledResource<T>(ResourcePool<T> &pool) : pool_(&pool), resource_(pool.acquire()) {
                }
                ~PooledResource<T>() {
                        if (this->pool_ && this->resource_) {
                                this->pool_->release(this->resource_);
                        }
                }
                PooledResource<T>(PooledResource<T> &&other) noexcept : pool_(other.pool_), resource_(other.resource_) {
                        other.pool_ = nullptr;
                        other.resource_ = nullptr;
                }
                PooledResource<T> &operator=(PooledResource<T> &&other) noexcept {
                        if (this != &other) {
                                if (this->pool_ && this->resource_) {
                                        this->pool_->release(this->resource_);
                                }
                                this->pool_ = other.pool_;
                                this->resource_ = other.resource_;
                                other.pool_ = nullptr;
                                other.resource_ = nullptr;
                        }
                        return *this;
                }
                PooledResource<T>(const PooledResource<T> &) = delete;
                PooledResource<T> &operator=(const PooledResource<T> &) = delete;
                T *get() const {
                        return this->resource_;
                }
                T &operator*() const {
                        return *this->resource_;
                }
                T *operator->() const {
                        return this->resource_;
                }
        };
        template <typename T, typename ...Args> int makeResource(Args &&...args) {
        }
        template <typename T, typename ...Args> int makeSharedResource(Args &&...args) {
        }
        inline FileResource openFile(const int &filename, const int &mode) {
                return FileResource(<recovery-expr>(), <recovery-expr>());
        }
        template <typename T> int makeArray(int size) {
        }
}
using namespace resman
struct TestResource {
        int value;
        static int constructorCalls;
        static int destructorCalls;
        TestResource(int v = 0) : value(v) {
                ++constructorCalls;
        }
        ~TestResource() noexcept {
                ++destructorCalls;
        }
        void setValue(int v) {
                this->value = v;
        }
        int getValue() const {
                return this->value;
        }
};
int constructorCalls = 0
int destructorCalls = 0
void resetTestResourceCounters() {
        TestResource::constructorCalls = 0;
        TestResource::destructorCalls = 0;
}

class ResourceHandleTest {
protected:
        void SetUp() {
                resetTestResourceCounters();
        }
        void TearDown() {
        }
};
class ScopeGuardTest {
protected:
        int counter = 0;
        void SetUp() {
                this->counter = 0;
        }
};
class SharedResourceTest {
protected:
        void SetUp() {
                resetTestResourceCounters();
        }
};
class FileResourceTest {
protected:
        int filename;
        void SetUp() {
        }
        void TearDown() {
        }
};
class MemoryPoolTest {
protected:
};
class ResourcePoolTest {
protected:
        void SetUp() {
                resetTestResourceCounters();
        }
};
int TEST_F(ResourceHandleTest, int) {
        int handle = <recovery-expr>((new TestResource(42)));
        ASSERT_NE(<recovery-expr>().get(), nullptr);
        ASSERT_EQ(<recovery-expr>()->getValue(), 42);
        ASSERT_EQ((*<recovery-expr>()).getValue(), 42);
        <recovery-expr>(ASSERT_TRUE, static_cast<bool>(<recovery-expr>()));
}

int TEST_F(ResourceHandleTest, int) {
        {
                int handle = <recovery-expr>((new TestResource(42)));
        }
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 1);
}

int TEST_F(ResourceHandleTest, int) {
        int handle1 = <recovery-expr>((new TestResource(100)));
        ASSERT_NE(<recovery-expr>().get(), nullptr);
        int handle2(int (handle1));
        ASSERT_NE(<recovery-expr>().get(), nullptr);
        ASSERT_EQ(<recovery-expr>().get(), nullptr);
        ASSERT_EQ(<recovery-expr>()->getValue(), 100);
}

int TEST_F(ResourceHandleTest, int) {
        {
                int handle1 = <recovery-expr>((new TestResource(100)));
                int handle2(int (handle1));
        }
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 1);
}

int TEST_F(ResourceHandleTest, int) {
        int handle = <recovery-expr>((new TestResource(1)));
        <recovery-expr>(ASSERT_EQ, TestResource::constructorCalls, 1);
        <recovery-expr>(handle).reset(new TestResource(2));
        <recovery-expr>(ASSERT_EQ, TestResource::constructorCalls, 2);
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 1);
        ASSERT_EQ(<recovery-expr>()->getValue(), 2);
}

int TEST_F(ResourceHandleTest, int) {
        int handle = <recovery-expr>((new TestResource(1)));
        <recovery-expr>(handle).reset(new TestResource(2));
        <recovery-expr>(handle).reset();
        ASSERT_EQ(<recovery-expr>().get(), nullptr);
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 2);
}

int TEST_F(ResourceHandleTest, int) {
        TestResource *raw = nullptr;
        {
                int handle = <recovery-expr>((new TestResource(99)));
                raw = <recovery-expr>().release();
                ASSERT_EQ(<recovery-expr>().get(), nullptr);
        }
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 0);
        <recovery-expr>(ASSERT_EQ, raw->getValue(), 99);
        delete raw;
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 1);
}

int TEST_F(ResourceHandleTest, int) {
        int handle1 = <recovery-expr>((new TestResource(10)));
        int handle2 = <recovery-expr>((new TestResource(20)));
        TestResource *ptr1 = <recovery-expr>().get();
        TestResource *ptr2 = <recovery-expr>().get();
        <recovery-expr>(handle1).swap(<recovery-expr>());
        ASSERT_EQ(<recovery-expr>().get(), ptr2);
        ASSERT_EQ(<recovery-expr>().get(), ptr1);
        ASSERT_EQ(<recovery-expr>()->getValue(), 20);
        ASSERT_EQ(<recovery-expr>()->getValue(), 10);
}

int TEST_F(ResourceHandleTest, int) {
        bool deleterCalled = false;
        {
                auto customDeleter = [&deleterCalled](TestResource *res) {
                        deleterCalled = true;
                        delete res;
                };
                ResourceHandle<TestResource, decltype(customDeleter)> handle;
                ASSERT_NE(<recovery-expr>().get(), nullptr);
        }
        <recovery-expr>(ASSERT_TRUE, deleterCalled);
}

int TEST_F(ResourceHandleTest, int) {
        struct Container {
                int resource;
                Container() {
                }
        };
        {
                int container = <recovery-expr>((new Container()));
                ASSERT_EQ(<recovery-expr>()->resource->getValue(), 100);
        }
        <recovery-expr>(ASSERT_GE, TestResource::destructorCalls, 1);
}

int TEST_F(ResourceHandleTest, int) {
        try {
                int handle = <recovery-expr>((new TestResource(1)));
        } catch (...) {
        }
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 1);
}

int TEST_F(ScopeGuardTest, int) {
        {
                auto guard = <recovery-expr>(makeScopeGuard, []() {
                });
                <recovery-expr>(ASSERT_EQ, 0);
        }
        <recovery-expr>(ASSERT_EQ, 100);
}

int TEST_F(ScopeGuardTest, int) {
        {
                auto guard = <recovery-expr>(makeScopeGuard, []() {
                });
                <recovery-expr>(guard).dismiss();
        }
        <recovery-expr>(ASSERT_EQ, 0);
}

int TEST_F(SharedResourceTest, int) {
        int shared1 = <recovery-expr>((new TestResource(50)));
        ASSERT_NE(<recovery-expr>().get(), nullptr);
        ASSERT_EQ(<recovery-expr>().useCount(), 1);
}

int TEST_F(SharedResourceTest, int) {
        int shared1 = <recovery-expr>((new TestResource(50)));
        {
                int shared2 = <recovery-expr>(<recovery-expr>());
                ASSERT_EQ(<recovery-expr>().get(), <recovery-expr>().get());
                ASSERT_EQ(<recovery-expr>().useCount(), 2);
                ASSERT_EQ(<recovery-expr>()->getValue(), <recovery-expr>()->getValue());
                int shared3 = <recovery-expr>((<recovery-expr>(shared1)));
                ASSERT_EQ(<recovery-expr>().useCount(), 3);
        }
        ASSERT_EQ(<recovery-expr>().useCount(), 1);
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 0);
}

int TEST_F(SharedResourceTest, int) {
        {
                int shared1 = <recovery-expr>((new TestResource(50)));
                int shared2 = <recovery-expr>(<recovery-expr>());
        }
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 1);
}

int TEST_F(SharedResourceTest, int) {
        int shared1 = <recovery-expr>((new TestResource(75)));
        int count1 = <recovery-expr>().useCount();
        int shared2(int (shared1));
        ASSERT_NE(<recovery-expr>().get(), nullptr);
        ASSERT_EQ(<recovery-expr>().useCount(), count1);
        ASSERT_EQ(<recovery-expr>().get(), nullptr);
}

int TEST_F(SharedResourceTest, int) {
        {
                int shared1 = <recovery-expr>((new TestResource(75)));
                int shared2(int (shared1));
        }
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 1);
}

int TEST_F(SharedResourceTest, int) {
        int shared1 = <recovery-expr>((new TestResource(10)));
        int shared2 = <recovery-expr>(<recovery-expr>());
        <recovery-expr>(shared1)->setValue(50);
        ASSERT_EQ(<recovery-expr>()->getValue(), 50);
        ASSERT_EQ(<recovery-expr>().get(), <recovery-expr>().get());
}

int TEST_F(FileResourceTest, int) {
        FileResource file;
        <recovery-expr>(ASSERT_TRUE, file.isOpen());
        <recovery-expr>(ASSERT_EQ, <recovery-expr>(file)());
        ASSERT_EQ(<recovery-expr>(file)(), "w");
        <recovery-expr>(file)("Hello, World!\n");
        <recovery-expr>(file)("Second line\n");
}

int TEST_F(FileResourceTest, int) {
        {
                FileResource file;
                <recovery-expr>(file)("Hello, World!\n");
                <recovery-expr>(file)("Second line\n");
        }
        FileResource file;
        <recovery-expr>(ASSERT_TRUE, file.isOpen());
        int content = <recovery-expr>(<recovery-expr>(file)());
        <recovery-expr>(ASSERT_NE, <recovery-expr>().find("Hello, World!"));
        <recovery-expr>(ASSERT_NE, <recovery-expr>().find("Second line"));
}

int TEST_F(FileResourceTest, int) {
        bool caught = false;
        try {
                FileResource file = <recovery-expr>("/nonexistent/path/file.txt", "r");
        } catch (const ResourceError &e) {
                caught = true;
        }
        <recovery-expr>(ASSERT_TRUE, caught);
}

int TEST_F(FileResourceTest, int) {
        const int file1 = <recovery-expr>("test1.txt");
        const int file2 = <recovery-expr>("test2.txt");
        {
                FileResource f1(<recovery-expr>(file1), "w");
                FileResource f2(<recovery-expr>(file2), "w");
                <recovery-expr>(f1)("File 1 content\n");
                <recovery-expr>(f2)("File 2 content\n");
                <recovery-expr>(ASSERT_TRUE, f1.isOpen() && f2.isOpen());
        }
        {
                FileResource f1(<recovery-expr>(file1), "r");
                FileResource f2(<recovery-expr>(file2), "r");
                <recovery-expr>(ASSERT_NE, <recovery-expr>(f1)().find("File 1"));
                <recovery-expr>(ASSERT_NE, <recovery-expr>(f2)().find("File 2"));
        }
}

int TEST_F(MemoryPoolTest, int) {
        MemoryPool<TestResource> pool;
        ASSERT_EQ(<recovery-expr>().capacity(), 10);
        ASSERT_EQ(<recovery-expr>().used(), 0);
        ASSERT_EQ(<recovery-expr>().available(), 10);
}

int TEST_F(MemoryPoolTest, int) {
        MemoryPool<TestResource> pool;
        for (int i = 0; i < 5; ++i) {
                TestResource *res = <recovery-expr>().allocate();
                res->setValue(i);
        }
        ASSERT_EQ(<recovery-expr>().used(), 5);
        ASSERT_EQ(<recovery-expr>().available(), 5);
        <recovery-expr>(<recovery-expr>(pool).deallocate);
        <recovery-expr>(<recovery-expr>(pool).deallocate);
        ASSERT_EQ(<recovery-expr>().used(), 3);
        ASSERT_EQ(<recovery-expr>().available(), 7);
        for (int i = <recovery-expr>(2); <recovery-expr>(); ++<recovery-expr>()) {
                <recovery-expr>(<recovery-expr>(pool).deallocate);
        }
        ASSERT_EQ(<recovery-expr>().used(), 0);
        ASSERT_EQ(<recovery-expr>().available(), 10);
}

int TEST_F(MemoryPoolTest, int) {
        MemoryPool<int> pool;
        int *a = <recovery-expr>().allocate();
        int *b = <recovery-expr>().allocate();
        bool caught = false;
        try {
                <recovery-expr>(pool).allocate();
        } catch (const ResourceError &e) {
                caught = true;
        }
        <recovery-expr>(ASSERT_TRUE, caught);
        <recovery-expr>(pool).deallocate(a);
        <recovery-expr>(pool).deallocate(b);
}

int TEST_F(MemoryPoolTest, int) {
        const int poolSize = <recovery-expr>(100);
        MemoryPool<int> pool;
        for (int i = <recovery-expr>(0); <recovery-expr>() < <recovery-expr>() / 2; ++<recovery-expr>()) {
        }
        ASSERT_EQ(<recovery-expr>().used(), <recovery-expr>() / 2);
        ASSERT_EQ(<recovery-expr>().used(), 0);
        for (int i = <recovery-expr>(0); <recovery-expr>() < <recovery-expr>(); ++<recovery-expr>()) {
        }
        ASSERT_EQ(<recovery-expr>().used(), <recovery-expr>());
}

int TEST_F(ResourcePoolTest, int) {
        ResourcePool<TestResource> pool;
        ASSERT_EQ(<recovery-expr>().capacity(), 5);
        ASSERT_EQ(<recovery-expr>().available(), 0);
}

int TEST_F(ResourcePoolTest, int) {
        ResourcePool<TestResource> pool;
        for (int i = 0; i < 5; ++i) {
                <recovery-expr>(<recovery-expr>(pool).add);
        }
        ASSERT_EQ(<recovery-expr>().available(), 5);
        ASSERT_EQ(<recovery-expr>().inUse(), 0);
        TestResource *res1 = <recovery-expr>().acquire();
        TestResource *res2 = <recovery-expr>().acquire();
        ASSERT_EQ(<recovery-expr>().available(), 3);
        ASSERT_EQ(<recovery-expr>().inUse(), 2);
        <recovery-expr>(pool).release(res1);
        <recovery-expr>(pool).release(res2);
        ASSERT_EQ(<recovery-expr>().available(), 5);
        ASSERT_EQ(<recovery-expr>().inUse(), 0);
}

int TEST_F(ResourcePoolTest, int) {
        ResourcePool<TestResource> pool;
        <recovery-expr>(<recovery-expr>(pool).add);
        <recovery-expr>(<recovery-expr>(pool).add);
        <recovery-expr>(<recovery-expr>(pool).add);
        bool caught = false;
        try {
                <recovery-expr>(<recovery-expr>(pool).add);
        } catch (const ResourceError &e) {
                caught = true;
        }
        <recovery-expr>(ASSERT_TRUE, caught);
}

int TEST_F(ResourcePoolTest, int) {
        ResourcePool<TestResource> pool;
        <recovery-expr>(<recovery-expr>(pool).add);
        <recovery-expr>(<recovery-expr>(pool).add);
        <recovery-expr>(<recovery-expr>(pool).add);
        ASSERT_EQ(<recovery-expr>().available(), 3);
        {
                PooledResource<TestResource> res1;
                ASSERT_EQ(<recovery-expr>().available(), 2);
                {
                        PooledResource<TestResource> res2;
                        ASSERT_EQ(<recovery-expr>().available(), 1);
                }
                ASSERT_EQ(<recovery-expr>().available(), 2);
        }
        ASSERT_EQ(<recovery-expr>().available(), 3);
}

int TEST(int, int) {
        resetTestResourceCounters();
        {
                auto handle = <recovery-expr>(makeResource<TestResource>, 42);
                ASSERT_NE(<recovery-expr>().get(), nullptr);
                ASSERT_EQ(<recovery-expr>()->getValue(), 42);
        }
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 1);
}

int TEST(int, int) {
        resetTestResourceCounters();
        {
                auto shared = <recovery-expr>(makeSharedResource<TestResource>, 99);
                ASSERT_NE(<recovery-expr>().get(), nullptr);
                ASSERT_EQ(<recovery-expr>()->getValue(), 99);
                ASSERT_EQ(<recovery-expr>().useCount(), 1);
        }
        <recovery-expr>(ASSERT_EQ, TestResource::destructorCalls, 1);
}

int TEST(int, int) {
        {
                auto arr = <recovery-expr>(makeArray<int>, 10);
                ASSERT_NE(<recovery-expr>().get(), nullptr);
                for (int i = 0; i < 10; ++i) {
                        <recovery-expr>(arr).get()[i] = i * 2;
                }
                ASSERT_EQ(<recovery-expr>().get()[5], 10);
        }
        <recovery-expr>(SUCCEED);
}


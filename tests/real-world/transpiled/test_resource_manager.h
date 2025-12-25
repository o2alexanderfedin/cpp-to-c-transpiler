// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/resource-manager/tests/test_resource_manager.cpp
// Header file

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
void resetTestResourceCounters();
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
int TEST_F(ResourceHandleTest, int);
int TEST_F(ResourceHandleTest, int);
int TEST_F(ResourceHandleTest, int);
int TEST_F(ResourceHandleTest, int);
int TEST_F(ResourceHandleTest, int);
int TEST_F(ResourceHandleTest, int);
int TEST_F(ResourceHandleTest, int);
int TEST_F(ResourceHandleTest, int);
int TEST_F(ResourceHandleTest, int);
int TEST_F(ResourceHandleTest, int);
int TEST_F(ResourceHandleTest, int);
int TEST_F(ScopeGuardTest, int);
int TEST_F(ScopeGuardTest, int);
int TEST_F(SharedResourceTest, int);
int TEST_F(SharedResourceTest, int);
int TEST_F(SharedResourceTest, int);
int TEST_F(SharedResourceTest, int);
int TEST_F(SharedResourceTest, int);
int TEST_F(SharedResourceTest, int);
int TEST_F(FileResourceTest, int);
int TEST_F(FileResourceTest, int);
int TEST_F(FileResourceTest, int);
int TEST_F(FileResourceTest, int);
int TEST_F(MemoryPoolTest, int);
int TEST_F(MemoryPoolTest, int);
int TEST_F(MemoryPoolTest, int);
int TEST_F(MemoryPoolTest, int);
int TEST_F(ResourcePoolTest, int);
int TEST_F(ResourcePoolTest, int);
int TEST_F(ResourcePoolTest, int);
int TEST_F(ResourcePoolTest, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);

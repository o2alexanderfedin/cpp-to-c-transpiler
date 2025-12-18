#ifndef RESOURCE_MANAGER_H
#define RESOURCE_MANAGER_H

#include <memory>
#include <functional>
#include <stdexcept>
#include <vector>
#include <map>
#include <string>
#include <utility>
#include <iostream>
#include <fstream>
#include <cstdio>
#include <cstring>

namespace resman {

// Resource exception
class ResourceError : public std::runtime_error {
public:
    explicit ResourceError(const std::string& message)
        : std::runtime_error("Resource Error: " + message) {}
};

// Base resource interface
template<typename T>
class IResource {
public:
    virtual ~IResource() = default;
    virtual T& get() = 0;
    virtual const T& get() const = 0;
    virtual bool isValid() const = 0;
    virtual void release() = 0;
};

// Generic resource handle with RAII
template<typename T, typename Deleter = std::default_delete<T>>
class ResourceHandle {
private:
    T* resource_;
    Deleter deleter_;
    bool owns_;

public:
    // Constructor
    explicit ResourceHandle(T* resource = nullptr, Deleter deleter = Deleter())
        : resource_(resource), deleter_(std::move(deleter)), owns_(true) {}

    // Move constructor
    ResourceHandle(ResourceHandle&& other) noexcept
        : resource_(other.resource_), deleter_(std::move(other.deleter_)), owns_(other.owns_) {
        other.resource_ = nullptr;
        other.owns_ = false;
    }

    // Move assignment
    ResourceHandle& operator=(ResourceHandle&& other) noexcept {
        if (this != &other) {
            reset();
            resource_ = other.resource_;
            deleter_ = std::move(other.deleter_);
            owns_ = other.owns_;
            other.resource_ = nullptr;
            other.owns_ = false;
        }
        return *this;
    }

    // Delete copy
    ResourceHandle(const ResourceHandle&) = delete;
    ResourceHandle& operator=(const ResourceHandle&) = delete;

    // Destructor
    ~ResourceHandle() {
        reset();
    }

    // Reset (delete current resource)
    void reset(T* newResource = nullptr) {
        if (resource_ && owns_) {
            deleter_(resource_);
        }
        resource_ = newResource;
        owns_ = (newResource != nullptr);
    }

    // Release ownership
    T* release() {
        T* temp = resource_;
        resource_ = nullptr;
        owns_ = false;
        return temp;
    }

    // Get resource
    T* get() const { return resource_; }

    // Dereference
    T& operator*() const {
        if (!resource_) {
            throw ResourceError("Dereferencing null resource");
        }
        return *resource_;
    }

    T* operator->() const {
        if (!resource_) {
            throw ResourceError("Accessing null resource");
        }
        return resource_;
    }

    // Boolean conversion
    explicit operator bool() const {
        return resource_ != nullptr;
    }

    // Swap
    void swap(ResourceHandle& other) noexcept {
        std::swap(resource_, other.resource_);
        std::swap(deleter_, other.deleter_);
        std::swap(owns_, other.owns_);
    }
};

// Scope guard for cleanup
template<typename Func>
class ScopeGuard {
private:
    Func func_;
    bool active_;

public:
    explicit ScopeGuard(Func func)
        : func_(std::move(func)), active_(true) {}

    ~ScopeGuard() {
        if (active_) {
            try {
                func_();
            } catch (...) {
                // Suppress exceptions in destructor
            }
        }
    }

    void dismiss() {
        active_ = false;
    }

    // Delete copy/move
    ScopeGuard(const ScopeGuard&) = delete;
    ScopeGuard& operator=(const ScopeGuard&) = delete;
    ScopeGuard(ScopeGuard&&) = delete;
    ScopeGuard& operator=(ScopeGuard&&) = delete;
};

// Helper function to create scope guard
template<typename Func>
ScopeGuard<Func> makeScopeGuard(Func func) {
    return ScopeGuard<Func>(std::move(func));
}

// Reference counter (for shared resources)
class RefCounter {
private:
    int* count_;

public:
    RefCounter() : count_(new int(1)) {}

    RefCounter(const RefCounter& other) : count_(other.count_) {
        if (count_) {
            ++(*count_);
        }
    }

    RefCounter& operator=(const RefCounter& other) {
        if (this != &other) {
            release();
            count_ = other.count_;
            if (count_) {
                ++(*count_);
            }
        }
        return *this;
    }

    ~RefCounter() {
        release();
    }

    int count() const {
        return count_ ? *count_ : 0;
    }

    void release() {
        if (count_) {
            if (--(*count_) == 0) {
                delete count_;
            }
            count_ = nullptr;
        }
    }
};

// Shared resource (reference counted)
template<typename T, typename Deleter = std::default_delete<T>>
class SharedResource {
private:
    T* resource_;
    RefCounter refCount_;
    Deleter deleter_;

public:
    explicit SharedResource(T* resource = nullptr, Deleter deleter = Deleter())
        : resource_(resource), refCount_(), deleter_(std::move(deleter)) {}

    // Copy constructor
    SharedResource(const SharedResource& other)
        : resource_(other.resource_), refCount_(other.refCount_), deleter_(other.deleter_) {}

    // Move constructor
    SharedResource(SharedResource&& other) noexcept
        : resource_(other.resource_), refCount_(std::move(other.refCount_)),
          deleter_(std::move(other.deleter_)) {
        other.resource_ = nullptr;
    }

    // Copy assignment
    SharedResource& operator=(const SharedResource& other) {
        if (this != &other) {
            reset();
            resource_ = other.resource_;
            refCount_ = other.refCount_;
            deleter_ = other.deleter_;
        }
        return *this;
    }

    // Move assignment
    SharedResource& operator=(SharedResource&& other) noexcept {
        if (this != &other) {
            reset();
            resource_ = other.resource_;
            refCount_ = std::move(other.refCount_);
            deleter_ = std::move(other.deleter_);
            other.resource_ = nullptr;
        }
        return *this;
    }

    ~SharedResource() {
        reset();
    }

    void reset(T* newResource = nullptr) {
        if (resource_ && refCount_.count() == 1) {
            deleter_(resource_);
        }
        resource_ = newResource;
        if (newResource) {
            refCount_ = RefCounter();
        }
    }

    T* get() const { return resource_; }

    T& operator*() const {
        if (!resource_) {
            throw ResourceError("Dereferencing null shared resource");
        }
        return *resource_;
    }

    T* operator->() const {
        if (!resource_) {
            throw ResourceError("Accessing null shared resource");
        }
        return resource_;
    }

    explicit operator bool() const {
        return resource_ != nullptr;
    }

    int useCount() const {
        return refCount_.count();
    }
};

// Custom deleters
struct FileDeleter {
    void operator()(std::FILE* file) const {
        if (file) {
            std::fclose(file);
        }
    }
};

struct MemoryDeleter {
    void operator()(void* ptr) const {
        if (ptr) {
            std::free(ptr);
        }
    }
};

template<typename T>
struct ArrayDeleter {
    void operator()(T* ptr) const {
        if (ptr) {
            delete[] ptr;
        }
    }
};

// Specific resource types
using FileHandle = ResourceHandle<std::FILE, FileDeleter>;
using MemoryHandle = ResourceHandle<void, MemoryDeleter>;

template<typename T>
using ArrayHandle = ResourceHandle<T, ArrayDeleter<T>>;

// File resource wrapper
class FileResource {
private:
    FileHandle handle_;
    std::string filename_;
    std::string mode_;

public:
    FileResource(const std::string& filename, const std::string& mode)
        : filename_(filename), mode_(mode) {
        std::FILE* file = std::fopen(filename.c_str(), mode.c_str());
        if (!file) {
            throw ResourceError("Failed to open file: " + filename);
        }
        handle_.reset(file);
    }

    std::FILE* get() const { return handle_.get(); }

    bool isOpen() const { return handle_.get() != nullptr; }

    void close() {
        handle_.reset();
    }

    const std::string& filename() const { return filename_; }
    const std::string& mode() const { return mode_; }

    // Write string to file
    void write(const std::string& data) {
        if (!isOpen()) {
            throw ResourceError("File not open");
        }
        std::fwrite(data.c_str(), 1, data.size(), handle_.get());
    }

    // Read all content
    std::string readAll() {
        if (!isOpen()) {
            throw ResourceError("File not open");
        }

        std::fseek(handle_.get(), 0, SEEK_END);
        long size = std::ftell(handle_.get());
        std::fseek(handle_.get(), 0, SEEK_SET);

        std::vector<char> buffer(size + 1);
        std::fread(buffer.data(), 1, size, handle_.get());
        buffer[size] = '\0';

        return std::string(buffer.data());
    }
};

// Memory pool (fixed-size allocations)
template<typename T>
class MemoryPool {
private:
    struct Block {
        T data;
        bool inUse;
        Block* next;

        Block() : inUse(false), next(nullptr) {}
    };

    std::vector<Block*> blocks_;
    Block* freeList_;
    size_t capacity_;
    size_t used_;

public:
    explicit MemoryPool(size_t capacity = 100)
        : freeList_(nullptr), capacity_(capacity), used_(0) {
        blocks_.reserve(capacity);
        for (size_t i = 0; i < capacity; ++i) {
            Block* block = new Block();
            block->next = freeList_;
            freeList_ = block;
            blocks_.push_back(block);
        }
    }

    ~MemoryPool() {
        for (Block* block : blocks_) {
            delete block;
        }
    }

    // Allocate object
    T* allocate() {
        if (!freeList_) {
            throw ResourceError("Memory pool exhausted");
        }

        Block* block = freeList_;
        freeList_ = block->next;
        block->inUse = true;
        block->next = nullptr;
        ++used_;

        return &block->data;
    }

    // Deallocate object
    void deallocate(T* ptr) {
        if (!ptr) return;

        Block* block = reinterpret_cast<Block*>(
            reinterpret_cast<char*>(ptr) - offsetof(Block, data)
        );

        if (!block->inUse) {
            throw ResourceError("Double free detected");
        }

        block->inUse = false;
        block->next = freeList_;
        freeList_ = block;
        --used_;
    }

    size_t capacity() const { return capacity_; }
    size_t used() const { return used_; }
    size_t available() const { return capacity_ - used_; }

    // Delete copy/move
    MemoryPool(const MemoryPool&) = delete;
    MemoryPool& operator=(const MemoryPool&) = delete;
};

// Resource pool (generic)
template<typename T>
class ResourcePool {
private:
    std::vector<std::unique_ptr<T>> resources_;
    std::vector<T*> available_;
    size_t capacity_;

public:
    explicit ResourcePool(size_t capacity) : capacity_(capacity) {
        resources_.reserve(capacity);
    }

    virtual ~ResourcePool() = default;

    // Add resource to pool
    void add(std::unique_ptr<T> resource) {
        if (resources_.size() >= capacity_) {
            throw ResourceError("Resource pool at capacity");
        }
        available_.push_back(resource.get());
        resources_.push_back(std::move(resource));
    }

    // Acquire resource from pool
    T* acquire() {
        if (available_.empty()) {
            throw ResourceError("No available resources in pool");
        }

        T* resource = available_.back();
        available_.pop_back();
        return resource;
    }

    // Release resource back to pool
    void release(T* resource) {
        if (!resource) return;

        // Verify resource belongs to this pool
        bool found = false;
        for (const auto& res : resources_) {
            if (res.get() == resource) {
                found = true;
                break;
            }
        }

        if (!found) {
            throw ResourceError("Resource does not belong to this pool");
        }

        // Check if already available
        for (T* avail : available_) {
            if (avail == resource) {
                throw ResourceError("Resource already released");
            }
        }

        available_.push_back(resource);
    }

    size_t capacity() const { return capacity_; }
    size_t available() const { return available_.size(); }
    size_t inUse() const { return resources_.size() - available_.size(); }
};

// RAII wrapper for pooled resources
template<typename T>
class PooledResource {
private:
    ResourcePool<T>* pool_;
    T* resource_;

public:
    PooledResource(ResourcePool<T>& pool)
        : pool_(&pool), resource_(pool.acquire()) {}

    ~PooledResource() {
        if (pool_ && resource_) {
            pool_->release(resource_);
        }
    }

    // Move constructor
    PooledResource(PooledResource&& other) noexcept
        : pool_(other.pool_), resource_(other.resource_) {
        other.pool_ = nullptr;
        other.resource_ = nullptr;
    }

    // Move assignment
    PooledResource& operator=(PooledResource&& other) noexcept {
        if (this != &other) {
            if (pool_ && resource_) {
                pool_->release(resource_);
            }
            pool_ = other.pool_;
            resource_ = other.resource_;
            other.pool_ = nullptr;
            other.resource_ = nullptr;
        }
        return *this;
    }

    // Delete copy
    PooledResource(const PooledResource&) = delete;
    PooledResource& operator=(const PooledResource&) = delete;

    T* get() const { return resource_; }
    T& operator*() const { return *resource_; }
    T* operator->() const { return resource_; }
};

// Resource factory
template<typename T, typename... Args>
ResourceHandle<T> makeResource(Args&&... args) {
    return ResourceHandle<T>(new T(std::forward<Args>(args)...));
}

template<typename T, typename... Args>
SharedResource<T> makeSharedResource(Args&&... args) {
    return SharedResource<T>(new T(std::forward<Args>(args)...));
}

// Helper functions
inline FileResource openFile(const std::string& filename, const std::string& mode) {
    return FileResource(filename, mode);
}

template<typename T>
ArrayHandle<T> makeArray(size_t size) {
    return ArrayHandle<T>(new T[size]);
}

} // namespace resman

#endif // RESOURCE_MANAGER_H

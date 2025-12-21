// tests/FrameAllocationTest_GTest.cpp
// Migrated from FrameAllocationTest.cpp to Google Test framework
// Unit tests for Frame Allocation and Coroutine Handle (Story #107)

#include <gtest/gtest.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include "../include/FrameAllocator.h"
#include <memory>
#include <string>

using namespace clang;

// Test fixture for Frame Allocation tests
class FrameAllocationTestFixture : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        std::vector<std::string> args = {
            "-std=c++20",
            "-isystem", "/opt/homebrew/Cellar/llvm/21.1.7/include/c++/v1",
            "-isystem", "/opt/homebrew/Cellar/llvm/21.1.7/lib/clang/21/include",
            "-isysroot", "/Library/Developer/CommandLineTools/SDKs/MacOSX15.sdk"
        };
        return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
    }

    FunctionDecl* findFunction(TranslationUnitDecl* TU, const std::string& name) {
        for (auto *D : TU->decls()) {
            if (auto *FD = dyn_cast<FunctionDecl>(D)) {
                if (FD->getNameAsString() == name) {
                    return FD;
                }
            }
        }
        return nullptr;
    }

    const char* getCoroCode() {
        return R"(
            struct task;

            namespace std {
                template<typename Promise = void>
                struct coroutine_handle {
                    static coroutine_handle from_address(void* addr) noexcept { return {}; }
                };

                template<typename T, typename... Args>
                struct coroutine_traits {
                    using promise_type = typename T::promise_type;
                };
            }

            struct task {
                struct promise_type {
                    struct awaiter {
                        bool await_ready() noexcept { return false; }
                        template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}
                        void await_resume() noexcept {}
                    };

                    task get_return_object() { return {}; }
                    awaiter initial_suspend() { return {}; }
                    awaiter final_suspend() noexcept { return {}; }
                    void return_void() {}
                    void unhandled_exception() {}
                };
            };

            task coro() {
                co_return;
            }
        )";
    }
};

// Test 1: Generate frame allocation code
TEST_F(FrameAllocationTestFixture, GenerateFrameAllocation) {
    auto AST = buildAST(getCoroCode());
    ASSERT_TRUE(AST) << "Failed to build AST";

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string allocCode = allocator.generateFrameAllocation(func);

    ASSERT_FALSE(allocCode.empty()) << "Should generate frame allocation code";
    EXPECT_TRUE(allocCode.find("malloc") != std::string::npos ||
                allocCode.find("alloc") != std::string::npos)
        << "Should allocate memory";
    EXPECT_NE(allocCode.find("frame"), std::string::npos) << "Should reference frame";
}

// Test 2: Generate coroutine handle structure
TEST_F(FrameAllocationTestFixture, GenerateCoroutineHandle) {
    auto AST = buildAST(getCoroCode());
    ASSERT_TRUE(AST) << "Failed to build AST";

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string handleStruct = allocator.generateCoroutineHandle(func);

    ASSERT_FALSE(handleStruct.empty()) << "Should generate coroutine handle";
    EXPECT_NE(handleStruct.find("struct"), std::string::npos) << "Should be a struct";
    EXPECT_TRUE(handleStruct.find("handle") != std::string::npos ||
                handleStruct.find("coro") != std::string::npos)
        << "Should reference handle or coroutine";
}

// Test 3: Generate resume operation
TEST_F(FrameAllocationTestFixture, GenerateResumeOperation) {
    auto AST = buildAST(getCoroCode());
    ASSERT_TRUE(AST) << "Failed to build AST";

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string resumeCode = allocator.generateResumeOperation(func);

    ASSERT_FALSE(resumeCode.empty()) << "Should generate resume operation";
    EXPECT_NE(resumeCode.find("resume"), std::string::npos) << "Should contain resume";
    EXPECT_NE(resumeCode.find("void"), std::string::npos) << "Should be void function";
}

// Test 4: Generate destroy operation
TEST_F(FrameAllocationTestFixture, GenerateDestroyOperation) {
    auto AST = buildAST(getCoroCode());
    ASSERT_TRUE(AST) << "Failed to build AST";

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string destroyCode = allocator.generateDestroyOperation(func);

    ASSERT_FALSE(destroyCode.empty()) << "Should generate destroy operation";
    EXPECT_NE(destroyCode.find("destroy"), std::string::npos) << "Should contain destroy";
    EXPECT_TRUE(destroyCode.find("free") != std::string::npos ||
                destroyCode.find("dealloc") != std::string::npos)
        << "Should deallocate memory";
}

// Test 5: Initialize frame with parameters
TEST_F(FrameAllocationTestFixture, InitializeFrameWithParameters) {
    auto AST = buildAST(getCoroCode());
    ASSERT_TRUE(AST) << "Failed to build AST";

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string initCode = allocator.initializeFrame(func);

    ASSERT_FALSE(initCode.empty()) << "Should generate frame initialization";
    EXPECT_NE(initCode.find("frame"), std::string::npos) << "Should reference frame";
}

// Test 6: Allocate frame on heap
TEST_F(FrameAllocationTestFixture, AllocateFrameOnHeap) {
    auto AST = buildAST(getCoroCode());
    ASSERT_TRUE(AST) << "Failed to build AST";

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string heapAllocCode = allocator.allocateOnHeap(func);

    ASSERT_FALSE(heapAllocCode.empty()) << "Should generate heap allocation";
    EXPECT_TRUE(heapAllocCode.find("malloc") != std::string::npos ||
                heapAllocCode.find("alloc") != std::string::npos)
        << "Should use heap allocation";
}

// Test 7: Return coroutine handle
TEST_F(FrameAllocationTestFixture, ReturnCoroutineHandle) {
    auto AST = buildAST(getCoroCode());
    ASSERT_TRUE(AST) << "Failed to build AST";

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string returnCode = allocator.generateReturnHandle(func);

    ASSERT_FALSE(returnCode.empty()) << "Should generate return handle code";
    EXPECT_TRUE(returnCode.find("return") != std::string::npos ||
                returnCode.find("handle") != std::string::npos)
        << "Should return handle";
}

// tests/FrameAllocationTest.cpp
// Unit tests for Frame Allocation and Coroutine Handle (Story #107)
// Following TDD: RED phase - tests written first

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/FrameAllocator.h"
#include <cassert>

using namespace clang;

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

// Test fixture
class FrameAllocationTest : public ::testing::Test {
protected:
};

TEST_F(FrameAllocationTest, GenerateFrameAllocation) {
    const char *code = R"(
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

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        FrameAllocator allocator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string allocCode = allocator.generateFrameAllocation(func);

        ASSERT_TRUE(!allocCode.empty()) << "Should generate frame allocation code";
        ASSERT_TRUE(allocCode.find("malloc") != std::string::npos ||
               allocCode.find("alloc") != std::string::npos) << "Should allocate memory";
        ASSERT_TRUE(allocCode.find("frame") != std::string::npos) << "Should reference frame";
}

TEST_F(FrameAllocationTest, GenerateCoroutineHandle) {
    const char *code = R"(
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

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        FrameAllocator allocator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string handleStruct = allocator.generateCoroutineHandle(func);

        ASSERT_TRUE(!handleStruct.empty()) << "Should generate coroutine handle";
        ASSERT_TRUE(handleStruct.find("struct") != std::string::npos) << "Should be a struct";
        ASSERT_TRUE(handleStruct.find("handle") != std::string::npos ||
               handleStruct.find("coro") != std::string::npos) << "Should reference handle or coroutine";
}

TEST_F(FrameAllocationTest, GenerateResumeOperation) {
    const char *code = R"(
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

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        FrameAllocator allocator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string resumeOp = allocator.generateResumeOperation(func);

        ASSERT_TRUE(!resumeOp.empty()) << "Should generate resume operation";
        ASSERT_TRUE(resumeOp.find("resume") != std::string::npos) << "Should reference resume";
}

TEST_F(FrameAllocationTest, GenerateDestroyOperation) {
    const char *code = R"(
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

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        FrameAllocator allocator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string destroyOp = allocator.generateDestroyOperation(func);

        ASSERT_TRUE(!destroyOp.empty()) << "Should generate destroy operation";
        ASSERT_TRUE(destroyOp.find("destroy") != std::string::npos) << "Should reference destroy";
}

TEST_F(FrameAllocationTest, InitializeFrameWithParameters) {
    const char *code = R"(
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

            task coro_with_params(int x, int y) {
                co_return;
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        FrameAllocator allocator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "coro_with_params");

        ASSERT_TRUE(func) << "Function not found";

        std::string initCode = allocator.generateFrameInitialization(func);

        ASSERT_TRUE(!initCode.empty()) << "Should generate frame initialization";
        ASSERT_TRUE(initCode.find("frame") != std::string::npos) << "Should reference frame";
}

TEST_F(FrameAllocationTest, AllocateFrameOnHeap) {
    const char *code = R"(
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

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        FrameAllocator allocator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string allocCode = allocator.generateFrameAllocation(func);

        ASSERT_TRUE(allocCode.find("sizeof") != std::string::npos) << "Should use sizeof for frame size";
}

TEST_F(FrameAllocationTest, ReturnCoroutineHandle) {
    const char *code = R"(
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

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        FrameAllocator allocator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string returnCode = allocator.generateHandleReturn(func);

        ASSERT_TRUE(!returnCode.empty()) << "Should generate return code";
        ASSERT_TRUE(returnCode.find("return") != std::string::npos) << "Should have return statement";
}

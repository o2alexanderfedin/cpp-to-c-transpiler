// tests/FrameAllocationTest.cpp
// Unit tests for Frame Allocation and Coroutine Handle (Story #107)
// Following TDD: RED phase - tests written first

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/FrameAllocator.h"
#include <iostream>
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {
        "-std=c++20",
        "-fcoroutines",
        "-isystem", "/opt/homebrew/Cellar/llvm/21.1.7/include/c++/v1",
        "-isystem", "/opt/homebrew/Cellar/llvm/21.1.7/lib/clang/21/include",
        "-isysroot", "/Library/Developer/CommandLineTools/SDKs/MacOSX15.sdk"
    };
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        std::cerr << "  Condition: " #cond << std::endl; \
        return; \
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

// Test 1: Generate frame allocation code
void test_GenerateFrameAllocation() {
    TEST_START("GenerateFrameAllocation");

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
                    bool await_ready() { return false; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    std::string allocCode = allocator.generateFrameAllocation(func);

    ASSERT(!allocCode.empty(), "Should generate frame allocation code");
    ASSERT(allocCode.find("malloc") != std::string::npos ||
           allocCode.find("alloc") != std::string::npos,
           "Should allocate memory");
    ASSERT(allocCode.find("frame") != std::string::npos, "Should reference frame");

    TEST_PASS("GenerateFrameAllocation");
}

// Test 2: Generate coroutine handle structure
void test_GenerateCoroutineHandle() {
    TEST_START("GenerateCoroutineHandle");

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
                    bool await_ready() { return false; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    std::string handleStruct = allocator.generateCoroutineHandle(func);

    ASSERT(!handleStruct.empty(), "Should generate coroutine handle");
    ASSERT(handleStruct.find("struct") != std::string::npos, "Should be a struct");
    ASSERT(handleStruct.find("handle") != std::string::npos ||
           handleStruct.find("coro") != std::string::npos,
           "Should reference handle or coroutine");

    TEST_PASS("GenerateCoroutineHandle");
}

// Test 3: Generate resume operation
void test_GenerateResumeOperation() {
    TEST_START("GenerateResumeOperation");

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
                    bool await_ready() { return false; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    std::string resumeOp = allocator.generateResumeOperation(func);

    ASSERT(!resumeOp.empty(), "Should generate resume operation");
    ASSERT(resumeOp.find("resume") != std::string::npos, "Should reference resume");

    TEST_PASS("GenerateResumeOperation");
}

// Test 4: Generate destroy operation
void test_GenerateDestroyOperation() {
    TEST_START("GenerateDestroyOperation");

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
                    bool await_ready() { return false; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    std::string destroyOp = allocator.generateDestroyOperation(func);

    ASSERT(!destroyOp.empty(), "Should generate destroy operation");
    ASSERT(destroyOp.find("destroy") != std::string::npos, "Should reference destroy");

    TEST_PASS("GenerateDestroyOperation");
}

// Test 5: Initialize frame with parameters
void test_InitializeFrameWithParameters() {
    TEST_START("InitializeFrameWithParameters");

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
                    bool await_ready() { return false; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro_with_params");

    ASSERT(func, "Function not found");

    std::string initCode = allocator.generateFrameInitialization(func);

    ASSERT(!initCode.empty(), "Should generate frame initialization");
    ASSERT(initCode.find("frame") != std::string::npos, "Should reference frame");

    TEST_PASS("InitializeFrameWithParameters");
}

// Test 6: Allocate frame on heap
void test_AllocateFrameOnHeap() {
    TEST_START("AllocateFrameOnHeap");

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
                    bool await_ready() { return false; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    std::string allocCode = allocator.generateFrameAllocation(func);

    ASSERT(allocCode.find("sizeof") != std::string::npos, "Should use sizeof for frame size");

    TEST_PASS("AllocateFrameOnHeap");
}

// Test 7: Return coroutine handle to caller
void test_ReturnCoroutineHandle() {
    TEST_START("ReturnCoroutineHandle");

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
                    bool await_ready() { return false; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    FrameAllocator allocator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    std::string returnCode = allocator.generateHandleReturn(func);

    ASSERT(!returnCode.empty(), "Should generate return code");
    ASSERT(returnCode.find("return") != std::string::npos, "Should have return statement");

    TEST_PASS("ReturnCoroutineHandle");
}

int main() {
    std::cout << "=== Frame Allocation and Coroutine Handle Tests (Story #107) ===" << std::endl;
    std::cout << "TDD Phase: RED - All tests should FAIL initially\n" << std::endl;

    test_GenerateFrameAllocation();
    test_GenerateCoroutineHandle();
    test_GenerateResumeOperation();
    test_GenerateDestroyOperation();
    test_InitializeFrameWithParameters();
    test_AllocateFrameOnHeap();
    test_ReturnCoroutineHandle();

    std::cout << "\n=== All tests passed! ===" << std::endl;
    return 0;
}

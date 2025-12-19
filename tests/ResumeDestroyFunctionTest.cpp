// tests/ResumeDestroyFunctionTest.cpp
// Unit tests for Resume and Destroy Function Generation (Story #106)
// Following TDD: RED phase - tests written first

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/StateMachineTransformer.h"
#include <iostream>
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

// Test 1: Generate resume function signature
void test_GenerateResumeFunctionSignature() {
    TEST_START("GenerateResumeFunctionSignature");

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

        task simple_coro() {
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "simple_coro");

    ASSERT(func, "Function not found");

    std::string resumeFunc = transformer.generateResumeFunction(func);

    ASSERT(!resumeFunc.empty(), "Should generate resume function");
    ASSERT(resumeFunc.find("simple_coro_resume") != std::string::npos ||
           resumeFunc.find("resume") != std::string::npos,
           "Should have resume in function name");
    ASSERT(resumeFunc.find("void") != std::string::npos, "Should have void return type");
    ASSERT(resumeFunc.find("frame") != std::string::npos, "Should accept frame parameter");

    TEST_PASS("GenerateResumeFunctionSignature");
}

// Test 2: Generate destroy function signature
void test_GenerateDestroyFunctionSignature() {
    TEST_START("GenerateDestroyFunctionSignature");

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

        task simple_coro() {
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "simple_coro");

    ASSERT(func, "Function not found");

    std::string destroyFunc = transformer.generateDestroyFunction(func);

    ASSERT(!destroyFunc.empty(), "Should generate destroy function");
    ASSERT(destroyFunc.find("simple_coro_destroy") != std::string::npos ||
           destroyFunc.find("destroy") != std::string::npos,
           "Should have destroy in function name");
    ASSERT(destroyFunc.find("void") != std::string::npos, "Should have void return type");
    ASSERT(destroyFunc.find("frame") != std::string::npos, "Should accept frame parameter");

    TEST_PASS("GenerateDestroyFunctionSignature");
}

// Test 3: Resume function contains state machine
void test_ResumeFunctionContainsStateMachine() {
    TEST_START("ResumeFunctionContainsStateMachine");

    const char *code = R"(
        struct generator;

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

        struct generator {
            struct promise_type {
                struct awaiter {
                    bool await_ready_val;
                    awaiter(bool ready) : await_ready_val(ready) {}
                    bool await_ready() noexcept { return await_ready_val; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}
                    void await_resume() noexcept {}
                };

                int value;
                generator get_return_object() { return {}; }
                awaiter initial_suspend() { return awaiter(true); }
                awaiter final_suspend() noexcept { return awaiter(true); }
                awaiter yield_value(int v) { value = v; return awaiter(false); }
                void return_void() {}
                void unhandled_exception() {}
            };
        };

        generator count() {
            co_yield 1;
            co_yield 2;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count");

    ASSERT(func, "Function not found");

    std::string resumeFunc = transformer.generateResumeFunction(func);

    ASSERT(resumeFunc.find("switch") != std::string::npos, "Should contain switch statement");
    ASSERT(resumeFunc.find("case") != std::string::npos, "Should contain case labels");
    ASSERT(resumeFunc.find("state") != std::string::npos, "Should reference state variable");

    TEST_PASS("ResumeFunctionContainsStateMachine");
}

// Test 4: Destroy function frees frame memory
void test_DestroyFunctionFreesMemory() {
    TEST_START("DestroyFunctionFreesMemory");

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
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    std::string destroyFunc = transformer.generateDestroyFunction(func);

    ASSERT(destroyFunc.find("free") != std::string::npos, "Should call free() to release memory");
    ASSERT(destroyFunc.find("frame") != std::string::npos, "Should free frame");

    TEST_PASS("DestroyFunctionFreesMemory");
}

// Test 5: Resume function accepts frame pointer
void test_ResumeFunctionAcceptsFramePointer() {
    TEST_START("ResumeFunctionAcceptsFramePointer");

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
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    std::string resumeFunc = transformer.generateResumeFunction(func);

    ASSERT(resumeFunc.find("void*") != std::string::npos ||
           resumeFunc.find("frame_ptr") != std::string::npos,
           "Should accept void* frame pointer");

    TEST_PASS("ResumeFunctionAcceptsFramePointer");
}

// Test 6: Destroy function accepts frame pointer
void test_DestroyFunctionAcceptsFramePointer() {
    TEST_START("DestroyFunctionAcceptsFramePointer");

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
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    std::string destroyFunc = transformer.generateDestroyFunction(func);

    ASSERT(destroyFunc.find("void*") != std::string::npos ||
           destroyFunc.find("frame_ptr") != std::string::npos,
           "Should accept void* frame pointer");

    TEST_PASS("DestroyFunctionAcceptsFramePointer");
}

// Test 7: Resume and destroy function names match coroutine name
void test_FunctionNamesMatchCoroutineName() {
    TEST_START("FunctionNamesMatchCoroutineName");

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

        task my_custom_coro() {
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "my_custom_coro");

    ASSERT(func, "Function not found");

    std::string resumeFunc = transformer.generateResumeFunction(func);
    std::string destroyFunc = transformer.generateDestroyFunction(func);

    ASSERT(resumeFunc.find("my_custom_coro") != std::string::npos,
           "Resume function should reference coroutine name");
    ASSERT(destroyFunc.find("my_custom_coro") != std::string::npos,
           "Destroy function should reference coroutine name");

    TEST_PASS("FunctionNamesMatchCoroutineName");
}

int main() {
    std::cout << "=== Resume and Destroy Function Generation Tests (Story #106) ===" << std::endl;
    std::cout << "TDD Phase: RED - All tests should FAIL initially\n" << std::endl;

    test_GenerateResumeFunctionSignature();
    test_GenerateDestroyFunctionSignature();
    test_ResumeFunctionContainsStateMachine();
    test_DestroyFunctionFreesMemory();
    test_ResumeFunctionAcceptsFramePointer();
    test_DestroyFunctionAcceptsFramePointer();
    test_FunctionNamesMatchCoroutineName();

    std::cout << "\n=== All tests passed! ===" << std::endl;
    return 0;
}

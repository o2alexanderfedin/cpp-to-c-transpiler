// tests/ResumeDestroyFunctionTest.cpp
// Unit tests for Resume and Destroy Function Generation (Story #106)
// Following TDD: RED phase - tests written first

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/StateMachineTransformer.h"
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

// Test fixture
class ResumeDestroyFunctionTest : public ::testing::Test {
protected:
};

TEST_F(ResumeDestroyFunctionTest, GenerateResumeFunctionSignature) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "simple_coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string resumeFunc = transformer.generateResumeFunction(func);

        ASSERT_TRUE(!resumeFunc.empty()) << "Should generate resume function";
        ASSERT_TRUE(resumeFunc.find("simple_coro_resume") != std::string::npos ||
               resumeFunc.find("resume") != std::string::npos) << "Should have resume in function name";
        ASSERT_TRUE(resumeFunc.find("void") != std::string::npos) << "Should have void return type";
        ASSERT_TRUE(resumeFunc.find("frame") != std::string::npos) << "Should accept frame parameter";
}

TEST_F(ResumeDestroyFunctionTest, GenerateDestroyFunctionSignature) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "simple_coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string destroyFunc = transformer.generateDestroyFunction(func);

        ASSERT_TRUE(!destroyFunc.empty()) << "Should generate destroy function";
        ASSERT_TRUE(destroyFunc.find("simple_coro_destroy") != std::string::npos ||
               destroyFunc.find("destroy") != std::string::npos) << "Should have destroy in function name";
        ASSERT_TRUE(destroyFunc.find("void") != std::string::npos) << "Should have void return type";
        ASSERT_TRUE(destroyFunc.find("frame") != std::string::npos) << "Should accept frame parameter";
}

TEST_F(ResumeDestroyFunctionTest, ResumeFunctionContainsStateMachine) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "count");

        ASSERT_TRUE(func) << "Function not found";

        std::string resumeFunc = transformer.generateResumeFunction(func);

        ASSERT_TRUE(resumeFunc.find("switch") != std::string::npos) << "Should contain switch statement";
        ASSERT_TRUE(resumeFunc.find("case") != std::string::npos) << "Should contain case labels";
        ASSERT_TRUE(resumeFunc.find("state") != std::string::npos) << "Should reference state variable";
}

TEST_F(ResumeDestroyFunctionTest, DestroyFunctionFreesMemory) {
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

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string destroyFunc = transformer.generateDestroyFunction(func);

        ASSERT_TRUE(destroyFunc.find("free") != std::string::npos) << "Should call free(;to release memory");
        ASSERT_TRUE(destroyFunc.find("frame") != std::string::npos) << "Should free frame";
}

TEST_F(ResumeDestroyFunctionTest, ResumeFunctionAcceptsFramePointer) {
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

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string resumeFunc = transformer.generateResumeFunction(func);

        ASSERT_TRUE(resumeFunc.find("void*") != std::string::npos ||
               resumeFunc.find("frame_ptr") != std::string::npos) << "Should accept void* frame pointer";
}

TEST_F(ResumeDestroyFunctionTest, DestroyFunctionAcceptsFramePointer) {
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

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string destroyFunc = transformer.generateDestroyFunction(func);

        ASSERT_TRUE(destroyFunc.find("void*") != std::string::npos ||
               destroyFunc.find("frame_ptr") != std::string::npos) << "Should accept void* frame pointer";
}

TEST_F(ResumeDestroyFunctionTest, FunctionNamesMatchCoroutineName) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "my_custom_coro");

        ASSERT_TRUE(func) << "Function not found";

        std::string resumeFunc = transformer.generateResumeFunction(func);
        std::string destroyFunc = transformer.generateDestroyFunction(func);

        ASSERT_TRUE(resumeFunc.find("my_custom_coro") != std::string::npos) << "Resume function should reference coroutine name";
        ASSERT_TRUE(destroyFunc.find("my_custom_coro") != std::string::npos) << "Destroy function should reference coroutine name";
}

// tests/ResumeDestroyFunctionTest_GTest.cpp
// Unit tests for Resume and Destroy Function Generation (Story #106)
// Migrated to Google Test framework

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/StateMachineTransformer.h"

using namespace clang;

class ResumeDestroyFunctionTestFixture : public ::testing::Test {
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
};

TEST_F(ResumeDestroyFunctionTestFixture, GenerateResumeFunctionSignature) {
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
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "simple_coro");
    ASSERT_NE(func, nullptr);

    std::string resumeFunc = transformer.generateResumeFunction(func);
    EXPECT_FALSE(resumeFunc.empty());
    bool hasResume = resumeFunc.find("simple_coro_resume") != std::string::npos ||
                     resumeFunc.find("resume") != std::string::npos;
    EXPECT_TRUE(hasResume);
    EXPECT_NE(resumeFunc.find("void"), std::string::npos);
    EXPECT_NE(resumeFunc.find("frame"), std::string::npos);
}

TEST_F(ResumeDestroyFunctionTestFixture, GenerateDestroyFunctionSignature) {
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
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "simple_coro");
    ASSERT_NE(func, nullptr);

    std::string destroyFunc = transformer.generateDestroyFunction(func);
    EXPECT_FALSE(destroyFunc.empty());
    bool hasDestroy = destroyFunc.find("simple_coro_destroy") != std::string::npos ||
                      destroyFunc.find("destroy") != std::string::npos;
    EXPECT_TRUE(hasDestroy);
    EXPECT_NE(destroyFunc.find("void"), std::string::npos);
    EXPECT_NE(destroyFunc.find("frame"), std::string::npos);
}

TEST_F(ResumeDestroyFunctionTestFixture, ResumeFunctionContainsStateMachine) {
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
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "count");
    ASSERT_NE(func, nullptr);

    std::string resumeFunc = transformer.generateResumeFunction(func);
    EXPECT_NE(resumeFunc.find("switch"), std::string::npos);
    EXPECT_NE(resumeFunc.find("case"), std::string::npos);
    EXPECT_NE(resumeFunc.find("state"), std::string::npos);
}

TEST_F(ResumeDestroyFunctionTestFixture, DestroyFunctionFreesMemory) {
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
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "coro");
    ASSERT_NE(func, nullptr);

    std::string destroyFunc = transformer.generateDestroyFunction(func);
    EXPECT_NE(destroyFunc.find("free"), std::string::npos);
    EXPECT_NE(destroyFunc.find("frame"), std::string::npos);
}

TEST_F(ResumeDestroyFunctionTestFixture, ResumeFunctionAcceptsFramePointer) {
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
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "coro");
    ASSERT_NE(func, nullptr);

    std::string resumeFunc = transformer.generateResumeFunction(func);
    bool hasFramePtr = resumeFunc.find("void*") != std::string::npos ||
                       resumeFunc.find("frame_ptr") != std::string::npos;
    EXPECT_TRUE(hasFramePtr);
}

TEST_F(ResumeDestroyFunctionTestFixture, DestroyFunctionAcceptsFramePointer) {
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
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "coro");
    ASSERT_NE(func, nullptr);

    std::string destroyFunc = transformer.generateDestroyFunction(func);
    bool hasFramePtr = destroyFunc.find("void*") != std::string::npos ||
                       destroyFunc.find("frame_ptr") != std::string::npos;
    EXPECT_TRUE(hasFramePtr);
}

TEST_F(ResumeDestroyFunctionTestFixture, FunctionNamesMatchCoroutineName) {
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
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "my_custom_coro");
    ASSERT_NE(func, nullptr);

    std::string resumeFunc = transformer.generateResumeFunction(func);
    std::string destroyFunc = transformer.generateDestroyFunction(func);

    EXPECT_NE(resumeFunc.find("my_custom_coro"), std::string::npos);
    EXPECT_NE(destroyFunc.find("my_custom_coro"), std::string::npos);
}

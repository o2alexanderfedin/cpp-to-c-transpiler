// tests/StateMachineTransformerTest_GTest.cpp
// Unit tests for State Machine Transformation (Story #104)
// Migrated to Google Test framework

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/StateMachineTransformer.h"
#include "../include/SuspendPointIdentifier.h"

using namespace clang;

class StateMachineTransformerTestFixture : public ::testing::Test {
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

TEST_F(StateMachineTransformerTestFixture, GenerateSwitchWrapper) {
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

    std::string stateMachine = transformer.transformToStateMachine(func);
    EXPECT_FALSE(stateMachine.empty());
    EXPECT_NE(stateMachine.find("switch"), std::string::npos);
    EXPECT_NE(stateMachine.find("case"), std::string::npos);
}

TEST_F(StateMachineTransformerTestFixture, GenerateCaseLabels) {
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
            co_yield 3;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "count");
    ASSERT_NE(func, nullptr);

    std::string stateMachine = transformer.transformToStateMachine(func);
    bool hasCase0 = stateMachine.find("case 0:") != std::string::npos ||
                    stateMachine.find("case 0 :") != std::string::npos;
    EXPECT_TRUE(hasCase0);
}

TEST_F(StateMachineTransformerTestFixture, SplitCodeAtSuspendPoints) {
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
        generator sequential() {
            int x = 1;
            co_yield x;
            int y = 2;
            co_yield y;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "sequential");
    ASSERT_NE(func, nullptr);

    std::string stateMachine = transformer.transformToStateMachine(func);
    EXPECT_FALSE(stateMachine.empty());
}

TEST_F(StateMachineTransformerTestFixture, GenerateResumeFunction) {
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
    EXPECT_FALSE(resumeFunc.empty());
    bool hasResume = resumeFunc.find("_resume") != std::string::npos ||
                     resumeFunc.find("resume") != std::string::npos;
    EXPECT_TRUE(hasResume);
}

TEST_F(StateMachineTransformerTestFixture, InsertStateSaveBeforeSuspend) {
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
        generator gen() {
            co_yield 42;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "gen");
    ASSERT_NE(func, nullptr);

    std::string stateMachine = transformer.transformToStateMachine(func);
    EXPECT_NE(stateMachine.find("state"), std::string::npos);
}

TEST_F(StateMachineTransformerTestFixture, HandleInitialSuspendPoint) {
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
        task initial() {
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "initial");
    ASSERT_NE(func, nullptr);

    std::string stateMachine = transformer.transformToStateMachine(func);
    bool hasCase0 = stateMachine.find("case 0") != std::string::npos ||
                    stateMachine.find("case 0:") != std::string::npos;
    EXPECT_TRUE(hasCase0);
}

TEST_F(StateMachineTransformerTestFixture, PreserveLocalVariableLifetime) {
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
        generator lifetime_test() {
            int counter = 0;
            co_yield counter;
            counter++;
            co_yield counter;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr);
    StateMachineTransformer transformer(AST->getASTContext());
    auto *func = findFunction(AST->getASTContext().getTranslationUnitDecl(), "lifetime_test");
    ASSERT_NE(func, nullptr);

    std::string stateMachine = transformer.transformToStateMachine(func);
    EXPECT_FALSE(stateMachine.empty());
}

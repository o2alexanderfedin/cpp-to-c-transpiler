// tests/StateMachineTransformerTest.cpp
// Unit tests for State Machine Transformation (Story #104)
// Following TDD: RED phase - tests written first

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/StateMachineTransformer.h"
#include "../include/SuspendPointIdentifier.h"
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
class StateMachineTransformerTest : public ::testing::Test {
protected:
};

TEST_F(StateMachineTransformerTest, GenerateSwitchWrapper) {
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

        std::string stateMachine = transformer.transformToStateMachine(func);

        ASSERT_TRUE(!stateMachine.empty()) << "Should generate state machine code";
        ASSERT_TRUE(stateMachine.find("switch") != std::string::npos) << "Should contain switch statement";
        ASSERT_TRUE(stateMachine.find("case") != std::string::npos) << "Should contain case labels";
}

TEST_F(StateMachineTransformerTest, GenerateCaseLabels) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "count");

        ASSERT_TRUE(func) << "Function not found";

        std::string stateMachine = transformer.transformToStateMachine(func);

        // Should have case 0 (initial), case 1, case 2, case 3 for the three yields
        ASSERT_TRUE(stateMachine.find("case 0:") != std::string::npos ||
               stateMachine.find("case 0 :") != std::string::npos) << "Should have case 0 for initial state";
}

TEST_F(StateMachineTransformerTest, SplitCodeAtSuspendPoints) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "sequential");

        ASSERT_TRUE(func) << "Function not found";

        std::string stateMachine = transformer.transformToStateMachine(func);

        ASSERT_TRUE(!stateMachine.empty()) << "Should generate code";
        // Code should be split into segments between suspend points
}

TEST_F(StateMachineTransformerTest, GenerateResumeFunction) {
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

        ASSERT_TRUE(!resumeFunc.empty()) << "Should generate resume function";
        ASSERT_TRUE(resumeFunc.find("_resume") != std::string::npos ||
               resumeFunc.find("resume") != std::string::npos) << "Should have resume in function name";
}

TEST_F(StateMachineTransformerTest, InsertStateSaveBeforeSuspend) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "gen");

        ASSERT_TRUE(func) << "Function not found";

        std::string stateMachine = transformer.transformToStateMachine(func);

        // Should save state before returning/suspending
        ASSERT_TRUE(stateMachine.find("state") != std::string::npos) << "Should reference state variable";
}

TEST_F(StateMachineTransformerTest, HandleInitialSuspendPoint) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "initial");

        ASSERT_TRUE(func) << "Function not found";

        std::string stateMachine = transformer.transformToStateMachine(func);

        // Should handle initial state (case 0)
        ASSERT_TRUE(stateMachine.find("case 0") != std::string::npos ||
               stateMachine.find("case 0:") != std::string::npos) << "Should have initial state case";
}

TEST_F(StateMachineTransformerTest, PreserveLocalVariableLifetime) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        StateMachineTransformer transformer(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *func = findFunction(TU, "lifetime_test");

        ASSERT_TRUE(func) << "Function not found";

        std::string stateMachine = transformer.transformToStateMachine(func);

        ASSERT_TRUE(!stateMachine.empty()) << "Should generate state machine";
        // Locals that span suspend points should be moved to frame
}

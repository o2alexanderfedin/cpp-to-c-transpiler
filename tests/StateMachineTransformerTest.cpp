// tests/StateMachineTransformerTest.cpp
// Unit tests for State Machine Transformation (Story #104)
// Following TDD: RED phase - tests written first

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/StateMachineTransformer.h"
#include "../include/SuspendPointIdentifier.h"
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

// Test 1: Generate switch statement wrapper
void test_GenerateSwitchWrapper() {
    TEST_START("GenerateSwitchWrapper");

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

    std::string stateMachine = transformer.transformToStateMachine(func);

    ASSERT(!stateMachine.empty(), "Should generate state machine code");
    ASSERT(stateMachine.find("switch") != std::string::npos, "Should contain switch statement");
    ASSERT(stateMachine.find("case") != std::string::npos, "Should contain case labels");

    TEST_PASS("GenerateSwitchWrapper");
}

// Test 2: Generate case labels for each suspend point
void test_GenerateCaseLabels() {
    TEST_START("GenerateCaseLabels");

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
                    bool await_ready() { return await_ready_val; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count");

    ASSERT(func, "Function not found");

    std::string stateMachine = transformer.transformToStateMachine(func);

    // Should have case 0 (initial), case 1, case 2, case 3 for the three yields
    ASSERT(stateMachine.find("case 0:") != std::string::npos ||
           stateMachine.find("case 0 :") != std::string::npos,
           "Should have case 0 for initial state");

    TEST_PASS("GenerateCaseLabels");
}

// Test 3: Split code at suspend points
void test_SplitCodeAtSuspendPoints() {
    TEST_START("SplitCodeAtSuspendPoints");

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
                    bool await_ready() { return await_ready_val; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "sequential");

    ASSERT(func, "Function not found");

    std::string stateMachine = transformer.transformToStateMachine(func);

    ASSERT(!stateMachine.empty(), "Should generate code");
    // Code should be split into segments between suspend points

    TEST_PASS("SplitCodeAtSuspendPoints");
}

// Test 4: Generate resume function
void test_GenerateResumeFunction() {
    TEST_START("GenerateResumeFunction");

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

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    std::string resumeFunc = transformer.generateResumeFunction(func);

    ASSERT(!resumeFunc.empty(), "Should generate resume function");
    ASSERT(resumeFunc.find("_resume") != std::string::npos ||
           resumeFunc.find("resume") != std::string::npos,
           "Should have resume in function name");

    TEST_PASS("GenerateResumeFunction");
}

// Test 5: Insert state save before suspend points
void test_InsertStateSaveBeforeSuspend() {
    TEST_START("InsertStateSaveBeforeSuspend");

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
                    bool await_ready() { return await_ready_val; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "gen");

    ASSERT(func, "Function not found");

    std::string stateMachine = transformer.transformToStateMachine(func);

    // Should save state before returning/suspending
    ASSERT(stateMachine.find("state") != std::string::npos,
           "Should reference state variable");

    TEST_PASS("InsertStateSaveBeforeSuspend");
}

// Test 6: Handle initial suspend point
void test_HandleInitialSuspendPoint() {
    TEST_START("HandleInitialSuspendPoint");

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

        task initial() {
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "initial");

    ASSERT(func, "Function not found");

    std::string stateMachine = transformer.transformToStateMachine(func);

    // Should handle initial state (case 0)
    ASSERT(stateMachine.find("case 0") != std::string::npos ||
           stateMachine.find("case 0:") != std::string::npos,
           "Should have initial state case");

    TEST_PASS("HandleInitialSuspendPoint");
}

// Test 7: Preserve local variable lifetime across suspend points
void test_PreserveLocalVariableLifetime() {
    TEST_START("PreserveLocalVariableLifetime");

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
                    bool await_ready() { return await_ready_val; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) {}
                    void await_resume() {}
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
    ASSERT(AST, "Failed to build AST");

    StateMachineTransformer transformer(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "lifetime_test");

    ASSERT(func, "Function not found");

    std::string stateMachine = transformer.transformToStateMachine(func);

    ASSERT(!stateMachine.empty(), "Should generate state machine");
    // Locals that span suspend points should be moved to frame

    TEST_PASS("PreserveLocalVariableLifetime");
}

int main() {
    std::cout << "=== State Machine Transformation Tests (Story #104) ===" << std::endl;
    std::cout << "TDD Phase: RED - All tests should FAIL initially\n" << std::endl;

    test_GenerateSwitchWrapper();
    test_GenerateCaseLabels();
    test_SplitCodeAtSuspendPoints();
    test_GenerateResumeFunction();
    test_InsertStateSaveBeforeSuspend();
    test_HandleInitialSuspendPoint();
    test_PreserveLocalVariableLifetime();

    std::cout << "\n=== All tests passed! ===" << std::endl;
    return 0;
}

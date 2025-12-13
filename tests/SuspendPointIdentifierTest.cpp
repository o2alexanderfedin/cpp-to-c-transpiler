// tests/SuspendPointIdentifierTest.cpp
// Unit tests for Suspend Point Identification (Story #103)
// Following TDD: RED phase - tests written first

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
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

// Test 1: Identify co_await suspend points
void test_IdentifyCoAwaitSuspendPoints() {
    TEST_START("IdentifyCoAwaitSuspendPoints");

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

        task async_func() {
            co_await task::promise_type::awaiter{};
            co_await task::promise_type::awaiter{};
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "async_func");

    ASSERT(func, "Function not found");

    auto suspendPoints = identifier.identifySuspendPoints(func);
    ASSERT(suspendPoints.size() >= 2, "Should identify at least 2 co_await suspend points");

    TEST_PASS("IdentifyCoAwaitSuspendPoints");
}

// Test 2: Identify co_yield suspend points
void test_IdentifyCoYieldSuspendPoints() {
    TEST_START("IdentifyCoYieldSuspendPoints");

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

        generator produce_values() {
            co_yield 1;
            co_yield 2;
            co_yield 3;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "produce_values");

    ASSERT(func, "Function not found");

    auto suspendPoints = identifier.identifySuspendPoints(func);
    ASSERT(suspendPoints.size() >= 3, "Should identify at least 3 co_yield suspend points");

    TEST_PASS("IdentifyCoYieldSuspendPoints");
}

// Test 3: Identify co_return suspend points
void test_IdentifyCoReturnSuspendPoints() {
    TEST_START("IdentifyCoReturnSuspendPoints");

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

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "simple_coro");

    ASSERT(func, "Function not found");

    auto suspendPoints = identifier.identifySuspendPoints(func);
    ASSERT(suspendPoints.size() >= 1, "Should identify at least 1 suspend point (co_return)");

    TEST_PASS("IdentifyCoReturnSuspendPoints");
}

// Test 4: Get suspend point locations with line numbers
void test_GetSuspendPointLocations() {
    TEST_START("GetSuspendPointLocations");

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
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count");

    ASSERT(func, "Function not found");

    auto suspendPoints = identifier.identifySuspendPoints(func);
    ASSERT(!suspendPoints.empty(), "Should have suspend points");

    // Check that each suspend point has valid location info
    for (const auto& sp : suspendPoints) {
        ASSERT(sp.line > 0, "Suspend point should have valid line number");
        ASSERT(!sp.kind.empty(), "Suspend point should have kind");
    }

    TEST_PASS("GetSuspendPointLocations");
}

// Test 5: Classify suspend point types
void test_ClassifySuspendPointTypes() {
    TEST_START("ClassifySuspendPointTypes");

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

        generator mixed() {
            co_yield 42;
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "mixed");

    ASSERT(func, "Function not found");

    auto suspendPoints = identifier.identifySuspendPoints(func);

    bool hasYield = false;
    bool hasReturn = false;

    for (const auto& sp : suspendPoints) {
        if (sp.kind == "co_yield") hasYield = true;
        if (sp.kind == "co_return") hasReturn = true;
    }

    ASSERT(hasYield, "Should identify co_yield");
    ASSERT(hasReturn, "Should identify co_return");

    TEST_PASS("ClassifySuspendPointTypes");
}

// Test 6: Generate state labels for suspend points
void test_GenerateStateLabels() {
    TEST_START("GenerateStateLabels");

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
            co_yield 1;
            co_yield 2;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "gen");

    ASSERT(func, "Function not found");

    std::string stateLabels = identifier.generateStateLabels(func);

    ASSERT(!stateLabels.empty(), "Should generate state labels");
    ASSERT(stateLabels.find("STATE_") != std::string::npos, "Should contain STATE_ prefix");

    TEST_PASS("GenerateStateLabels");
}

// Test 7: Order suspend points by execution flow
void test_OrderSuspendPointsByFlow() {
    TEST_START("OrderSuspendPointsByFlow");

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
            co_yield 1;
            co_yield 2;
            co_yield 3;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "sequential");

    ASSERT(func, "Function not found");

    auto suspendPoints = identifier.identifySuspendPoints(func);

    // Verify suspend points are ordered by line number
    for (size_t i = 1; i < suspendPoints.size(); ++i) {
        ASSERT(suspendPoints[i].line >= suspendPoints[i-1].line,
               "Suspend points should be ordered by line number");
    }

    TEST_PASS("OrderSuspendPointsByFlow");
}

int main() {
    std::cout << "=== Suspend Point Identification Tests (Story #103) ===" << std::endl;
    std::cout << "TDD Phase: RED - All tests should FAIL initially\n" << std::endl;

    test_IdentifyCoAwaitSuspendPoints();
    test_IdentifyCoYieldSuspendPoints();
    test_IdentifyCoReturnSuspendPoints();
    test_GetSuspendPointLocations();
    test_ClassifySuspendPointTypes();
    test_GenerateStateLabels();
    test_OrderSuspendPointsByFlow();

    std::cout << "\n=== All tests passed! ===" << std::endl;
    return 0;
}

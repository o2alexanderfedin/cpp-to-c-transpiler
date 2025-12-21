// tests/SuspendPointIdentifierTest_GTest.cpp
// Unit tests for Suspend Point Identification (Story #103)
// Migrated to Google Test framework

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/SuspendPointIdentifier.h"

using namespace clang;

class SuspendPointIdentifierTestFixture : public ::testing::Test {
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

// Test 1: Identify co_await suspend points
TEST_F(SuspendPointIdentifierTestFixture, IdentifyCoAwaitSuspendPoints) {
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
        task async_func() {
            co_await task::promise_type::awaiter{};
            co_await task::promise_type::awaiter{};
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "async_func");
    ASSERT_NE(func, nullptr) << "Function not found";

    auto suspendPoints = identifier.identifySuspendPoints(func);
    EXPECT_GE(suspendPoints.size(), 2u) << "Should identify at least 2 co_await suspend points";
}

// Test 2: Identify co_yield suspend points
TEST_F(SuspendPointIdentifierTestFixture, IdentifyCoYieldSuspendPoints) {
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
        generator produce_values() {
            co_yield 1;
            co_yield 2;
            co_yield 3;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "produce_values");
    ASSERT_NE(func, nullptr) << "Function not found";

    auto suspendPoints = identifier.identifySuspendPoints(func);
    EXPECT_GE(suspendPoints.size(), 3u) << "Should identify at least 3 co_yield suspend points";
}

// Test 3: Identify co_return suspend points
TEST_F(SuspendPointIdentifierTestFixture, IdentifyCoReturnSuspendPoints) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "simple_coro");
    ASSERT_NE(func, nullptr) << "Function not found";

    auto suspendPoints = identifier.identifySuspendPoints(func);
    EXPECT_GE(suspendPoints.size(), 1u) << "Should identify at least 1 suspend point (co_return)";
}

// Test 4: Get suspend point locations with line numbers
TEST_F(SuspendPointIdentifierTestFixture, GetSuspendPointLocations) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count");
    ASSERT_NE(func, nullptr) << "Function not found";

    auto suspendPoints = identifier.identifySuspendPoints(func);
    EXPECT_FALSE(suspendPoints.empty()) << "Should have suspend points";

    for (const auto& sp : suspendPoints) {
        EXPECT_GT(sp.line, 0u) << "Suspend point should have valid line number";
        EXPECT_FALSE(sp.kind.empty()) << "Suspend point should have kind";
    }
}

// Test 5: Classify suspend point types
TEST_F(SuspendPointIdentifierTestFixture, ClassifySuspendPointTypes) {
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
        generator mixed() {
            co_yield 42;
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "mixed");
    ASSERT_NE(func, nullptr) << "Function not found";

    auto suspendPoints = identifier.identifySuspendPoints(func);

    bool hasYield = false;
    bool hasReturn = false;

    for (const auto& sp : suspendPoints) {
        if (sp.kind == "co_yield") hasYield = true;
        if (sp.kind == "co_return") hasReturn = true;
    }

    EXPECT_TRUE(hasYield) << "Should identify co_yield";
    EXPECT_TRUE(hasReturn) << "Should identify co_return";
}

// Test 6: Generate state labels for suspend points
TEST_F(SuspendPointIdentifierTestFixture, GenerateStateLabels) {
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
            co_yield 1;
            co_yield 2;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "gen");
    ASSERT_NE(func, nullptr) << "Function not found";

    std::string stateLabels = identifier.generateStateLabels(func);

    EXPECT_FALSE(stateLabels.empty()) << "Should generate state labels";
    EXPECT_NE(stateLabels.find("STATE_"), std::string::npos) << "Should contain STATE_ prefix";
}

// Test 7: Order suspend points by execution flow
TEST_F(SuspendPointIdentifierTestFixture, OrderSuspendPointsByFlow) {
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
            co_yield 1;
            co_yield 2;
            co_yield 3;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "sequential");
    ASSERT_NE(func, nullptr) << "Function not found";

    auto suspendPoints = identifier.identifySuspendPoints(func);

    // Verify suspend points are ordered by line number
    for (size_t i = 1; i < suspendPoints.size(); ++i) {
        EXPECT_GE(suspendPoints[i].line, suspendPoints[i-1].line)
            << "Suspend points should be ordered by line number";
    }
}

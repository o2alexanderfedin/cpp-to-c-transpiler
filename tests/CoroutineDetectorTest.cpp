// tests/CoroutineDetectorTest.cpp
// Unit tests for Coroutine Detection and Frame Structure (Story #102)
// Following TDD: RED phase - tests written first

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/CoroutineDetector.h"
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

// Test 1: Detect coroutine by co_return
void test_DetectCoroutineByCoReturn() {
    TEST_START("DetectCoroutineByCoReturn");

    // Minimal coroutine without standard library dependencies
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

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "simple_coro");

    ASSERT(func, "Function not found");
    ASSERT(detector.isCoroutine(func), "Should detect coroutine with co_return");

    TEST_PASS("DetectCoroutineByCoReturn");
}

// Test 2: Detect coroutine by co_yield
void test_DetectCoroutineByCoYield() {
    TEST_START("DetectCoroutineByCoYield");

    // Minimal coroutine with co_yield
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

        generator count_to(int n) {
            for (int i = 0; i < n; ++i) {
                co_yield i;
            }
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count_to");

    ASSERT(func, "Function not found");
    ASSERT(detector.isCoroutine(func), "Should detect coroutine with co_yield");

    TEST_PASS("DetectCoroutineByCoYield");
}

// Test 3: Non-coroutine function
void test_NonCoroutineDetection() {
    TEST_START("NonCoroutineDetection");

    const char *code = R"(
        int regular_function() {
            return 42;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "regular_function");

    ASSERT(func, "Function not found");
    ASSERT(!detector.isCoroutine(func), "Should NOT detect regular function as coroutine");

    TEST_PASS("NonCoroutineDetection");
}

// Test 4: Generate frame structure
void test_GenerateFrameStructure() {
    TEST_START("GenerateFrameStructure");

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

        task my_coro(int param) {
            int local = param;
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "my_coro");

    ASSERT(func, "Function not found");

    std::string frameCode = detector.generateFrameStructure(func);

    ASSERT(!frameCode.empty(), "Frame structure should be generated");
    ASSERT(frameCode.find("_frame") != std::string::npos, "Should contain frame struct");
    ASSERT(frameCode.find("state") != std::string::npos, "Should contain state field");

    TEST_PASS("GenerateFrameStructure");
}

// Test 5: Frame includes resume/destroy function pointers
void test_FrameIncludesFunctionPointers() {
    TEST_START("FrameIncludesFunctionPointers");

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

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    std::string frameCode = detector.generateFrameStructure(func);

    ASSERT(frameCode.find("resume_fn") != std::string::npos ||
           frameCode.find("resume") != std::string::npos,
           "Frame should include resume function pointer");
    ASSERT(frameCode.find("destroy_fn") != std::string::npos ||
           frameCode.find("destroy") != std::string::npos,
           "Frame should include destroy function pointer");

    TEST_PASS("FrameIncludesFunctionPointers");
}

// Test 6: Frame includes parameters
void test_FrameIncludesParameters() {
    TEST_START("FrameIncludesParameters");

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

        task coro_with_params(int x, double y) {
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro_with_params");

    std::string frameCode = detector.generateFrameStructure(func);

    // Parameters should be copied to frame
    ASSERT(frameCode.find("int") != std::string::npos, "Frame should include int parameter");

    TEST_PASS("FrameIncludesParameters");
}

// Test 7: Count suspend points
void test_CountSuspendPoints() {
    TEST_START("CountSuspendPoints");

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
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count");

    ASSERT(func, "Function not found");

    size_t suspendCount = detector.countSuspendPoints(func);
    ASSERT(suspendCount >= 2, "Should detect at least 2 co_yield suspend points");

    TEST_PASS("CountSuspendPoints");
}

// Test 8: Identify local variables spanning suspend points
void test_IdentifyLocalVariablesSpanningSuspends() {
    TEST_START("IdentifyLocalVariablesSpanningSuspends");

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

        generator count_to(int n) {
            for (int i = 0; i < n; ++i) {
                co_yield i;
            }
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count_to");

    ASSERT(func, "Function not found");

    auto localVars = detector.analyzeLocalVariables(func);

    // Variable 'i' should be identified as spanning suspend points
    ASSERT(!localVars.empty(), "Should identify at least one local variable");

    bool foundI = false;
    for (const auto& var : localVars) {
        if (var.name == "i") {
            foundI = true;
            ASSERT(var.type == "int", "Variable 'i' should be int type");
        }
    }
    ASSERT(foundI, "Should identify loop variable 'i' that spans suspend points");

    TEST_PASS("IdentifyLocalVariablesSpanningSuspends");
}

// Test 9: Local variables not spanning suspends should not be included
void test_LocalVarsNotSpanningSuspendsExcluded() {
    TEST_START("LocalVarsNotSpanningSuspendsExcluded");

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

        generator coro() {
            int x = 10;
            co_yield x;
            int y = 20;  // y is declared after suspend, should not span
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT(func, "Function not found");

    auto localVars = detector.analyzeLocalVariables(func);

    // x should be found (used before suspend), y should not (declared after suspend)
    bool foundX = false;
    bool foundY = false;
    for (const auto& var : localVars) {
        if (var.name == "x") foundX = true;
        if (var.name == "y") foundY = true;
    }

    ASSERT(foundX, "Variable 'x' should be identified as it's used before suspend");
    ASSERT(!foundY, "Variable 'y' should NOT be identified as it's declared after suspend");

    TEST_PASS("LocalVarsNotSpanningSuspendsExcluded");
}

// Test 10: Frame structure includes local variables
void test_FrameIncludesLocalVariables() {
    TEST_START("FrameIncludesLocalVariables");

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

        generator count_to(int n) {
            for (int i = 0; i < n; ++i) {
                co_yield i;
            }
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count_to");

    ASSERT(func, "Function not found");

    std::string frameCode = detector.generateFrameStructure(func);

    // Frame should include local variable 'i'
    ASSERT(frameCode.find("int i") != std::string::npos,
           "Frame structure should include local variable 'i'");

    TEST_PASS("FrameIncludesLocalVariables");
}

// Test 11: Multiple local variables spanning suspends
void test_MultipleLocalVariablesSpanningSuspends() {
    TEST_START("MultipleLocalVariablesSpanningSuspends");

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

        generator complex_coro(int n) {
            int count = 0;
            double sum = 0.0;
            for (int i = 0; i < n; ++i) {
                sum += i;
                count++;
                co_yield count;
            }
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "complex_coro");

    ASSERT(func, "Function not found");

    auto localVars = detector.analyzeLocalVariables(func);

    // Should find count, sum, and i
    ASSERT(localVars.size() >= 3, "Should identify at least 3 local variables");

    bool foundCount = false, foundSum = false, foundI = false;
    for (const auto& var : localVars) {
        if (var.name == "count") foundCount = true;
        if (var.name == "sum") foundSum = true;
        if (var.name == "i") foundI = true;
    }

    ASSERT(foundCount, "Should identify 'count' variable");
    ASSERT(foundSum, "Should identify 'sum' variable");
    ASSERT(foundI, "Should identify 'i' variable");

    TEST_PASS("MultipleLocalVariablesSpanningSuspends");
}

int main() {
    std::cout << "=== Coroutine Detection and Frame Structure Tests (Story #102) ===" << std::endl;
    std::cout << "TDD Phase: RED - All tests should FAIL initially\n" << std::endl;

    test_DetectCoroutineByCoReturn();
    test_DetectCoroutineByCoYield();
    test_NonCoroutineDetection();
    test_GenerateFrameStructure();
    test_FrameIncludesFunctionPointers();
    test_FrameIncludesParameters();
    test_CountSuspendPoints();
    test_IdentifyLocalVariablesSpanningSuspends();
    test_LocalVarsNotSpanningSuspendsExcluded();
    test_FrameIncludesLocalVariables();
    test_MultipleLocalVariablesSpanningSuspends();

    std::cout << "\n=== All tests passed! ===" << std::endl;
    return 0;
}

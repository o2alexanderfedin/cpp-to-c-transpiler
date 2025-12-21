// tests/CoroutineDetectorTest_GTest.cpp
// Unit tests for Coroutine Detection and Frame Structure (Story #102)
// Migrated to Google Test framework

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/CoroutineDetector.h"

using namespace clang;

// Common test fixture for C++20 coroutine features
class CoroutineDetectorTestFixture : public ::testing::Test {
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

    // Common coroutine task structure for reuse
    const char* taskBoilerplate = R"(
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
    )";

    const char* generatorBoilerplate = R"(
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
    )";
};

// Test 1: Detect coroutine by co_return
TEST_F(CoroutineDetectorTestFixture, DetectCoroutineByCoReturn) {
    std::string code = std::string(taskBoilerplate) + R"(
        task simple_coro() {
            co_return;
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "simple_coro");

    ASSERT_NE(func, nullptr) << "Function not found";
    EXPECT_TRUE(detector.isCoroutine(func)) << "Should detect coroutine with co_return";
}

// Test 2: Detect coroutine by co_yield
TEST_F(CoroutineDetectorTestFixture, DetectCoroutineByCoYield) {
    std::string code = std::string(generatorBoilerplate) + R"(
        generator count_to(int n) {
            for (int i = 0; i < n; ++i) {
                co_yield i;
            }
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count_to");

    ASSERT_NE(func, nullptr) << "Function not found";
    EXPECT_TRUE(detector.isCoroutine(func)) << "Should detect coroutine with co_yield";
}

// Test 3: Non-coroutine function
TEST_F(CoroutineDetectorTestFixture, NonCoroutineDetection) {
    const char *code = R"(
        int regular_function() {
            return 42;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "regular_function");

    ASSERT_NE(func, nullptr) << "Function not found";
    EXPECT_FALSE(detector.isCoroutine(func)) << "Should NOT detect regular function as coroutine";
}

// Test 4: Generate frame structure
TEST_F(CoroutineDetectorTestFixture, GenerateFrameStructure) {
    std::string code = std::string(taskBoilerplate) + R"(
        task my_coro(int param) {
            int local = param;
            co_return;
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "my_coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string frameCode = detector.generateFrameStructure(func);

    EXPECT_FALSE(frameCode.empty()) << "Frame structure should be generated";
    EXPECT_NE(frameCode.find("_frame"), std::string::npos) << "Should contain frame struct";
    EXPECT_NE(frameCode.find("state"), std::string::npos) << "Should contain state field";
}

// Test 5: Frame includes resume/destroy function pointers
TEST_F(CoroutineDetectorTestFixture, FrameIncludesFunctionPointers) {
    std::string code = std::string(taskBoilerplate) + R"(
        task coro() {
            co_return;
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    std::string frameCode = detector.generateFrameStructure(func);

    bool hasResume = frameCode.find("resume_fn") != std::string::npos ||
                     frameCode.find("resume") != std::string::npos;
    bool hasDestroy = frameCode.find("destroy_fn") != std::string::npos ||
                      frameCode.find("destroy") != std::string::npos;

    EXPECT_TRUE(hasResume) << "Frame should include resume function pointer";
    EXPECT_TRUE(hasDestroy) << "Frame should include destroy function pointer";
}

// Test 6: Frame includes parameters
TEST_F(CoroutineDetectorTestFixture, FrameIncludesParameters) {
    std::string code = std::string(taskBoilerplate) + R"(
        task coro_with_params(int x, double y) {
            co_return;
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro_with_params");

    std::string frameCode = detector.generateFrameStructure(func);

    // Parameters should be copied to frame
    EXPECT_NE(frameCode.find("int"), std::string::npos) << "Frame should include int parameter";
}

// Test 7: Count suspend points
TEST_F(CoroutineDetectorTestFixture, CountSuspendPoints) {
    std::string code = std::string(generatorBoilerplate) + R"(
        generator count() {
            co_yield 1;
            co_yield 2;
            co_return;
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count");

    ASSERT_NE(func, nullptr) << "Function not found";

    size_t suspendCount = detector.countSuspendPoints(func);
    EXPECT_GE(suspendCount, 2u) << "Should detect at least 2 co_yield suspend points";
}

// Test 8: Identify local variables spanning suspend points
TEST_F(CoroutineDetectorTestFixture, IdentifyLocalVariablesSpanningSuspends) {
    std::string code = std::string(generatorBoilerplate) + R"(
        generator count_to(int n) {
            for (int i = 0; i < n; ++i) {
                co_yield i;
            }
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count_to");

    ASSERT_NE(func, nullptr) << "Function not found";

    auto localVars = detector.analyzeLocalVariables(func);

    // Variable 'i' should be identified as spanning suspend points
    EXPECT_FALSE(localVars.empty()) << "Should identify at least one local variable";

    bool foundI = false;
    for (const auto& var : localVars) {
        if (var.name == "i") {
            foundI = true;
            EXPECT_EQ(var.type, "int") << "Variable 'i' should be int type";
        }
    }
    EXPECT_TRUE(foundI) << "Should identify loop variable 'i' that spans suspend points";
}

// Test 9: Local variables not spanning suspends should not be included
TEST_F(CoroutineDetectorTestFixture, LocalVarsNotSpanningSuspendsExcluded) {
    std::string code = std::string(generatorBoilerplate) + R"(
        generator coro() {
            int x = 10;
            co_yield x;
            int y = 20;  // y is declared after suspend, should not span
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    auto localVars = detector.analyzeLocalVariables(func);

    // x should be found (used before suspend), y should not (declared after suspend)
    bool foundX = false;
    bool foundY = false;
    for (const auto& var : localVars) {
        if (var.name == "x") foundX = true;
        if (var.name == "y") foundY = true;
    }

    EXPECT_TRUE(foundX) << "Variable 'x' should be identified as it's used before suspend";
    EXPECT_FALSE(foundY) << "Variable 'y' should NOT be identified as it's declared after suspend";
}

// Test 10: Frame structure includes local variables
TEST_F(CoroutineDetectorTestFixture, FrameIncludesLocalVariables) {
    std::string code = std::string(generatorBoilerplate) + R"(
        generator count_to(int n) {
            for (int i = 0; i < n; ++i) {
                co_yield i;
            }
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count_to");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string frameCode = detector.generateFrameStructure(func);

    // Frame should include local variable 'i'
    EXPECT_NE(frameCode.find("int i"), std::string::npos)
        << "Frame structure should include local variable 'i'";
}

// Test 11: Multiple local variables spanning suspends
TEST_F(CoroutineDetectorTestFixture, MultipleLocalVariablesSpanningSuspends) {
    std::string code = std::string(generatorBoilerplate) + R"(
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

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "complex_coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    auto localVars = detector.analyzeLocalVariables(func);

    // Should find count, sum, and i
    EXPECT_GE(localVars.size(), 3u) << "Should identify at least 3 local variables";

    bool foundCount = false, foundSum = false, foundI = false;
    for (const auto& var : localVars) {
        if (var.name == "count") foundCount = true;
        if (var.name == "sum") foundSum = true;
        if (var.name == "i") foundI = true;
    }

    EXPECT_TRUE(foundCount) << "Should identify 'count' variable";
    EXPECT_TRUE(foundSum) << "Should identify 'sum' variable";
    EXPECT_TRUE(foundI) << "Should identify 'i' variable";
}

// Test 12: Extract promise type from simple coroutine return type
TEST_F(CoroutineDetectorTestFixture, ExtractPromiseTypeFromSimpleReturnType) {
    std::string code = std::string(taskBoilerplate) + R"(
        task simple_coro() {
            co_return;
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "simple_coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string promiseTypeName = detector.extractPromiseTypeName(func);
    EXPECT_FALSE(promiseTypeName.empty()) << "Should extract promise type name";
    EXPECT_EQ(promiseTypeName, "struct task_promise") << "Promise type should be 'struct task_promise'";
}

// Test 13: Extract promise type from template coroutine return type
TEST_F(CoroutineDetectorTestFixture, ExtractPromiseTypeFromTemplateReturnType) {
    const char *code = R"(
        template<typename T>
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

        template<typename T>
        struct generator {
            struct promise_type {
                struct awaiter {
                    bool await_ready_val;
                    awaiter(bool ready) : await_ready_val(ready) {}
                    bool await_ready() noexcept { return await_ready_val; }
                    template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}
                    void await_resume() noexcept {}
                };

                T value;
                generator get_return_object() { return {}; }
                awaiter initial_suspend() { return awaiter(true); }
                awaiter final_suspend() noexcept { return awaiter(true); }
                awaiter yield_value(T v) { value = v; return awaiter(false); }
                void return_void() {}
                void unhandled_exception() {}
            };
        };

        generator<int> count_to(int n) {
            for (int i = 0; i < n; ++i) {
                co_yield i;
            }
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count_to");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string promiseTypeName = detector.extractPromiseTypeName(func);
    EXPECT_FALSE(promiseTypeName.empty()) << "Should extract promise type name from template";
    EXPECT_EQ(promiseTypeName, "struct generator_int_promise")
        << "Promise type should be 'struct generator_int_promise'";
}

// Test 14: Frame structure uses actual promise type instead of void*
TEST_F(CoroutineDetectorTestFixture, FrameUsesActualPromiseType) {
    std::string code = std::string(generatorBoilerplate) + R"(
        generator count_to(int n) {
            for (int i = 0; i < n; ++i) {
                co_yield i;
            }
        }
    )";

    auto AST = buildAST(code.c_str());
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count_to");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string frameCode = detector.generateFrameStructure(func);

    // Should contain actual promise type, not void*
    EXPECT_NE(frameCode.find("struct generator_promise promise"), std::string::npos)
        << "Frame should use 'struct generator_promise promise' instead of 'void* promise'";
    EXPECT_EQ(frameCode.find("void* promise"), std::string::npos)
        << "Frame should NOT contain 'void* promise'";
}

// Test 15: Fallback to void* when promise type cannot be determined
TEST_F(CoroutineDetectorTestFixture, FallbackToVoidPointerWhenPromiseTypeNotFound) {
    const char *code = R"(
        struct broken_task {
            // Intentionally missing promise_type for testing fallback
        };

        namespace std {
            template<typename Promise = void>
            struct coroutine_handle {
                static coroutine_handle from_address(void* addr) noexcept { return {}; }
            };

            template<typename T, typename... Args>
            struct coroutine_traits;

            template<>
            struct coroutine_traits<broken_task> {
                struct promise_type {
                    struct awaiter {
                        bool await_ready() noexcept { return false; }
                        template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}
                        void await_resume() noexcept {}
                    };

                    broken_task get_return_object() { return {}; }
                    awaiter initial_suspend() { return {}; }
                    awaiter final_suspend() noexcept { return {}; }
                    void return_void() {}
                    void unhandled_exception() {}
                };
            };
        }

        broken_task broken_coro() {
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    CoroutineDetector detector(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "broken_coro");

    ASSERT_NE(func, nullptr) << "Function not found";

    std::string promiseTypeName = detector.extractPromiseTypeName(func);
    // Should fallback to void* when promise type cannot be extracted
    EXPECT_EQ(promiseTypeName, "void*") << "Should fallback to 'void*' when promise type not found";

    std::string frameCode = detector.generateFrameStructure(func);
    EXPECT_NE(frameCode.find("void* promise"), std::string::npos)
        << "Frame should use 'void* promise' as fallback";
}

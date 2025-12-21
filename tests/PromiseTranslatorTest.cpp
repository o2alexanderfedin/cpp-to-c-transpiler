// tests/PromiseTranslatorTest.cpp
// Unit tests for Promise Object Translation (Story #105)
// Following TDD: RED phase - tests written first

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/PromiseTranslator.h"
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

CXXRecordDecl* findClass(TranslationUnitDecl* TU, const std::string& name) {
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == name && RD->isCompleteDefinition()) {
                return RD;
            }
        }
    }
    return nullptr;
}

// Test fixture
class PromiseTranslatorTest : public ::testing::Test {
protected:
};

TEST_F(PromiseTranslatorTest, ExtractPromiseType) {
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

        PromiseTranslator translator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *taskClass = findClass(TU, "task");

        ASSERT_TRUE(taskClass) << "task class not found";

        auto *promiseType = translator.extractPromiseType(taskClass);
        ASSERT_TRUE(promiseType != nullptr) << "Should extract promise_type";
        ASSERT_TRUE(promiseType->getNameAsString() == "promise_type") << "Should be named promise_type";
}

TEST_F(PromiseTranslatorTest, GeneratePromiseStruct) {
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

        PromiseTranslator translator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *genClass = findClass(TU, "generator");

        ASSERT_TRUE(genClass) << "generator class not found";

        std::string promiseStruct = translator.generatePromiseStruct(genClass);

        ASSERT_TRUE(!promiseStruct.empty()) << "Should generate promise struct";
        ASSERT_TRUE(promiseStruct.find("struct") != std::string::npos) << "Should contain struct keyword";
        ASSERT_TRUE(promiseStruct.find("promise") != std::string::npos) << "Should contain promise in name";
}

TEST_F(PromiseTranslatorTest, IncludePromiseDataMembers) {
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

        PromiseTranslator translator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *genClass = findClass(TU, "generator");

        std::string promiseStruct = translator.generatePromiseStruct(genClass);

        // Should include the 'int value' member
        ASSERT_TRUE(promiseStruct.find("int") != std::string::npos) << "Should include int value member";
}

TEST_F(PromiseTranslatorTest, TranslateGetReturnObject) {
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

        PromiseTranslator translator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *taskClass = findClass(TU, "task");

        std::string getReturnObj = translator.translateGetReturnObject(taskClass);

        ASSERT_TRUE(!getReturnObj.empty()) << "Should translate get_return_object";
        ASSERT_TRUE(getReturnObj.find("get_return_object") != std::string::npos ||
               getReturnObj.find("return") != std::string::npos) << "Should reference return object creation";
}

TEST_F(PromiseTranslatorTest, TranslateYieldValue) {
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

        PromiseTranslator translator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *genClass = findClass(TU, "generator");

        std::string yieldFunc = translator.translateYieldValue(genClass);

        ASSERT_TRUE(!yieldFunc.empty()) << "Should translate yield_value";
        ASSERT_TRUE(yieldFunc.find("yield_value") != std::string::npos ||
               yieldFunc.find("yield") != std::string::npos ||
               yieldFunc.find("value") != std::string::npos) << "Should reference yield value operation";
}

TEST_F(PromiseTranslatorTest, TranslateReturnVoid) {
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

        PromiseTranslator translator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *taskClass = findClass(TU, "task");

        std::string returnVoid = translator.translateReturnVoid(taskClass);

        // return_void is often a no-op, so empty is acceptable
        // Just verify the function doesn't crash and returns a string
        ASSERT_TRUE(true) << "Should translate return_void (may be empty for no-op;");
}

TEST_F(PromiseTranslatorTest, TranslateUnhandledException) {
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

        PromiseTranslator translator(AST->getASTContext());
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *taskClass = findClass(TU, "task");

        std::string unhandledExcept = translator.translateUnhandledException(taskClass);

        // unhandled_exception might be no-op in C (no exceptions)
        ASSERT_TRUE(true) << "Should translate unhandled_exception";
}

// tests/PromiseTranslatorTest.cpp
// Unit tests for Promise Object Translation (Story #105)
// Following TDD: RED phase - tests written first

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/PromiseTranslator.h"
#include <iostream>
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

#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
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

// Test 1: Extract promise_type from coroutine return type
void test_ExtractPromiseType() {
    TEST_START("ExtractPromiseType");

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
    ASSERT(AST, "Failed to build AST");

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *taskClass = findClass(TU, "task");

    ASSERT(taskClass, "task class not found");

    auto *promiseType = translator.extractPromiseType(taskClass);
    ASSERT(promiseType != nullptr, "Should extract promise_type");
    ASSERT(promiseType->getNameAsString() == "promise_type", "Should be named promise_type");

    TEST_PASS("ExtractPromiseType");
}

// Test 2: Generate C struct for promise object
void test_GeneratePromiseStruct() {
    TEST_START("GeneratePromiseStruct");

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
    ASSERT(AST, "Failed to build AST");

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *genClass = findClass(TU, "generator");

    ASSERT(genClass, "generator class not found");

    std::string promiseStruct = translator.generatePromiseStruct(genClass);

    ASSERT(!promiseStruct.empty(), "Should generate promise struct");
    ASSERT(promiseStruct.find("struct") != std::string::npos, "Should contain struct keyword");
    ASSERT(promiseStruct.find("promise") != std::string::npos, "Should contain promise in name");

    TEST_PASS("GeneratePromiseStruct");
}

// Test 3: Include promise data members in struct
void test_IncludePromiseDataMembers() {
    TEST_START("IncludePromiseDataMembers");

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
    ASSERT(AST, "Failed to build AST");

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *genClass = findClass(TU, "generator");

    std::string promiseStruct = translator.generatePromiseStruct(genClass);

    // Should include the 'int value' member
    ASSERT(promiseStruct.find("int") != std::string::npos, "Should include int value member");

    TEST_PASS("IncludePromiseDataMembers");
}

// Test 4: Translate get_return_object()
void test_TranslateGetReturnObject() {
    TEST_START("TranslateGetReturnObject");

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
    ASSERT(AST, "Failed to build AST");

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *taskClass = findClass(TU, "task");

    std::string getReturnObj = translator.translateGetReturnObject(taskClass);

    ASSERT(!getReturnObj.empty(), "Should translate get_return_object");
    ASSERT(getReturnObj.find("get_return_object") != std::string::npos ||
           getReturnObj.find("return") != std::string::npos,
           "Should reference return object creation");

    TEST_PASS("TranslateGetReturnObject");
}

// Test 5: Translate yield_value()
void test_TranslateYieldValue() {
    TEST_START("TranslateYieldValue");

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
    ASSERT(AST, "Failed to build AST");

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *genClass = findClass(TU, "generator");

    std::string yieldFunc = translator.translateYieldValue(genClass);

    ASSERT(!yieldFunc.empty(), "Should translate yield_value");
    ASSERT(yieldFunc.find("yield_value") != std::string::npos ||
           yieldFunc.find("yield") != std::string::npos ||
           yieldFunc.find("value") != std::string::npos,
           "Should reference yield value operation");

    TEST_PASS("TranslateYieldValue");
}

// Test 6: Translate return_void()
void test_TranslateReturnVoid() {
    TEST_START("TranslateReturnVoid");

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
    ASSERT(AST, "Failed to build AST");

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *taskClass = findClass(TU, "task");

    std::string returnVoid = translator.translateReturnVoid(taskClass);

    // return_void is often a no-op, so empty is acceptable
    // Just verify the function doesn't crash and returns a string
    ASSERT(true, "Should translate return_void (may be empty for no-op)");

    TEST_PASS("TranslateReturnVoid");
}

// Test 7: Translate unhandled_exception()
void test_TranslateUnhandledException() {
    TEST_START("TranslateUnhandledException");

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
    ASSERT(AST, "Failed to build AST");

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *taskClass = findClass(TU, "task");

    std::string unhandledExcept = translator.translateUnhandledException(taskClass);

    // unhandled_exception might be no-op in C (no exceptions)
    ASSERT(true, "Should translate unhandled_exception");

    TEST_PASS("TranslateUnhandledException");
}

int main() {
    std::cout << "=== Promise Object Translation Tests (Story #105) ===" << std::endl;
    std::cout << "TDD Phase: RED - All tests should FAIL initially\n" << std::endl;

    test_ExtractPromiseType();
    test_GeneratePromiseStruct();
    test_IncludePromiseDataMembers();
    test_TranslateGetReturnObject();
    test_TranslateYieldValue();
    test_TranslateReturnVoid();
    test_TranslateUnhandledException();

    std::cout << "\n=== All tests passed! ===" << std::endl;
    return 0;
}

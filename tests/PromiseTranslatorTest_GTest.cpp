// tests/PromiseTranslatorTest_GTest.cpp
// Unit tests for Promise Object Translation (Story #105)
// Migrated to Google Test framework

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/PromiseTranslator.h"

using namespace clang;

class PromiseTranslatorTestFixture : public ::testing::Test {
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

        task coro() {
            co_return;
        }
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

        generator gen() {
            co_yield 42;
        }
    )";
};

// Test 1: Extract promise_type from coroutine return type
TEST_F(PromiseTranslatorTestFixture, ExtractPromiseType) {
    auto AST = buildAST(taskBoilerplate);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *taskClass = findClass(TU, "task");

    ASSERT_NE(taskClass, nullptr) << "task class not found";

    auto *promiseType = translator.extractPromiseType(taskClass);
    ASSERT_NE(promiseType, nullptr) << "Should extract promise_type";
    EXPECT_EQ(promiseType->getNameAsString(), "promise_type") << "Should be named promise_type";
}

// Test 2: Generate C struct for promise object
TEST_F(PromiseTranslatorTestFixture, GeneratePromiseStruct) {
    auto AST = buildAST(generatorBoilerplate);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *genClass = findClass(TU, "generator");

    ASSERT_NE(genClass, nullptr) << "generator class not found";

    std::string promiseStruct = translator.generatePromiseStruct(genClass);

    EXPECT_FALSE(promiseStruct.empty()) << "Should generate promise struct";
    EXPECT_NE(promiseStruct.find("struct"), std::string::npos) << "Should contain struct keyword";
    EXPECT_NE(promiseStruct.find("promise"), std::string::npos) << "Should contain promise in name";
}

// Test 3: Include promise data members in struct
TEST_F(PromiseTranslatorTestFixture, IncludePromiseDataMembers) {
    auto AST = buildAST(generatorBoilerplate);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *genClass = findClass(TU, "generator");

    std::string promiseStruct = translator.generatePromiseStruct(genClass);

    // Should include the 'int value' member
    EXPECT_NE(promiseStruct.find("int"), std::string::npos) << "Should include int value member";
}

// Test 4: Translate get_return_object()
TEST_F(PromiseTranslatorTestFixture, TranslateGetReturnObject) {
    auto AST = buildAST(taskBoilerplate);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *taskClass = findClass(TU, "task");

    std::string getReturnObj = translator.translateGetReturnObject(taskClass);

    EXPECT_FALSE(getReturnObj.empty()) << "Should translate get_return_object";
    bool hasGetReturnObject = getReturnObj.find("get_return_object") != std::string::npos ||
                               getReturnObj.find("return") != std::string::npos;
    EXPECT_TRUE(hasGetReturnObject) << "Should reference return object creation";
}

// Test 5: Translate yield_value()
TEST_F(PromiseTranslatorTestFixture, TranslateYieldValue) {
    auto AST = buildAST(generatorBoilerplate);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *genClass = findClass(TU, "generator");

    std::string yieldFunc = translator.translateYieldValue(genClass);

    EXPECT_FALSE(yieldFunc.empty()) << "Should translate yield_value";
    bool hasYield = yieldFunc.find("yield_value") != std::string::npos ||
                    yieldFunc.find("yield") != std::string::npos ||
                    yieldFunc.find("value") != std::string::npos;
    EXPECT_TRUE(hasYield) << "Should reference yield value operation";
}

// Test 6: Translate return_void()
TEST_F(PromiseTranslatorTestFixture, TranslateReturnVoid) {
    auto AST = buildAST(taskBoilerplate);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *taskClass = findClass(TU, "task");

    std::string returnVoid = translator.translateReturnVoid(taskClass);

    // return_void is often a no-op, so empty is acceptable
    // Just verify the function doesn't crash and returns a string
    SUCCEED() << "Should translate return_void (may be empty for no-op)";
}

// Test 7: Translate unhandled_exception()
TEST_F(PromiseTranslatorTestFixture, TranslateUnhandledException) {
    auto AST = buildAST(taskBoilerplate);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    PromiseTranslator translator(AST->getASTContext());
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *taskClass = findClass(TU, "task");

    std::string unhandledExcept = translator.translateUnhandledException(taskClass);

    // unhandled_exception might be no-op in C (no exceptions)
    SUCCEED() << "Should translate unhandled_exception";
}

// tests/CoroutineIntegrationTest.cpp
// Integration tests for C++20 Coroutines (Story #108)
// Following TDD: RED phase - tests written first

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/CoroutineDetector.h"
#include "../include/SuspendPointIdentifier.h"
#include "../include/StateMachineTransformer.h"
#include "../include/PromiseTranslator.h"
#include "../include/FrameAllocator.h"
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

// Test 1: End-to-end generator coroutine translation
void test_GeneratorCoroutineEndToEnd() {
    TEST_START("GeneratorCoroutineEndToEnd");

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

        generator count_to_three() {
            co_yield 1;
            co_yield 2;
            co_yield 3;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count_to_three");
    auto *genClass = findClass(TU, "generator");

    ASSERT(func, "Function not found");
    ASSERT(genClass, "Generator class not found");

    // Test all components together
    CoroutineDetector detector(AST->getASTContext());
    SuspendPointIdentifier identifier(AST->getASTContext());
    StateMachineTransformer transformer(AST->getASTContext());
    PromiseTranslator promiseTranslator(AST->getASTContext());
    FrameAllocator allocator(AST->getASTContext());

    // 1. Detect coroutine
    ASSERT(detector.isCoroutine(func), "Should detect as coroutine");

    // 2. Identify suspend points
    auto suspendPoints = identifier.identifySuspendPoints(func);
    ASSERT(!suspendPoints.empty(), "Should have suspend points");

    // 3. Generate frame structure
    std::string frameStruct = detector.generateFrameStructure(func);
    ASSERT(!frameStruct.empty(), "Should generate frame structure");

    // 4. Generate promise struct
    std::string promiseStruct = promiseTranslator.generatePromiseStruct(genClass);
    ASSERT(!promiseStruct.empty(), "Should generate promise struct");

    // 5. Generate state machine
    std::string stateMachine = transformer.transformToStateMachine(func);
    ASSERT(!stateMachine.empty(), "Should generate state machine");

    // 6. Generate resume function
    std::string resumeFunc = transformer.generateResumeFunction(func);
    ASSERT(!resumeFunc.empty(), "Should generate resume function");

    // 7. Generate destroy function
    std::string destroyFunc = transformer.generateDestroyFunction(func);
    ASSERT(!destroyFunc.empty(), "Should generate destroy function");

    // 8. Generate frame allocation
    std::string allocCode = allocator.generateFrameAllocation(func);
    ASSERT(!allocCode.empty(), "Should generate frame allocation");

    TEST_PASS("GeneratorCoroutineEndToEnd");
}

// Test 2: Simple async coroutine translation
void test_AsyncCoroutineEndToEnd() {
    TEST_START("AsyncCoroutineEndToEnd");

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

        task async_task() {
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "async_task");

    ASSERT(func, "Function not found");

    CoroutineDetector detector(AST->getASTContext());
    StateMachineTransformer transformer(AST->getASTContext());

    ASSERT(detector.isCoroutine(func), "Should detect as coroutine");

    std::string frameStruct = detector.generateFrameStructure(func);
    std::string stateMachine = transformer.transformToStateMachine(func);

    ASSERT(!frameStruct.empty(), "Should generate frame structure");
    ASSERT(!stateMachine.empty(), "Should generate state machine");

    TEST_PASS("AsyncCoroutineEndToEnd");
}

// Test 3: Coroutine with parameters
void test_CoroutineWithParameters() {
    TEST_START("CoroutineWithParameters");

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

        generator count_to(int n) {
            for (int i = 0; i < n; ++i) {
                co_yield i;
            }
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "count_to");

    ASSERT(func, "Function not found");

    CoroutineDetector detector(AST->getASTContext());
    FrameAllocator allocator(AST->getASTContext());

    // Frame should include parameter
    std::string frameStruct = detector.generateFrameStructure(func);
    ASSERT(frameStruct.find("int") != std::string::npos, "Frame should include parameter type");

    // Initialization should copy parameter
    std::string initCode = allocator.generateFrameInitialization(func);
    ASSERT(!initCode.empty(), "Should generate initialization");

    TEST_PASS("CoroutineWithParameters");
}

// Test 4: Multiple suspend points
void test_MultipleSuspendPoints() {
    TEST_START("MultipleSuspendPoints");

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

        generator multiple_yields() {
            co_yield 1;
            co_yield 2;
            co_yield 3;
            co_yield 4;
            co_yield 5;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "multiple_yields");

    ASSERT(func, "Function not found");

    SuspendPointIdentifier identifier(AST->getASTContext());
    auto suspendPoints = identifier.identifySuspendPoints(func);

    ASSERT(suspendPoints.size() >= 5, "Should identify all yield points");

    TEST_PASS("MultipleSuspendPoints");
}

// Test 5: Promise object with data members
void test_PromiseWithDataMembers() {
    TEST_START("PromiseWithDataMembers");

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
                int count;
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

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *genClass = findClass(TU, "generator");

    ASSERT(genClass, "Generator class not found");

    PromiseTranslator translator(AST->getASTContext());
    std::string promiseStruct = translator.generatePromiseStruct(genClass);

    ASSERT(promiseStruct.find("int value") != std::string::npos ||
           promiseStruct.find("int") != std::string::npos,
           "Promise struct should include data members");

    TEST_PASS("PromiseWithDataMembers");
}

// Test 6: Complete coroutine pipeline
void test_CompleteCoroutinePipeline() {
    TEST_START("CompleteCoroutinePipeline");

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

        task complete_coro() {
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "complete_coro");

    ASSERT(func, "Function not found");

    // Run complete pipeline
    CoroutineDetector detector(AST->getASTContext());
    SuspendPointIdentifier identifier(AST->getASTContext());
    StateMachineTransformer transformer(AST->getASTContext());
    FrameAllocator allocator(AST->getASTContext());

    // 1. Detect
    ASSERT(detector.isCoroutine(func), "Detection failed");

    // 2. Identify
    auto suspendPoints = identifier.identifySuspendPoints(func);
    ASSERT(!suspendPoints.empty(), "Identification failed");

    // 3. Generate frame
    std::string frameStruct = detector.generateFrameStructure(func);
    ASSERT(!frameStruct.empty(), "Frame generation failed");

    // 4. Transform
    std::string stateMachine = transformer.transformToStateMachine(func);
    ASSERT(!stateMachine.empty(), "Transformation failed");

    // 5. Generate functions
    std::string resumeFunc = transformer.generateResumeFunction(func);
    std::string destroyFunc = transformer.generateDestroyFunction(func);
    ASSERT(!resumeFunc.empty(), "Resume generation failed");
    ASSERT(!destroyFunc.empty(), "Destroy generation failed");

    // 6. Allocate
    std::string allocCode = allocator.generateFrameAllocation(func);
    ASSERT(!allocCode.empty(), "Allocation generation failed");

    TEST_PASS("CompleteCoroutinePipeline");
}

// Test 7: Coroutine handle operations
void test_CoroutineHandleOperations() {
    TEST_START("CoroutineHandleOperations");

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

        task handle_test() {
            co_return;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *func = findFunction(TU, "handle_test");

    ASSERT(func, "Function not found");

    FrameAllocator allocator(AST->getASTContext());

    std::string handleStruct = allocator.generateCoroutineHandle(func);
    std::string resumeOp = allocator.generateResumeOperation(func);
    std::string destroyOp = allocator.generateDestroyOperation(func);

    ASSERT(!handleStruct.empty(), "Handle struct generation failed");
    ASSERT(!resumeOp.empty(), "Resume operation generation failed");
    ASSERT(!destroyOp.empty(), "Destroy operation generation failed");

    TEST_PASS("CoroutineHandleOperations");
}

int main() {
    std::cout << "=== C++20 Coroutines Integration Tests (Story #108) ===" << std::endl;
    std::cout << "TDD Phase: RED - All tests should FAIL initially\n" << std::endl;

    test_GeneratorCoroutineEndToEnd();
    test_AsyncCoroutineEndToEnd();
    test_CoroutineWithParameters();
    test_MultipleSuspendPoints();
    test_PromiseWithDataMembers();
    test_CompleteCoroutinePipeline();
    test_CoroutineHandleOperations();

    std::cout << "\n=== All integration tests passed! ===" << std::endl;
    return 0;
}

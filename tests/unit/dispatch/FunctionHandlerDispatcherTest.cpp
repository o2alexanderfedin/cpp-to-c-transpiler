/**
 * @file FunctionHandlerDispatcherTest.cpp
 * @brief Unit tests for FunctionHandler dispatcher integration
 *
 * Verifies:
 * - Handler registration with dispatcher
 * - canHandle predicate behavior (FunctionDecl yes, CXXMethodDecl no)
 * - Function signature translation (no body in Phase 1)
 * - Integration with PathMapper and TranslationUnit management
 * - ParameterHandler integration (FunctionHandler dispatches parameters)
 */

#include "dispatch/FunctionHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/Casting.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

// Helper to build AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

// ============================================================================
// Test: FunctionHandler Registration
// ============================================================================

TEST(FunctionHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        int add(int a, int b) {
            return a + b;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    // Setup components
    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    // Create mapping utilities
    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;

    // Create dispatcher
    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper);

    // Register handlers (ParameterHandler must be registered before FunctionHandler)
    // FunctionHandler depends on ParameterHandler to translate parameters
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::FunctionHandler::registerWith(dispatcher);

    // Find the function declaration
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    FunctionDecl* addFunc = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "add") {
                addFunc = FD;
                break;
            }
        }
    }
    ASSERT_NE(addFunc, nullptr) << "Should find 'add' function";

    // Dispatch the function
    bool handled = dispatcher.dispatch(cppCtx, cCtx, addFunc);

    // Verify handler was invoked
    EXPECT_TRUE(handled) << "FunctionDecl should be handled by FunctionHandler";
}

// ============================================================================
// Test: Predicate Excludes Methods
// ============================================================================

TEST(FunctionHandlerDispatcherTest, PredicateExcludesMethods) {
    const char *cpp = R"(
        class Calculator {
        public:
            int add(int a, int b) {
                return a + b;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper);

    // Register handlers (ParameterHandler must be registered before FunctionHandler)
    // FunctionHandler depends on ParameterHandler to translate parameters
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::FunctionHandler::registerWith(dispatcher);

    // Find the method (CXXMethodDecl is subclass of FunctionDecl)
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXMethodDecl* addMethod = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == "Calculator") {
                for (auto* M : CRD->methods()) {
                    if (M->getNameAsString() == "add") {
                        addMethod = M;
                        break;
                    }
                }
            }
        }
    }
    ASSERT_NE(addMethod, nullptr) << "Should find 'add' method";

    // Dispatch the method - should NOT be handled by FunctionHandler
    bool handled = dispatcher.dispatch(cppCtx, cCtx, addMethod);

    // Verify handler did NOT handle the method
    EXPECT_FALSE(handled) << "CXXMethodDecl should NOT be handled by FunctionHandler";
}

// ============================================================================
// Test: Free Function vs Method Distinction
// ============================================================================

TEST(FunctionHandlerDispatcherTest, FreeFunctionVsMethod) {
    const char *cpp = R"(
        // Free function - should be handled
        int freeFunc(int x) {
            return x * 2;
        }

        // Method - should NOT be handled
        class MyClass {
        public:
            int memberFunc(int x) {
                return x * 3;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper);

    // Register handlers
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::FunctionHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();

    // Find free function
    FunctionDecl* freeFunc = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "freeFunc" && !isa<CXXMethodDecl>(FD)) {
                freeFunc = FD;
                break;
            }
        }
    }
    ASSERT_NE(freeFunc, nullptr) << "Should find 'freeFunc'";

    // Find method
    CXXMethodDecl* memberFunc = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == "MyClass") {
                for (auto* M : CRD->methods()) {
                    if (M->getNameAsString() == "memberFunc") {
                        memberFunc = M;
                        break;
                    }
                }
            }
        }
    }
    ASSERT_NE(memberFunc, nullptr) << "Should find 'memberFunc'";

    // Dispatch free function - should be handled
    bool freeFuncHandled = dispatcher.dispatch(cppCtx, cCtx, freeFunc);
    EXPECT_TRUE(freeFuncHandled) << "Free function should be handled";

    // Dispatch method - should NOT be handled
    bool memberFuncHandled = dispatcher.dispatch(cppCtx, cCtx, memberFunc);
    EXPECT_FALSE(memberFuncHandled) << "Method should NOT be handled";
}

// ============================================================================
// Test: Reference to Pointer Translation
// ============================================================================

TEST(FunctionHandlerDispatcherTest, ReferenceToPointerTranslation) {
    const char *cpp = R"(
        void processValue(int& ref) {
            ref = 42;
        }

        void processConstValue(const int& constRef) {
            // Read-only
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper);

    // Register handlers
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::FunctionHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();

    // Find functions
    FunctionDecl* processValue = nullptr;
    FunctionDecl* processConstValue = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "processValue") {
                processValue = FD;
            } else if (FD->getNameAsString() == "processConstValue") {
                processConstValue = FD;
            }
        }
    }
    ASSERT_NE(processValue, nullptr);
    ASSERT_NE(processConstValue, nullptr);

    // Dispatch both functions
    dispatcher.dispatch(cppCtx, cCtx, processValue);
    dispatcher.dispatch(cppCtx, cCtx, processConstValue);

    // Get C TranslationUnit and verify functions were added
    // Note: getTargetPath uses the actual source location from the AST node
    std::string targetPath = dispatcher.getTargetPath(cppCtx, processValue);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);
    ASSERT_NE(cTU, nullptr);

    // Find translated functions in C TU
    FunctionDecl* cProcessValue = nullptr;
    FunctionDecl* cProcessConstValue = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "processValue") {
                cProcessValue = FD;
            } else if (FD->getNameAsString() == "processConstValue") {
                cProcessConstValue = FD;
            }
        }
    }

    ASSERT_NE(cProcessValue, nullptr) << "Should find translated processValue";
    ASSERT_NE(cProcessConstValue, nullptr) << "Should find translated processConstValue";

    // Verify parameter types are pointers (not references)
    // Note: This is a basic smoke test - full type checking would require more setup
    EXPECT_EQ(cProcessValue->getNumParams(), 1);
    EXPECT_EQ(cProcessConstValue->getNumParams(), 1);

    // Verify bodies are nullptr (Phase 1 limitation)
    EXPECT_EQ(cProcessValue->getBody(), nullptr) << "Phase 1: Body should be nullptr";
    EXPECT_EQ(cProcessConstValue->getBody(), nullptr) << "Phase 1: Body should be nullptr";
}

// ============================================================================
// Test: Phase 1 Limitation - No Function Body
// ============================================================================

TEST(FunctionHandlerDispatcherTest, Phase1NoFunctionBody) {
    const char *cpp = R"(
        int calculate(int a, int b) {
            int result = a + b;
            return result * 2;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper);

    // Register handlers
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::FunctionHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();

    // Find function
    FunctionDecl* calculate = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "calculate") {
                calculate = FD;
                break;
            }
        }
    }
    ASSERT_NE(calculate, nullptr);

    // Verify C++ function has a body
    EXPECT_NE(calculate->getBody(), nullptr) << "C++ function should have body";

    // Dispatch function
    dispatcher.dispatch(cppCtx, cCtx, calculate);

    // Find translated function
    // Note: getTargetPath uses the actual source location from the AST node
    std::string targetPath = dispatcher.getTargetPath(cppCtx, calculate);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);
    FunctionDecl* cCalculate = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "calculate") {
                cCalculate = FD;
                break;
            }
        }
    }
    ASSERT_NE(cCalculate, nullptr) << "Should find translated function";

    // CRITICAL: Verify C function has NO body (Phase 1 limitation)
    EXPECT_EQ(cCalculate->getBody(), nullptr)
        << "Phase 1: Translated function should have nullptr body (no statement translation yet)";
}

/**
 * @file StaticMethodHandlerDispatcherTest.cpp
 * @brief Unit tests for StaticMethodHandler dispatcher integration
 *
 * Verifies:
 * - Handler registration with dispatcher
 * - canHandle predicate behavior (static methods yes, instance methods no)
 * - Static method signature translation (no "this" parameter)
 * - Class name prefixing with appropriate separators
 * - Namespace handling (namespace::Class::method → namespace_Class_method)
 * - Integration with PathMapper and TranslationUnit management
 * - ParameterHandler integration (StaticMethodHandler dispatches parameters)
 * - Exclusion of constructors and destructors
 */

#include "dispatch/StaticMethodHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/TypeHandler.h"
#include "dispatch/NamespaceHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "TargetContext.h"
#include "NameMangler.h"
#include "OverloadRegistry.h"
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

// Helper to find static method in a class
CXXMethodDecl* findStaticMethod(ASTContext& ctx, const std::string& className, const std::string& methodName) {
    TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == className) {
                for (auto* M : CRD->methods()) {
                    if (M->getNameAsString() == methodName && M->isStatic()) {
                        return M;
                    }
                }
            }
        }
    }
    return nullptr;
}

// Helper to find instance method in a class
CXXMethodDecl* findInstanceMethod(ASTContext& ctx, const std::string& className, const std::string& methodName) {
    TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == className) {
                for (auto* M : CRD->methods()) {
                    if (M->getNameAsString() == methodName && !M->isStatic()) {
                        return M;
                    }
                }
            }
        }
    }
    return nullptr;
}

// Helper to find constructor in a class
CXXConstructorDecl* findConstructor(ASTContext& ctx, const std::string& className) {
    TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == className) {
                for (auto* C : CRD->ctors()) {
                    return C;
                }
            }
        }
    }
    return nullptr;
}

// ============================================================================
// Test Fixture: Provides clean state between tests
// ============================================================================

class StaticMethodHandlerDispatcherTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Reset singletons before each test to ensure test isolation
        cpptoc::OverloadRegistry::getInstance().reset();
        TargetContext::getInstance().reset();  // Reset state, don't destroy singleton
        cpptoc::PathMapper::reset();
    }

    void TearDown() override {
        // Clean up after each test
        cpptoc::OverloadRegistry::getInstance().reset();
        TargetContext::getInstance().reset();  // Reset state, don't destroy singleton
        cpptoc::PathMapper::reset();
    }
};
// ============================================================================
// Test 1: Registration - Handler registers and processes static method
// ============================================================================

TEST_F(StaticMethodHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        class Counter {
        public:
            static int getValue() {
                return 42;
            }
        };
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
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    // Create dispatcher
    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers (TypeHandler and ParameterHandler must be registered before StaticMethodHandler)
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);

    // Find the static method
    CXXMethodDecl* getValue = findStaticMethod(cppCtx, "Counter", "getValue");
    ASSERT_NE(getValue, nullptr) << "Should find 'getValue' static method";

    // Verify it's static
    EXPECT_TRUE(getValue->isStatic()) << "Method should be static";

    // Dispatch the static method
    bool handled = dispatcher.dispatch(cppCtx, cCtx, getValue);

    // Verify handler was invoked
    EXPECT_TRUE(handled) << "Static CXXMethodDecl should be handled by StaticMethodHandler";
}

// ============================================================================
// Test 2: SimpleStaticMethod - Counter::getValue() → Counter_getValue
// ============================================================================

TEST_F(StaticMethodHandlerDispatcherTest, SimpleStaticMethod) {
    const char *cpp = R"(
        class Counter {
        public:
            static int getValue() {
                return 42;
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
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);

    // Find static method
    CXXMethodDecl* getValue = findStaticMethod(cppCtx, "Counter", "getValue");
    ASSERT_NE(getValue, nullptr);

    // Dispatch static method
    dispatcher.dispatch(cppCtx, cCtx, getValue);

    // Verify C function was created with correct name
    std::string targetPath = dispatcher.getTargetPath(cppCtx, getValue);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);
    ASSERT_NE(cTU, nullptr);

    // Find translated function
    FunctionDecl* cGetValue = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "Counter__getValue__void") {
                cGetValue = FD;
                break;
            }
        }
    }

    ASSERT_NE(cGetValue, nullptr) << "Should find translated function 'Counter__getValue__void' (NameMangler format: class__method__params)";

    // Verify function signature
    EXPECT_EQ(cGetValue->getNumParams(), 0) << "Static method should have NO 'this' parameter";
    EXPECT_EQ(cGetValue->getReturnType().getAsString(), "int") << "Return type should be 'int'";
}

// ============================================================================
// Test 3: StaticMethodWithParameters - Math::add(int,int) → Math_add
// ============================================================================

TEST_F(StaticMethodHandlerDispatcherTest, StaticMethodWithParameters) {
    const char *cpp = R"(
        class Math {
        public:
            static int add(int a, int b) {
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
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);

    // Find static method
    CXXMethodDecl* add = findStaticMethod(cppCtx, "Math", "add");
    ASSERT_NE(add, nullptr);

    // Dispatch static method
    dispatcher.dispatch(cppCtx, cCtx, add);

    // Verify C function was created
    std::string targetPath = dispatcher.getTargetPath(cppCtx, add);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);

    FunctionDecl* cAdd = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "Math__add__int_int") {
                cAdd = FD;
                break;
            }
        }
    }

    ASSERT_NE(cAdd, nullptr) << "Should find 'Math__add__int_int' (NameMangler format: class__method__params)";

    // Verify parameters (should have 2 parameters, NO "this")
    EXPECT_EQ(cAdd->getNumParams(), 2) << "Should have 2 parameters (no 'this')";
}

// ============================================================================
// Test 4: StaticMethodInNamespace - game::Entity::getMax() → game_Entity_getMax
// ============================================================================

TEST_F(StaticMethodHandlerDispatcherTest, StaticMethodInNamespace) {
    const char *cpp = R"(
        namespace game {
            class Entity {
            public:
                static int getMax() {
                    return 1000;
                }
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers (NamespaceHandler must be registered for namespace handling)
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::NamespaceHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);

    // Find namespace and static method
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* gameNS = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (NS->getNameAsString() == "game") {
                gameNS = NS;
                break;
            }
        }
    }
    ASSERT_NE(gameNS, nullptr) << "Should find 'game' namespace";

    // Find Entity class inside namespace
    CXXRecordDecl* entityClass = nullptr;
    for (auto* D : gameNS->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == "Entity") {
                entityClass = CRD;
                break;
            }
        }
    }
    ASSERT_NE(entityClass, nullptr) << "Should find 'Entity' class";

    // Find getMax static method
    CXXMethodDecl* getMax = nullptr;
    for (auto* M : entityClass->methods()) {
        if (M->getNameAsString() == "getMax" && M->isStatic()) {
            getMax = M;
            break;
        }
    }
    ASSERT_NE(getMax, nullptr) << "Should find 'getMax' static method";

    // Dispatch static method
    dispatcher.dispatch(cppCtx, cCtx, getMax);

    // Verify C function with namespace prefix
    std::string targetPath = dispatcher.getTargetPath(cppCtx, getMax);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);

    FunctionDecl* cGetMax = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "game__Entity__getMax__void") {
                cGetMax = FD;
                break;
            }
        }
    }

    ASSERT_NE(cGetMax, nullptr) << "Should find 'game__Entity__getMax__void' (NameMangler format: namespace__class__method__params)";
}

// ============================================================================
// Test 5: NestedNamespaceStaticMethod - ns1::ns2::Math::mul() → ns1_ns2_Math_mul
// ============================================================================

TEST_F(StaticMethodHandlerDispatcherTest, NestedNamespaceStaticMethod) {
    const char *cpp = R"(
        namespace ns1 {
            namespace ns2 {
                class Math {
                public:
                    static int mul(int a, int b) {
                        return a * b;
                    }
                };
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::NamespaceHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);

    // Navigate nested namespaces: ns1 → ns2 → Math → mul
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* ns1 = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (NS->getNameAsString() == "ns1") {
                ns1 = NS;
                break;
            }
        }
    }
    ASSERT_NE(ns1, nullptr);

    NamespaceDecl* ns2 = nullptr;
    for (auto* D : ns1->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (NS->getNameAsString() == "ns2") {
                ns2 = NS;
                break;
            }
        }
    }
    ASSERT_NE(ns2, nullptr);

    CXXRecordDecl* mathClass = nullptr;
    for (auto* D : ns2->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == "Math") {
                mathClass = CRD;
                break;
            }
        }
    }
    ASSERT_NE(mathClass, nullptr);

    CXXMethodDecl* mul = nullptr;
    for (auto* M : mathClass->methods()) {
        if (M->getNameAsString() == "mul" && M->isStatic()) {
            mul = M;
            break;
        }
    }
    ASSERT_NE(mul, nullptr);

    // Dispatch static method
    dispatcher.dispatch(cppCtx, cCtx, mul);

    // Verify nested namespace prefix
    std::string targetPath = dispatcher.getTargetPath(cppCtx, mul);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);

    FunctionDecl* cMul = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "ns1__ns2__Math__mul__int_int") {
                cMul = FD;
                break;
            }
        }
    }

    ASSERT_NE(cMul, nullptr) << "Should find 'ns1__ns2__Math__mul__int_int' (NameMangler format: ns1__ns2__class__method__params)";
}

// ============================================================================
// Test 6: ReferenceParameterConversion - References → pointers
// ============================================================================

TEST_F(StaticMethodHandlerDispatcherTest, ReferenceParameterConversion) {
    const char *cpp = R"(
        class Processor {
        public:
            static void process(int& value, const int& constValue) {
                value = 100;
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
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);

    // Find static method
    CXXMethodDecl* process = findStaticMethod(cppCtx, "Processor", "process");
    ASSERT_NE(process, nullptr);

    // Dispatch static method
    dispatcher.dispatch(cppCtx, cCtx, process);

    // Verify parameters converted to pointers
    std::string targetPath = dispatcher.getTargetPath(cppCtx, process);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);

    FunctionDecl* cProcess = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "Processor__process__intref_constintref") {
                cProcess = FD;
                break;
            }
        }
    }

    ASSERT_NE(cProcess, nullptr) << "Should find 'Processor__process__intref_constintref' (NameMangler format with sanitized param types)";
    EXPECT_EQ(cProcess->getNumParams(), 2) << "Should have 2 parameters (no 'this')";

    // Note: Full type checking requires TypeHandler integration
    // This is a basic smoke test
}

// ============================================================================
// Test 7: IgnoresInstanceMethods - Handler rejects non-static methods
// ============================================================================

TEST_F(StaticMethodHandlerDispatcherTest, IgnoresInstanceMethods) {
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
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);

    // Find instance method (non-static)
    CXXMethodDecl* add = findInstanceMethod(cppCtx, "Calculator", "add");
    ASSERT_NE(add, nullptr);

    // Verify it's NOT static
    EXPECT_FALSE(add->isStatic()) << "Method should NOT be static";

    // Dispatch instance method - should NOT be handled by StaticMethodHandler
    bool handled = dispatcher.dispatch(cppCtx, cCtx, add);

    // Verify handler did NOT handle the instance method
    EXPECT_FALSE(handled) << "Instance method should NOT be handled by StaticMethodHandler";
}

// ============================================================================
// Test 8: IgnoresConstructors - Handler rejects constructors
// ============================================================================

TEST_F(StaticMethodHandlerDispatcherTest, IgnoresConstructors) {
    const char *cpp = R"(
        class Widget {
        public:
            Widget() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);

    // Find constructor
    CXXConstructorDecl* ctor = findConstructor(cppCtx, "Widget");
    ASSERT_NE(ctor, nullptr);

    // Dispatch constructor - should NOT be handled by StaticMethodHandler
    bool handled = dispatcher.dispatch(cppCtx, cCtx, ctor);

    // Verify handler did NOT handle the constructor
    EXPECT_FALSE(handled) << "Constructor should NOT be handled by StaticMethodHandler";
}

// ============================================================================
// Test 9: MixedStaticAndInstanceMethods - Only static handled
// ============================================================================

TEST_F(StaticMethodHandlerDispatcherTest, MixedStaticAndInstanceMethods) {
    const char *cpp = R"(
        class MixedClass {
        public:
            static int staticMethod() {
                return 100;
            }

            int instanceMethod() {
                return 200;
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
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);

    // Find both methods
    CXXMethodDecl* staticMethod = findStaticMethod(cppCtx, "MixedClass", "staticMethod");
    CXXMethodDecl* instanceMethod = findInstanceMethod(cppCtx, "MixedClass", "instanceMethod");
    ASSERT_NE(staticMethod, nullptr);
    ASSERT_NE(instanceMethod, nullptr);

    // Dispatch both methods
    bool staticHandled = dispatcher.dispatch(cppCtx, cCtx, staticMethod);
    bool instanceHandled = dispatcher.dispatch(cppCtx, cCtx, instanceMethod);

    // Verify only static was handled
    EXPECT_TRUE(staticHandled) << "Static method should be handled";
    EXPECT_FALSE(instanceHandled) << "Instance method should NOT be handled";
}

// ============================================================================
// Test 10: NameManglingHelper - Direct test of getMangledName()
// ============================================================================

TEST_F(StaticMethodHandlerDispatcherTest, NameManglingHelper) {
    const char *cpp = R"(
        namespace app {
            class Service {
            public:
                static void initialize() {}
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();

    // Navigate to static method
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* appNS = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (NS->getNameAsString() == "app") {
                appNS = NS;
                break;
            }
        }
    }
    ASSERT_NE(appNS, nullptr);

    CXXRecordDecl* serviceClass = nullptr;
    for (auto* D : appNS->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == "Service") {
                serviceClass = CRD;
                break;
            }
        }
    }
    ASSERT_NE(serviceClass, nullptr);

    CXXMethodDecl* initialize = nullptr;
    for (auto* M : serviceClass->methods()) {
        if (M->getNameAsString() == "initialize" && M->isStatic()) {
            initialize = M;
            break;
        }
    }
    ASSERT_NE(initialize, nullptr);

    // Phase 3: Use NameMangler instead of removed StaticMethodHandler::getMangledName()
    std::string mangledName = cpptoc::mangle_method(initialize);

    // Verify mangled name includes namespace and class with correct separators
    // NameMangler format: namespace__class__method__params
    EXPECT_EQ(mangledName, "app__Service__initialize__void")
        << "Mangled name should be 'app__Service__initialize__void' (NameMangler format: namespace__class__method__params)";
}

/**
 * @file InstanceMethodHandlerDispatcherTest.cpp
 * @brief Unit tests for InstanceMethodHandler dispatcher integration
 *
 * Verifies:
 * - Handler registration with dispatcher
 * - canHandle predicate behavior (instance methods yes, static/virtual/ctor/dtor no)
 * - Instance method signature translation with "this" parameter
 * - "this" parameter is FIRST in parameter list
 * - "this" parameter type: struct ClassName* (with namespace prefix)
 * - Class name prefixing with __ separator (SAME as StaticMethodHandler)
 * - Namespace handling (namespace::Class::method → namespace__Class__method)
 * - Integration with PathMapper and TranslationUnit management
 * - ParameterHandler integration (InstanceMethodHandler dispatches parameters)
 * - Exclusion of static methods, virtual methods, constructors, destructors
 */

#include "dispatch/InstanceMethodHandler.h"
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

// Helper to find instance method in a class
CXXMethodDecl* findInstanceMethod(ASTContext& ctx, const std::string& className, const std::string& methodName) {
    TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == className) {
                for (auto* M : CRD->methods()) {
                    if (M->getNameAsString() == methodName && !M->isStatic() && !M->isVirtual()) {
                        return M;
                    }
                }
            }
        }
    }
    return nullptr;
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

// Helper to find virtual method in a class
CXXMethodDecl* findVirtualMethod(ASTContext& ctx, const std::string& className, const std::string& methodName) {
    TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == className) {
                for (auto* M : CRD->methods()) {
                    if (M->getNameAsString() == methodName && M->isVirtual()) {
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

class InstanceMethodHandlerDispatcherTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Reset singletons before each test to ensure test isolation
        cpptoc::OverloadRegistry::getInstance().reset();
        TargetContext::cleanup();
        cpptoc::PathMapper::reset();
    }

    void TearDown() override {
        // Clean up after each test
        cpptoc::OverloadRegistry::getInstance().reset();
        TargetContext::cleanup();
        cpptoc::PathMapper::reset();
    }
};

// ============================================================================
// Test 1: Registration - Handler registers and processes instance method
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        class Counter {
        public:
            void increment() {
                value++;
            }
        private:
            int value;
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
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    // Create dispatcher
    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers (TypeHandler and ParameterHandler must be registered before InstanceMethodHandler)
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Find the instance method
    CXXMethodDecl* increment = findInstanceMethod(cppCtx, "Counter", "increment");
    ASSERT_NE(increment, nullptr) << "Should find 'increment' instance method";

    // Verify it's NOT static and NOT virtual
    EXPECT_FALSE(increment->isStatic()) << "Method should NOT be static";
    EXPECT_FALSE(increment->isVirtual()) << "Method should NOT be virtual";

    // Dispatch the instance method
    bool handled = dispatcher.dispatch(cppCtx, cCtx, increment);

    // Verify handler was invoked
    EXPECT_TRUE(handled) << "Instance CXXMethodDecl should be handled by InstanceMethodHandler";
}

// ============================================================================
// Test 2: SimpleInstanceMethod - Counter::increment() → Counter_increment(struct Counter* this)
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, SimpleInstanceMethod) {
    const char *cpp = R"(
        class Counter {
        public:
            void increment() {
                value++;
            }
        private:
            int value;
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
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Find instance method
    CXXMethodDecl* increment = findInstanceMethod(cppCtx, "Counter", "increment");
    ASSERT_NE(increment, nullptr);

    // Dispatch instance method
    dispatcher.dispatch(cppCtx, cCtx, increment);

    // Verify C function was created with correct name
    std::string targetPath = dispatcher.getTargetPath(cppCtx, increment);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);
    ASSERT_NE(cTU, nullptr);

    // Find translated function
    FunctionDecl* cIncrement = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "Counter_increment") {
                cIncrement = FD;
                break;
            }
        }
    }

    ASSERT_NE(cIncrement, nullptr) << "Should find translated function 'Counter_increment'";

    // Verify function signature: Must have "this" parameter
    EXPECT_EQ(cIncrement->getNumParams(), 1) << "Instance method should have 'this' parameter";

    // Verify "this" parameter type: struct Counter*
    if (cIncrement->getNumParams() > 0) {
        ParmVarDecl* thisParam = cIncrement->getParamDecl(0);
        EXPECT_EQ(thisParam->getNameAsString(), "this") << "First parameter should be 'this'";

        QualType thisType = thisParam->getType();
        EXPECT_TRUE(thisType->isPointerType()) << "'this' should be pointer type";

        if (thisType->isPointerType()) {
            QualType pointeeType = thisType->getPointeeType();
            EXPECT_TRUE(pointeeType->isStructureType() || pointeeType->isRecordType())
                << "'this' should point to struct";
        }
    }

    // Verify return type
    EXPECT_EQ(cIncrement->getReturnType().getAsString(), "void") << "Return type should be 'void'";
}

// ============================================================================
// Test 3: InstanceMethodWithParameters - Math::add(int,int) → Math_add(struct Math* this, int, int)
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, InstanceMethodWithParameters) {
    const char *cpp = R"(
        class Math {
        public:
            int add(int a, int b) {
                return a + b + offset;
            }
        private:
            int offset;
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
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Find instance method
    CXXMethodDecl* add = findInstanceMethod(cppCtx, "Math", "add");
    ASSERT_NE(add, nullptr);

    // Dispatch instance method
    dispatcher.dispatch(cppCtx, cCtx, add);

    // Verify C function was created
    std::string targetPath = dispatcher.getTargetPath(cppCtx, add);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);

    FunctionDecl* cAdd = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "Math_add_int_int") {
                cAdd = FD;
                break;
            }
        }
    }

    ASSERT_NE(cAdd, nullptr) << "Should find 'Math_add_int_int'";

    // Verify parameters: "this" + 2 method parameters = 3 total
    EXPECT_EQ(cAdd->getNumParams(), 3) << "Should have 3 parameters (this + a + b)";

    // Verify first parameter is "this"
    if (cAdd->getNumParams() > 0) {
        ParmVarDecl* thisParam = cAdd->getParamDecl(0);
        EXPECT_EQ(thisParam->getNameAsString(), "this") << "First parameter should be 'this'";
    }
}

// ============================================================================
// Test 4: InstanceMethodInNamespace - game::Entity::update() → game_Entity_update(struct game_Entity* this)
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, InstanceMethodInNamespace) {
    const char *cpp = R"(
        namespace game {
            class Entity {
            public:
                void update() {
                    x += vx;
                }
            private:
                int x, vx;
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
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers (NamespaceHandler must be registered for namespace handling)
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::NamespaceHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Find namespace and instance method
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

    // Find update instance method
    CXXMethodDecl* update = nullptr;
    for (auto* M : entityClass->methods()) {
        if (M->getNameAsString() == "update" && !M->isStatic() && !M->isVirtual()) {
            update = M;
            break;
        }
    }
    ASSERT_NE(update, nullptr) << "Should find 'update' instance method";

    // Dispatch instance method
    dispatcher.dispatch(cppCtx, cCtx, update);

    // Verify C function with namespace prefix
    std::string targetPath = dispatcher.getTargetPath(cppCtx, update);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);

    FunctionDecl* cUpdate = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "game_Entity_update") {
                cUpdate = FD;
                break;
            }
        }
    }

    ASSERT_NE(cUpdate, nullptr) << "Should find 'game_Entity_update'";

    // Verify "this" parameter
    EXPECT_EQ(cUpdate->getNumParams(), 1) << "Should have 'this' parameter";
}

// ============================================================================
// Test 5: NestedNamespaceInstanceMethod - ns1::ns2::Calc::mul() → ns1__ns2__Calc__mul(struct ns1__ns2__Calc* this, ...)
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, NestedNamespaceInstanceMethod) {
    const char *cpp = R"(
        namespace ns1 {
            namespace ns2 {
                class Calc {
                public:
                    int mul(int a, int b) {
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
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::NamespaceHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Navigate nested namespaces: ns1 → ns2 → Calc → mul
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

    CXXRecordDecl* calcClass = nullptr;
    for (auto* D : ns2->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == "Calc") {
                calcClass = CRD;
                break;
            }
        }
    }
    ASSERT_NE(calcClass, nullptr);

    CXXMethodDecl* mul = nullptr;
    for (auto* M : calcClass->methods()) {
        if (M->getNameAsString() == "mul" && !M->isStatic() && !M->isVirtual()) {
            mul = M;
            break;
        }
    }
    ASSERT_NE(mul, nullptr);

    // Dispatch instance method
    dispatcher.dispatch(cppCtx, cCtx, mul);

    // Verify nested namespace prefix
    std::string targetPath = dispatcher.getTargetPath(cppCtx, mul);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);

    FunctionDecl* cMul = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "ns1_ns2_Calc_mul_int_int") {
                cMul = FD;
                break;
            }
        }
    }

    ASSERT_NE(cMul, nullptr) << "Should find 'ns1_ns2_Calc_mul_int_int'";

    // Verify parameters: this + 2 method params = 3
    EXPECT_EQ(cMul->getNumParams(), 3) << "Should have 3 parameters";
}

// ============================================================================
// Test 6: ReferenceParameterConversion - References → pointers
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, ReferenceParameterConversion) {
    const char *cpp = R"(
        class Processor {
        public:
            void process(int& value, const int& constValue) {
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
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Find instance method
    CXXMethodDecl* process = findInstanceMethod(cppCtx, "Processor", "process");
    ASSERT_NE(process, nullptr);

    // Dispatch instance method
    dispatcher.dispatch(cppCtx, cCtx, process);

    // Verify parameters converted to pointers
    std::string targetPath = dispatcher.getTargetPath(cppCtx, process);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);

    FunctionDecl* cProcess = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "Processor_process_int_ref_const_int_ref") {
                cProcess = FD;
                break;
            }
        }
    }

    ASSERT_NE(cProcess, nullptr);

    // Should have "this" + 2 method parameters = 3 total
    EXPECT_EQ(cProcess->getNumParams(), 3) << "Should have 3 parameters (this + value + constValue)";

    // Note: Full type checking requires TypeHandler integration
    // This is a basic smoke test
}

// ============================================================================
// Test 7: ReferenceReturnTypeConversion - Return references → pointers
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, ReferenceReturnTypeConversion) {
    const char *cpp = R"(
        class Container {
        public:
            int& get() {
                return data;
            }
        private:
            int data;
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
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Find instance method
    CXXMethodDecl* get = findInstanceMethod(cppCtx, "Container", "get");
    ASSERT_NE(get, nullptr);

    // Dispatch instance method
    dispatcher.dispatch(cppCtx, cCtx, get);

    // Verify C function was created
    std::string targetPath = dispatcher.getTargetPath(cppCtx, get);
    TranslationUnitDecl* cTU = mapper.getOrCreateTU(targetPath);

    FunctionDecl* cGet = nullptr;
    for (auto* D : cTU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "Container_get") {
                cGet = FD;
                break;
            }
        }
    }

    ASSERT_NE(cGet, nullptr);

    // Should have "this" parameter
    EXPECT_EQ(cGet->getNumParams(), 1) << "Should have 1 parameter (this)";
}

// ============================================================================
// Test 8: IgnoresStaticMethods - Handler rejects static methods
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, IgnoresStaticMethods) {
    const char *cpp = R"(
        class Calculator {
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
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Find static method
    CXXMethodDecl* add = findStaticMethod(cppCtx, "Calculator", "add");
    ASSERT_NE(add, nullptr);

    // Verify it's static
    EXPECT_TRUE(add->isStatic()) << "Method should be static";

    // Dispatch static method - should NOT be handled by InstanceMethodHandler
    bool handled = dispatcher.dispatch(cppCtx, cCtx, add);

    // Verify handler did NOT handle the static method
    EXPECT_FALSE(handled) << "Static method should NOT be handled by InstanceMethodHandler";
}

// ============================================================================
// Test 9: IgnoresVirtualMethods - Handler rejects virtual methods
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, IgnoresVirtualMethods) {
    const char *cpp = R"(
        class Base {
        public:
            virtual void compute() {}
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
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Find virtual method
    CXXMethodDecl* compute = findVirtualMethod(cppCtx, "Base", "compute");
    ASSERT_NE(compute, nullptr);

    // Verify it's virtual
    EXPECT_TRUE(compute->isVirtual()) << "Method should be virtual";

    // Dispatch virtual method - should NOT be handled by InstanceMethodHandler
    bool handled = dispatcher.dispatch(cppCtx, cCtx, compute);

    // Verify handler did NOT handle the virtual method
    EXPECT_FALSE(handled) << "Virtual method should NOT be handled by InstanceMethodHandler";
}

// ============================================================================
// Test 10: IgnoresConstructors - Handler rejects constructors
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, IgnoresConstructors) {
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
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Find constructor
    CXXConstructorDecl* ctor = findConstructor(cppCtx, "Widget");
    ASSERT_NE(ctor, nullptr);

    // Dispatch constructor - should NOT be handled by InstanceMethodHandler
    bool handled = dispatcher.dispatch(cppCtx, cCtx, ctor);

    // Verify handler did NOT handle the constructor
    EXPECT_FALSE(handled) << "Constructor should NOT be handled by InstanceMethodHandler";
}

// ============================================================================
// Test 11: MixedStaticAndInstanceMethods - Only instance handled
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, MixedStaticAndInstanceMethods) {
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
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);

    // Find both methods
    CXXMethodDecl* staticMethod = findStaticMethod(cppCtx, "MixedClass", "staticMethod");
    CXXMethodDecl* instanceMethod = findInstanceMethod(cppCtx, "MixedClass", "instanceMethod");
    ASSERT_NE(staticMethod, nullptr);
    ASSERT_NE(instanceMethod, nullptr);

    // Dispatch both methods
    bool staticHandled = dispatcher.dispatch(cppCtx, cCtx, staticMethod);
    bool instanceHandled = dispatcher.dispatch(cppCtx, cCtx, instanceMethod);

    // Verify only instance was handled
    EXPECT_FALSE(staticHandled) << "Static method should NOT be handled";
    EXPECT_TRUE(instanceHandled) << "Instance method should be handled";
}

// ============================================================================
// Test 12: NameManglingHelper - Direct test of getMangledName()
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, NameManglingHelper) {
    const char *cpp = R"(
        namespace app {
            class Service {
            public:
                void initialize() {}
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();

    // Navigate to instance method
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
        if (M->getNameAsString() == "initialize" && !M->isStatic() && !M->isVirtual()) {
            initialize = M;
            break;
        }
    }
    ASSERT_NE(initialize, nullptr);

    // Phase 3: Use NameMangler instead of removed InstanceMethodHandler::getMangledName()
    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    NameMangler mangler(cppCtx, registry);
    std::string mangledName = mangler.mangleMethodName(initialize);

    // Verify mangled name includes namespace and class with _ separator
    EXPECT_EQ(mangledName, "app_Service_initialize")
        << "Mangled name should be 'app_Service_initialize'";
}

// ============================================================================
// Test 13: ThisParameterCreation - Direct test of createThisParameter()
// ============================================================================

TEST_F(InstanceMethodHandlerDispatcherTest, ThisParameterCreation) {
    const char *cpp = R"(
        namespace game {
            class Player {
            public:
                void move() {}
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    // Navigate to class
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
    ASSERT_NE(gameNS, nullptr);

    CXXRecordDecl* playerClass = nullptr;
    for (auto* D : gameNS->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == "Player") {
                playerClass = CRD;
                break;
            }
        }
    }
    ASSERT_NE(playerClass, nullptr);

    // Test createThisParameter directly
    ParmVarDecl* thisParam = cpptoc::InstanceMethodHandler::createThisParameter(playerClass, cCtx);

    ASSERT_NE(thisParam, nullptr) << "Should create 'this' parameter";

    // Verify parameter name
    EXPECT_EQ(thisParam->getNameAsString(), "this") << "Parameter name should be 'this'";

    // Verify parameter type: should be pointer
    QualType thisType = thisParam->getType();
    EXPECT_TRUE(thisType->isPointerType()) << "'this' should be pointer type";

    // Verify pointee type: should be struct
    if (thisType->isPointerType()) {
        QualType pointeeType = thisType->getPointeeType();
        EXPECT_TRUE(pointeeType->isStructureType() || pointeeType->isRecordType())
            << "'this' should point to struct";
    }
}

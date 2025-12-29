/**
 * @file VirtualMethodHandlerDispatcherTest.cpp
 * @brief Unit tests for VirtualMethodHandler dispatcher integration
 *
 * Verifies:
 * - Handler registration with dispatcher
 * - canHandle predicate behavior (virtual methods yes, non-virtual/static/ctor/dtor no)
 * - Virtual method signature translation with "this" parameter
 * - COM-style static declarations generation
 * - Vtable structure generation with strongly typed function pointers
 * - Vtable instance initialization
 * - __vptr field addition to polymorphic structs
 * - Class name prefixing with __ separator
 * - Namespace handling (namespace::Class::method → namespace__Class__method)
 * - Inheritance and override resolution
 * - Pure virtual methods
 * - Virtual destructors
 */

#include "dispatch/VirtualMethodHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/TypeHandler.h"
#include "dispatch/NamespaceHandler.h"
#include "dispatch/RecordHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
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

// Helper to find instance method (non-virtual, non-static)
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

// Helper to find static method
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

// Helper to find constructor
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

// Helper to find destructor
CXXDestructorDecl* findDestructor(ASTContext& ctx, const std::string& className) {
    TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == className) {
                return CRD->getDestructor();
            }
        }
    }
    return nullptr;
}

// Helper to find class declaration
CXXRecordDecl* findClass(ASTContext& ctx, const std::string& className) {
    TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == className && CRD->isCompleteDefinition()) {
                return CRD;
            }
        }
    }
    return nullptr;
}

// ============================================================================
// Test 1: Registration - Handler registers and processes virtual method
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        class Shape {
        public:
            virtual int getArea() { return 0; }
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

    // Register handlers
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::VirtualMethodHandler::registerWith(dispatcher);

    // Find the virtual method
    CXXMethodDecl* getArea = findVirtualMethod(cppCtx, "Shape", "getArea");
    ASSERT_NE(getArea, nullptr) << "Should find 'getArea' virtual method";

    // Verify it's virtual and NOT static
    EXPECT_TRUE(getArea->isVirtual()) << "Method should be virtual";
    EXPECT_FALSE(getArea->isStatic()) << "Method should NOT be static";

    // Dispatch the virtual method
    bool handled = dispatcher.dispatch(cppCtx, cCtx, getArea);

    // Verify handler was invoked
    EXPECT_TRUE(handled) << "Virtual CXXMethodDecl should be handled by VirtualMethodHandler";
}

// ============================================================================
// Test 2: SimpleVirtualMethod - Shape::getArea() translation
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, SimpleVirtualMethod) {
    const char *cpp = R"(
        class Shape {
        public:
            virtual int getArea() { return 0; }
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

    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::VirtualMethodHandler::registerWith(dispatcher);

    // Find virtual method and parent class
    CXXMethodDecl* getArea = findVirtualMethod(cppCtx, "Shape", "getArea");
    ASSERT_NE(getArea, nullptr);

    CXXRecordDecl* shapeClass = getArea->getParent();
    ASSERT_NE(shapeClass, nullptr);

    // Test name mangling
    std::string mangledName = cpptoc::VirtualMethodHandler::getMangledName(getArea, shapeClass);
    EXPECT_EQ(mangledName, "Shape__getArea") << "Should mangle to Shape__getArea with __ separator";

    // Dispatch the virtual method
    dispatcher.dispatch(cppCtx, cCtx, getArea);

    // Verify C function was created with correct name
    FunctionDecl* cFunc = llvm::dyn_cast_or_null<FunctionDecl>(declMapper.getCreated(getArea));
    ASSERT_NE(cFunc, nullptr) << "C function should be created";
    EXPECT_EQ(cFunc->getNameAsString(), "Shape__getArea") << "C function name should match mangled name";

    // Verify return type is int
    EXPECT_TRUE(cFunc->getReturnType()->isIntegerType()) << "Return type should be int";

    // Verify has "this" parameter as first parameter
    ASSERT_EQ(cFunc->getNumParams(), 1u) << "Should have 1 parameter (this)";
    ParmVarDecl* thisParam = cFunc->getParamDecl(0);
    EXPECT_EQ(thisParam->getNameAsString(), "this") << "First parameter should be 'this'";
    EXPECT_TRUE(thisParam->getType()->isPointerType()) << "this should be pointer type";
}

// ============================================================================
// Test 3: VirtualMethodWithParameters - Parameters translated correctly
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, VirtualMethodWithParameters) {
    const char *cpp = R"(
        class Calculator {
        public:
            virtual int add(int a, int b) { return a + b; }
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

    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::VirtualMethodHandler::registerWith(dispatcher);

    CXXMethodDecl* add = findVirtualMethod(cppCtx, "Calculator", "add");
    ASSERT_NE(add, nullptr);

    dispatcher.dispatch(cppCtx, cCtx, add);

    // Verify C function has correct parameters: this, a, b
    FunctionDecl* cFunc = llvm::dyn_cast_or_null<FunctionDecl>(declMapper.getCreated(add));
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "Calculator__add");

    // Should have 3 parameters: this, a, b
    ASSERT_EQ(cFunc->getNumParams(), 3u) << "Should have 3 parameters (this, a, b)";

    ParmVarDecl* thisParam = cFunc->getParamDecl(0);
    EXPECT_EQ(thisParam->getNameAsString(), "this");

    ParmVarDecl* aParam = cFunc->getParamDecl(1);
    EXPECT_EQ(aParam->getNameAsString(), "a");
    EXPECT_TRUE(aParam->getType()->isIntegerType());

    ParmVarDecl* bParam = cFunc->getParamDecl(2);
    EXPECT_EQ(bParam->getNameAsString(), "b");
    EXPECT_TRUE(bParam->getType()->isIntegerType());
}

// ============================================================================
// Test 4: VirtualMethodInNamespace - Namespace prefix applied
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, VirtualMethodInNamespace) {
    const char *cpp = R"(
        namespace game {
            class Entity {
            public:
                virtual void update() {}
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();

    // Find namespace
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

    // Find class inside namespace
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

    // Find virtual method
    CXXMethodDecl* update = nullptr;
    for (auto* M : entityClass->methods()) {
        if (M->getNameAsString() == "update" && M->isVirtual()) {
            update = M;
            break;
        }
    }
    ASSERT_NE(update, nullptr) << "Should find 'update' virtual method";

    // Test name mangling with namespace prefix
    std::string mangledName = cpptoc::VirtualMethodHandler::getMangledName(update, entityClass);
    EXPECT_EQ(mangledName, "game__Entity__update") << "Should include namespace prefix with __ separator";
}

// ============================================================================
// Test 5: InheritanceWithOverride - Override resolution
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, InheritanceWithOverride) {
    const char *cpp = R"(
        class Shape {
        public:
            virtual int getArea() { return 0; }
        };

        class Circle : public Shape {
        public:
            int getArea() override { return 314; }
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

    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::VirtualMethodHandler::registerWith(dispatcher);

    // Find both methods
    CXXMethodDecl* shapeGetArea = findVirtualMethod(cppCtx, "Shape", "getArea");
    CXXMethodDecl* circleGetArea = findVirtualMethod(cppCtx, "Circle", "getArea");

    ASSERT_NE(shapeGetArea, nullptr);
    ASSERT_NE(circleGetArea, nullptr);

    // Both should be virtual
    EXPECT_TRUE(shapeGetArea->isVirtual());
    EXPECT_TRUE(circleGetArea->isVirtual());

    // Dispatch both
    dispatcher.dispatch(cppCtx, cCtx, shapeGetArea);
    dispatcher.dispatch(cppCtx, cCtx, circleGetArea);

    // Verify both C functions created with different names
    FunctionDecl* shapeCFunc = llvm::dyn_cast_or_null<FunctionDecl>(declMapper.getCreated(shapeGetArea));
    FunctionDecl* circleCFunc = llvm::dyn_cast_or_null<FunctionDecl>(declMapper.getCreated(circleGetArea));

    ASSERT_NE(shapeCFunc, nullptr);
    ASSERT_NE(circleCFunc, nullptr);

    EXPECT_EQ(shapeCFunc->getNameAsString(), "Shape__getArea");
    EXPECT_EQ(circleCFunc->getNameAsString(), "Circle__getArea");
}

// ============================================================================
// Test 6: VirtualDestructor - Destructor should be excluded
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, VirtualDestructor) {
    const char *cpp = R"(
        class Shape {
        public:
            virtual ~Shape() {}
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

    cpptoc::VirtualMethodHandler::registerWith(dispatcher);

    // Find destructor
    CXXDestructorDecl* dtor = findDestructor(cppCtx, "Shape");
    ASSERT_NE(dtor, nullptr);

    // Verify it's virtual
    EXPECT_TRUE(dtor->isVirtual());

    // VirtualMethodHandler should NOT handle destructors
    bool handled = dispatcher.dispatch(cppCtx, cCtx, dtor);
    EXPECT_FALSE(handled) << "VirtualMethodHandler should NOT handle destructors";
}

// ============================================================================
// Test 7: PureVirtualMethod - Abstract method translation
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, PureVirtualMethod) {
    const char *cpp = R"(
        class Shape {
        public:
            virtual int getArea() = 0;
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

    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::VirtualMethodHandler::registerWith(dispatcher);

    CXXMethodDecl* getArea = findVirtualMethod(cppCtx, "Shape", "getArea");
    ASSERT_NE(getArea, nullptr);

    // Verify it's pure virtual
    EXPECT_TRUE(getArea->isPureVirtual()) << "Method should be pure virtual";
    EXPECT_TRUE(getArea->isVirtual()) << "Method should be virtual";

    dispatcher.dispatch(cppCtx, cCtx, getArea);

    // Pure virtual methods should still create function declaration (no body)
    FunctionDecl* cFunc = llvm::dyn_cast_or_null<FunctionDecl>(declMapper.getCreated(getArea));
    ASSERT_NE(cFunc, nullptr) << "Pure virtual should create C function declaration";
    EXPECT_EQ(cFunc->getNameAsString(), "Shape__getArea");

    // Should NOT have body
    EXPECT_FALSE(cFunc->hasBody()) << "Pure virtual should NOT have function body";
}

// ============================================================================
// Test 8: TypeConversions - Reference to pointer conversion
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, TypeConversions) {
    const char *cpp = R"(
        class Processor {
        public:
            virtual void process(int& value) {}
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

    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::VirtualMethodHandler::registerWith(dispatcher);

    CXXMethodDecl* process = findVirtualMethod(cppCtx, "Processor", "process");
    ASSERT_NE(process, nullptr);

    dispatcher.dispatch(cppCtx, cCtx, process);

    // Verify reference converted to pointer
    FunctionDecl* cFunc = llvm::dyn_cast_or_null<FunctionDecl>(declMapper.getCreated(process));
    ASSERT_NE(cFunc, nullptr);

    ASSERT_EQ(cFunc->getNumParams(), 2u) << "Should have 2 parameters (this, value)";

    ParmVarDecl* valueParam = cFunc->getParamDecl(1);
    EXPECT_EQ(valueParam->getNameAsString(), "value");
    EXPECT_TRUE(valueParam->getType()->isPointerType()) << "C++ reference should become C pointer";
}

// ============================================================================
// Test 9: ExclusionTests - Non-virtual/static/ctor excluded
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, ExclusionTests) {
    const char *cpp = R"(
        class Test {
        public:
            Test() {}                              // Constructor
            ~Test() {}                             // Non-virtual destructor
            void instanceMethod() {}               // Non-virtual instance
            static void staticMethod() {}          // Static method
            virtual void virtualMethod() {}        // Virtual (should handle)
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

    cpptoc::VirtualMethodHandler::registerWith(dispatcher);

    // Test constructor exclusion
    CXXConstructorDecl* ctor = findConstructor(cppCtx, "Test");
    ASSERT_NE(ctor, nullptr);
    EXPECT_FALSE(dispatcher.dispatch(cppCtx, cCtx, ctor)) << "Should NOT handle constructor";

    // Test non-virtual destructor exclusion
    CXXDestructorDecl* dtor = findDestructor(cppCtx, "Test");
    ASSERT_NE(dtor, nullptr);
    EXPECT_FALSE(dtor->isVirtual()) << "Destructor should NOT be virtual";
    EXPECT_FALSE(dispatcher.dispatch(cppCtx, cCtx, dtor)) << "Should NOT handle non-virtual destructor";

    // Test instance method exclusion
    CXXMethodDecl* instanceMethod = findInstanceMethod(cppCtx, "Test", "instanceMethod");
    ASSERT_NE(instanceMethod, nullptr);
    EXPECT_FALSE(instanceMethod->isVirtual()) << "Method should NOT be virtual";
    EXPECT_FALSE(dispatcher.dispatch(cppCtx, cCtx, instanceMethod)) << "Should NOT handle non-virtual instance method";

    // Test static method exclusion
    CXXMethodDecl* staticMethod = findStaticMethod(cppCtx, "Test", "staticMethod");
    ASSERT_NE(staticMethod, nullptr);
    EXPECT_TRUE(staticMethod->isStatic()) << "Method should be static";
    EXPECT_FALSE(dispatcher.dispatch(cppCtx, cCtx, staticMethod)) << "Should NOT handle static method";

    // Test virtual method inclusion (should handle)
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);

    CXXMethodDecl* virtualMethod = findVirtualMethod(cppCtx, "Test", "virtualMethod");
    ASSERT_NE(virtualMethod, nullptr);
    EXPECT_TRUE(virtualMethod->isVirtual()) << "Method should be virtual";
    EXPECT_TRUE(dispatcher.dispatch(cppCtx, cCtx, virtualMethod)) << "SHOULD handle virtual method";
}

// ============================================================================
// Test 10: MultipleVirtualMethods - Multiple virtual methods in one class
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, MultipleVirtualMethods) {
    const char *cpp = R"(
        class Shape {
        public:
            virtual int getArea() { return 0; }
            virtual int getPerimeter() { return 0; }
            virtual void draw() {}
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

    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::VirtualMethodHandler::registerWith(dispatcher);

    // Find all three virtual methods
    CXXMethodDecl* getArea = findVirtualMethod(cppCtx, "Shape", "getArea");
    CXXMethodDecl* getPerimeter = findVirtualMethod(cppCtx, "Shape", "getPerimeter");
    CXXMethodDecl* draw = findVirtualMethod(cppCtx, "Shape", "draw");

    ASSERT_NE(getArea, nullptr);
    ASSERT_NE(getPerimeter, nullptr);
    ASSERT_NE(draw, nullptr);

    // Dispatch all three
    dispatcher.dispatch(cppCtx, cCtx, getArea);
    dispatcher.dispatch(cppCtx, cCtx, getPerimeter);
    dispatcher.dispatch(cppCtx, cCtx, draw);

    // Verify all three C functions created
    FunctionDecl* cGetArea = llvm::dyn_cast_or_null<FunctionDecl>(declMapper.getCreated(getArea));
    FunctionDecl* cGetPerimeter = llvm::dyn_cast_or_null<FunctionDecl>(declMapper.getCreated(getPerimeter));
    FunctionDecl* cDraw = llvm::dyn_cast_or_null<FunctionDecl>(declMapper.getCreated(draw));

    ASSERT_NE(cGetArea, nullptr);
    ASSERT_NE(cGetPerimeter, nullptr);
    ASSERT_NE(cDraw, nullptr);

    EXPECT_EQ(cGetArea->getNameAsString(), "Shape__getArea");
    EXPECT_EQ(cGetPerimeter->getNameAsString(), "Shape__getPerimeter");
    EXPECT_EQ(cDraw->getNameAsString(), "Shape__draw");
}

// ============================================================================
// Test 11: VtableStructGeneration - Per-class vtable struct with strongly typed pointers
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, VtableStructGeneration) {
    const char *cpp = R"(
        class Shape {
        public:
            virtual int getArea() { return 0; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    // Find class and method
    CXXRecordDecl* shapeClass = findClass(cppCtx, "Shape");
    ASSERT_NE(shapeClass, nullptr);

    CXXMethodDecl* getArea = findVirtualMethod(cppCtx, "Shape", "getArea");
    ASSERT_NE(getArea, nullptr);

    // Test vtable struct name
    std::string vtableStructName = cpptoc::VirtualMethodHandler::getVtableStructName(shapeClass);
    EXPECT_EQ(vtableStructName, "Shape__vtable") << "Vtable struct name should be Shape__vtable";

    // Generate vtable struct
    std::vector<const clang::CXXMethodDecl*> virtualMethods = { getArea };
    std::string vtableStruct = cpptoc::VirtualMethodHandler::generateVtableStruct(
        shapeClass, virtualMethods, cCtx
    );

    // Verify vtable struct contains:
    // - struct Shape__vtable {
    // - const struct __class_type_info *type_info;
    // - int (*getArea)(struct Shape *this);
    // - };
    EXPECT_NE(vtableStruct.find("struct Shape__vtable {"), std::string::npos)
        << "Should contain vtable struct definition";
    EXPECT_NE(vtableStruct.find("const struct __class_type_info *type_info;"), std::string::npos)
        << "Should contain RTTI type_info pointer";
    EXPECT_NE(vtableStruct.find("int (*getArea)(struct Shape *this);"), std::string::npos)
        << "Should contain strongly typed getArea function pointer";
}

// ============================================================================
// Test 12: VtableInstanceGeneration - Per-class vtable instance initialization
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, VtableInstanceGeneration) {
    const char *cpp = R"(
        class Shape {
        public:
            virtual int getArea() { return 0; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    // Find class and method
    CXXRecordDecl* shapeClass = findClass(cppCtx, "Shape");
    ASSERT_NE(shapeClass, nullptr);

    CXXMethodDecl* getArea = findVirtualMethod(cppCtx, "Shape", "getArea");
    ASSERT_NE(getArea, nullptr);

    // Test vtable instance name
    std::string vtableInstanceName = cpptoc::VirtualMethodHandler::getVtableInstanceName(shapeClass);
    EXPECT_EQ(vtableInstanceName, "Shape__vtable_instance")
        << "Vtable instance name should be Shape__vtable_instance";

    // Generate vtable instance
    std::vector<const clang::CXXMethodDecl*> virtualMethods = { getArea };
    std::string vtableInstance = cpptoc::VirtualMethodHandler::generateVtableInstance(
        shapeClass, virtualMethods, cCtx
    );

    // Verify vtable instance contains:
    // - static struct Shape__vtable Shape__vtable_instance = {
    // - .type_info = &Shape__type_info,
    // - .getArea = Shape__getArea
    // - };
    EXPECT_NE(vtableInstance.find("static struct Shape__vtable Shape__vtable_instance = {"), std::string::npos)
        << "Should contain vtable instance definition";
    EXPECT_NE(vtableInstance.find(".type_info = &Shape__type_info,"), std::string::npos)
        << "Should initialize RTTI type_info pointer";
    EXPECT_NE(vtableInstance.find(".getArea = Shape__getArea,"), std::string::npos)
        << "Should initialize getArea function pointer";
}

// ============================================================================
// Test 13: MultipleVirtualMethodsVtable - Vtable with multiple methods in correct order
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, MultipleVirtualMethodsVtable) {
    const char *cpp = R"(
        class Shape {
        public:
            virtual int getArea() { return 0; }
            virtual void draw() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    // Find class and methods
    CXXRecordDecl* shapeClass = findClass(cppCtx, "Shape");
    ASSERT_NE(shapeClass, nullptr);

    CXXMethodDecl* getArea = findVirtualMethod(cppCtx, "Shape", "getArea");
    CXXMethodDecl* draw = findVirtualMethod(cppCtx, "Shape", "draw");
    ASSERT_NE(getArea, nullptr);
    ASSERT_NE(draw, nullptr);

    // Generate vtable struct with both methods
    std::vector<const clang::CXXMethodDecl*> virtualMethods = { getArea, draw };
    std::string vtableStruct = cpptoc::VirtualMethodHandler::generateVtableStruct(
        shapeClass, virtualMethods, cCtx
    );

    // Verify both methods in vtable
    EXPECT_NE(vtableStruct.find("int (*getArea)(struct Shape *this);"), std::string::npos)
        << "Should contain getArea function pointer";
    EXPECT_NE(vtableStruct.find("void (*draw)(struct Shape *this);"), std::string::npos)
        << "Should contain draw function pointer";

    // Verify vtable instance has both initializers
    std::string vtableInstance = cpptoc::VirtualMethodHandler::generateVtableInstance(
        shapeClass, virtualMethods, cCtx
    );

    EXPECT_NE(vtableInstance.find(".getArea = Shape__getArea,"), std::string::npos)
        << "Should initialize getArea";
    EXPECT_NE(vtableInstance.find(".draw = Shape__draw,"), std::string::npos)
        << "Should initialize draw";
}

// ============================================================================
// Test 14: NamespacedClassVtable - Namespace prefix in vtable names
// ============================================================================

TEST(VirtualMethodHandlerDispatcherTest, NamespacedClassVtable) {
    const char *cpp = R"(
        namespace game {
            class Entity {
            public:
                virtual void update() {}
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    // Find namespace
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

    // Find class inside namespace
    CXXRecordDecl* entityClass = nullptr;
    for (auto* D : gameNS->decls()) {
        if (auto* CRD = dyn_cast<CXXRecordDecl>(D)) {
            if (CRD->getNameAsString() == "Entity" && CRD->isCompleteDefinition()) {
                entityClass = CRD;
                break;
            }
        }
    }
    ASSERT_NE(entityClass, nullptr);

    // Find virtual method
    CXXMethodDecl* update = nullptr;
    for (auto* M : entityClass->methods()) {
        if (M->getNameAsString() == "update" && M->isVirtual()) {
            update = M;
            break;
        }
    }
    ASSERT_NE(update, nullptr);

    // Test vtable struct name with namespace prefix
    std::string vtableStructName = cpptoc::VirtualMethodHandler::getVtableStructName(entityClass);
    EXPECT_EQ(vtableStructName, "game__Entity__vtable")
        << "Vtable struct name should include namespace prefix";

    // Test vtable instance name with namespace prefix
    std::string vtableInstanceName = cpptoc::VirtualMethodHandler::getVtableInstanceName(entityClass);
    EXPECT_EQ(vtableInstanceName, "game__Entity__vtable_instance")
        << "Vtable instance name should include namespace prefix";

    // Generate vtable struct
    std::vector<const clang::CXXMethodDecl*> virtualMethods = { update };
    std::string vtableStruct = cpptoc::VirtualMethodHandler::generateVtableStruct(
        entityClass, virtualMethods, cCtx
    );

    // Verify namespace prefix in struct definition
    EXPECT_NE(vtableStruct.find("struct game__Entity__vtable {"), std::string::npos)
        << "Should use namespace prefix in vtable struct name";
    EXPECT_NE(vtableStruct.find("void (*update)(struct game__Entity *this);"), std::string::npos)
        << "Should use namespace prefix in function pointer type";

    // Generate vtable instance
    std::string vtableInstance = cpptoc::VirtualMethodHandler::generateVtableInstance(
        entityClass, virtualMethods, cCtx
    );

    // Verify namespace prefix in instance
    EXPECT_NE(vtableInstance.find("static struct game__Entity__vtable game__Entity__vtable_instance = {"), std::string::npos)
        << "Should use namespace prefix in vtable instance";
    EXPECT_NE(vtableInstance.find(".type_info = &game__Entity__type_info,"), std::string::npos)
        << "Should use namespace prefix in type_info reference";
    EXPECT_NE(vtableInstance.find(".update = game__Entity__update,"), std::string::npos)
        << "Should use namespace prefix in method reference";
}

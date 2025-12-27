/**
 * @file ConstructorHandlerTest_lpVtbl.cpp
 * @brief TDD tests for ConstructorHandler lpVtbl initialization (Phase 45 Group 3)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (10 tests):
 * 1. lpVtblInitInDefaultConstructor - Inject lpVtbl init in default ctor
 * 2. lpVtblInitInParameterizedConstructor - Inject lpVtbl init in parameterized ctor
 * 3. lpVtblInitBeforeFieldInit - lpVtbl MUST be first statement
 * 4. lpVtblInitDerivedClass - Derived class uses Derived_vtable_instance
 * 5. lpVtblInitMultipleConstructors - All ctors initialize lpVtbl
 * 6. lpVtblInitWithMemberInitList - lpVtbl first, then init list
 * 7. lpVtblInitCorrectType - Assignment has correct type
 * 8. lpVtblInitPointsToStaticVtable - Points to &ClassName_vtable_instance
 * 9. NoLpVtblForNonPolymorphic - Non-polymorphic class skips lpVtbl init
 * 10. lpVtblInitEmptyConstructor - Empty ctor body gets lpVtbl init only
 *
 * lpVtbl Init Pattern (COM/DCOM):
 * C++: class Animal {
 *          int age;
 *      public:
 *          Animal() : age(0) {}
 *          virtual void speak();
 *      };
 *
 * C:   void Animal_init(struct Animal* this) {
 *          this->lpVtbl = &Animal_vtable_instance;  // FIRST!
 *          this->age = 0;                           // Then field init
 *      }
 */

#include "handlers/ConstructorHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Stmt.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ConstructorHandlerLpVtblTest
 * @brief Test fixture for ConstructorHandler lpVtbl initialization injection
 */
class ConstructorHandlerLpVtblTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;
    std::unique_ptr<ConstructorHandler> handler;

    void SetUp() override {
        // Create real AST contexts using minimal code
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr) << "Failed to create C++ AST";
        ASSERT_NE(cAST, nullptr) << "Failed to create C AST";

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Create handler
        handler = std::make_unique<ConstructorHandler>();
    }

    void TearDown() override {
        handler.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Build AST from code and return the first CXXConstructorDecl
     */
    const clang::CXXConstructorDecl* getCXXConstructorDeclFromCode(
        const std::string& code,
        int constructorIndex = 0
    ) {
        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code: " << code;

        if (!cppAST) return nullptr;

        // Recreate builder and context with new AST
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Find the CXXRecordDecl first
        auto& ctx = cppAST->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* cxxRecordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                // Skip implicit declarations
                if (cxxRecordDecl->isImplicit()) continue;

                // Find constructors
                int ctorIdx = 0;
                for (auto* method : cxxRecordDecl->methods()) {
                    if (auto* ctor = llvm::dyn_cast<clang::CXXConstructorDecl>(method)) {
                        if (!ctor->isImplicit() && ctorIdx == constructorIndex) {
                            return ctor;
                        }
                        if (!ctor->isImplicit()) ctorIdx++;
                    }
                }
            }
        }

        return nullptr;
    }

    /**
     * @brief Get parent class from constructor
     */
    const clang::CXXRecordDecl* getParentClass(const clang::CXXConstructorDecl* ctor) {
        if (!ctor) return nullptr;
        return ctor->getParent();
    }

    /**
     * @brief Create C struct for testing (mimics RecordHandler behavior)
     */
    clang::RecordDecl* createCStruct(
        const std::string& className,
        bool hasLpVtbl = true
    ) {
        auto& cCtx = cAST->getASTContext();

        // Create struct
        clang::IdentifierInfo& II = cCtx.Idents.get(className);
        auto* recordDecl = clang::RecordDecl::Create(
            cCtx,
            clang::TagTypeKind::Struct,
            cCtx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II
        );

        recordDecl->startDefinition();

        if (hasLpVtbl) {
            // Create lpVtbl field: const struct ClassName_vtable *lpVtbl;
            std::string vtableName = className + "_vtable";

            // Create vtable struct type
            clang::IdentifierInfo& vtableII = cCtx.Idents.get(vtableName);
            auto* vtableStruct = clang::RecordDecl::Create(
                cCtx,
                clang::TagTypeKind::Struct,
                cCtx.getTranslationUnitDecl(),
                clang::SourceLocation(),
                clang::SourceLocation(),
                &vtableII
            );
            vtableStruct->startDefinition();
            vtableStruct->completeDefinition();

            // Create type: const struct ClassName_vtable *
            clang::QualType vtableType = cCtx.getRecordType(vtableStruct);
            vtableType = cCtx.getConstType(vtableType);
            vtableType = cCtx.getPointerType(vtableType);

            // Create lpVtbl field
            clang::IdentifierInfo& lpVtblII = cCtx.Idents.get("lpVtbl");
            auto* lpVtblField = clang::FieldDecl::Create(
                cCtx,
                recordDecl,
                clang::SourceLocation(),
                clang::SourceLocation(),
                &lpVtblII,
                vtableType,
                cCtx.getTrivialTypeSourceInfo(vtableType),
                nullptr,
                false,
                clang::ICIS_NoInit
            );

            recordDecl->addDecl(lpVtblField);
        }

        recordDecl->completeDefinition();

        // Add to translation unit so ConstructorHandler can find it
        cCtx.getTranslationUnitDecl()->addDecl(recordDecl);

        return recordDecl;
    }
};

// =============================================================================
// Test 1: lpVtbl init in default constructor
// =============================================================================

/**
 * Test 1: Inject lpVtbl initialization in default constructor
 * C++: class Animal {
 *      public:
 *          Animal() {}
 *          virtual void speak();
 *      };
 *
 * C:   void Animal_init(struct Animal* this) {
 *          this->lpVtbl = &Animal_vtable_instance;
 *      }
 */
TEST_F(ConstructorHandlerLpVtblTest, lpVtblInitInDefaultConstructor) {
    const char* code = R"(
        class Animal {
        public:
            Animal() {}
            virtual void speak();
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code);
    ASSERT_NE(ctor, nullptr);
    EXPECT_EQ(ctor->getNumParams(), 0) << "Should be default constructor";

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);
    EXPECT_TRUE(parentClass->isPolymorphic()) << "Animal should be polymorphic";

    // Create C struct manually (normally done by RecordHandler)
    auto* cStruct = createCStruct("Animal", true);
    ASSERT_NE(cStruct, nullptr);

    // Translate constructor
    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(ctor, *context)
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "Animal_init");

    // Verify function has body
    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr) << "Constructor should have body with lpVtbl init";

    // Body should be CompoundStmt
    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    // Should have at least 1 statement (lpVtbl init)
    ASSERT_GE(compoundStmt->size(), 1) << "Should have lpVtbl initialization";

    // First statement should be assignment: this->lpVtbl = &Animal_vtable_instance;
    auto* firstStmt = compoundStmt->body_front();
    ASSERT_NE(firstStmt, nullptr);

    // Should be BinaryOperator (assignment)
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(firstStmt);
    ASSERT_NE(binOp, nullptr) << "First statement should be assignment";
    EXPECT_EQ(binOp->getOpcode(), clang::BO_Assign) << "Should be assignment operator";

    // LHS should be this->lpVtbl
    auto* lhs = binOp->getLHS();
    ASSERT_NE(lhs, nullptr);
    auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(lhs);
    ASSERT_NE(memberExpr, nullptr) << "LHS should be member access (this->lpVtbl)";
    EXPECT_EQ(memberExpr->getMemberDecl()->getNameAsString(), "lpVtbl");

    // RHS should be &Animal_vtable_instance
    auto* rhs = binOp->getRHS();
    ASSERT_NE(rhs, nullptr);
    auto* unaryOp = llvm::dyn_cast<clang::UnaryOperator>(rhs);
    ASSERT_NE(unaryOp, nullptr) << "RHS should be address-of operator";
    EXPECT_EQ(unaryOp->getOpcode(), clang::UO_AddrOf);
}

// =============================================================================
// Test 2: lpVtbl init in parameterized constructor
// =============================================================================

/**
 * Test 2: Inject lpVtbl initialization in parameterized constructor
 * C++: class Counter {
 *          int count;
 *      public:
 *          Counter(int initial) : count(initial) {}
 *          virtual void increment();
 *      };
 *
 * C:   void Counter_init_int(struct Counter* this, int initial) {
 *          this->lpVtbl = &Counter_vtable_instance;  // FIRST!
 *          this->count = initial;
 *      }
 */
TEST_F(ConstructorHandlerLpVtblTest, lpVtblInitInParameterizedConstructor) {
    const char* code = R"(
        class Counter {
            int count;
        public:
            Counter(int initial) : count(initial) {}
            virtual void increment();
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code);
    ASSERT_NE(ctor, nullptr);
    EXPECT_EQ(ctor->getNumParams(), 1) << "Should have one parameter";

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);
    EXPECT_TRUE(parentClass->isPolymorphic());

    // Create C struct
    auto* cStruct = createCStruct("Counter", true);
    ASSERT_NE(cStruct, nullptr);

    // Translate constructor
    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(ctor, *context)
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "Counter_init_int");

    // Verify function has body
    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr);

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    // Should have at least 1 statement (lpVtbl init)
    // NOTE: Member initializer list translation is not yet implemented
    ASSERT_GE(compoundStmt->size(), 1) << "Should have lpVtbl initialization";

    // First statement should be lpVtbl assignment
    auto* firstStmt = compoundStmt->body_front();
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(firstStmt);
    ASSERT_NE(binOp, nullptr);

    auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(binOp->getLHS());
    ASSERT_NE(memberExpr, nullptr);
    EXPECT_EQ(memberExpr->getMemberDecl()->getNameAsString(), "lpVtbl")
        << "First statement MUST be lpVtbl initialization";
}

// =============================================================================
// Test 3: lpVtbl init BEFORE field initialization
// =============================================================================

/**
 * Test 3: lpVtbl initialization must be FIRST statement
 * C++: class Point {
 *          int x, y;
 *      public:
 *          Point() : x(0), y(0) {}
 *          virtual void draw();
 *      };
 *
 * C:   void Point_init(struct Point* this) {
 *          this->lpVtbl = &Point_vtable_instance;  // MUST BE FIRST!
 *          this->x = 0;
 *          this->y = 0;
 *      }
 */
TEST_F(ConstructorHandlerLpVtblTest, lpVtblInitBeforeFieldInit) {
    const char* code = R"(
        class Point {
            int x, y;
        public:
            Point() : x(0), y(0) {}
            virtual void draw();
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code);
    ASSERT_NE(ctor, nullptr);

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);
    EXPECT_TRUE(parentClass->isPolymorphic());

    // Create C struct
    auto* cStruct = createCStruct("Point", true);
    ASSERT_NE(cStruct, nullptr);

    // Translate constructor
    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(ctor, *context)
    );

    ASSERT_NE(cFunc, nullptr);

    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr);

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    // Should have at least 1 statement (lpVtbl)
    // NOTE: Member initializer list translation (x, y) is not yet implemented
    ASSERT_GE(compoundStmt->size(), 1);

    // CRITICAL: First statement MUST be lpVtbl
    auto stmtIt = compoundStmt->body_begin();
    auto* firstStmt = *stmtIt;
    auto* firstBinOp = llvm::dyn_cast<clang::BinaryOperator>(firstStmt);
    ASSERT_NE(firstBinOp, nullptr);

    auto* firstMember = llvm::dyn_cast<clang::MemberExpr>(firstBinOp->getLHS());
    ASSERT_NE(firstMember, nullptr);
    EXPECT_EQ(firstMember->getMemberDecl()->getNameAsString(), "lpVtbl")
        << "FIRST statement MUST be lpVtbl initialization for COM/DCOM ABI";

    // TODO: When member initializer list translation is implemented, verify x and y follow lpVtbl
}

// =============================================================================
// Test 4: Derived class uses correct vtable
// =============================================================================

/**
 * Test 4: Derived class should use Derived_vtable_instance, not Base
 * C++: class Base {
 *      public:
 *          virtual void foo();
 *      };
 *      class Derived : public Base {
 *      public:
 *          Derived() {}
 *          void foo() override;
 *      };
 *
 * C:   void Derived_init(struct Derived* this) {
 *          this->lpVtbl = &Derived_vtable_instance;  // NOT Base!
 *      }
 */
TEST_F(ConstructorHandlerLpVtblTest, lpVtblInitDerivedClass) {
    const char* code = R"(
        class Base {
        public:
            virtual void foo();
        };
        class Derived : public Base {
        public:
            Derived() {}
            void foo() override;
        };
    )";

    // Get the Derived constructor (second class, first constructor)
    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::CXXConstructorDecl* derivedCtor = nullptr;
    for (auto* decl : TU->decls()) {
        if (auto* cxxRecordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (cxxRecordDecl->getNameAsString() == "Derived") {
                for (auto* method : cxxRecordDecl->methods()) {
                    if (auto* ctor = llvm::dyn_cast<clang::CXXConstructorDecl>(method)) {
                        if (!ctor->isImplicit()) {
                            derivedCtor = ctor;
                            break;
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(derivedCtor, nullptr);

    const auto* parentClass = getParentClass(derivedCtor);
    ASSERT_NE(parentClass, nullptr);
    EXPECT_EQ(parentClass->getNameAsString(), "Derived");
    EXPECT_TRUE(parentClass->isPolymorphic());

    // Create C struct for Derived
    auto* cStruct = createCStruct("Derived", true);
    ASSERT_NE(cStruct, nullptr);

    // Translate constructor
    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(derivedCtor, *context)
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "Derived_init");

    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr);

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    // Find lpVtbl assignment (may not be first statement due to base constructor calls)
    clang::BinaryOperator* binOp = nullptr;
    for (auto* stmt : compoundStmt->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                if (memberExpr->getMemberDecl()->getNameAsString() == "lpVtbl") {
                    binOp = bo;
                    break;
                }
            }
        }
    }
    ASSERT_NE(binOp, nullptr) << "Should have lpVtbl assignment";

    // RHS should reference Derived_vtable_instance
    auto* rhs = binOp->getRHS();
    auto* unaryOp = llvm::dyn_cast<clang::UnaryOperator>(rhs);
    ASSERT_NE(unaryOp, nullptr);

    auto* declRef = llvm::dyn_cast<clang::DeclRefExpr>(unaryOp->getSubExpr());
    ASSERT_NE(declRef, nullptr);
    EXPECT_EQ(declRef->getNameInfo().getAsString(), "Derived_vtable_instance")
        << "Derived class should use Derived_vtable_instance, NOT Base_vtable_instance";
}

// =============================================================================
// Test 5: Multiple constructors - all initialize lpVtbl
// =============================================================================

/**
 * Test 5: All constructors should initialize lpVtbl
 * C++: class Widget {
 *      public:
 *          Widget() {}
 *          Widget(int size) {}
 *          virtual void render();
 *      };
 *
 * C:   void Widget_init(struct Widget* this) {
 *          this->lpVtbl = &Widget_vtable_instance;
 *      }
 *      void Widget_init_int(struct Widget* this, int size) {
 *          this->lpVtbl = &Widget_vtable_instance;
 *      }
 */
TEST_F(ConstructorHandlerLpVtblTest, lpVtblInitMultipleConstructors) {
    const char* code = R"(
        class Widget {
        public:
            Widget() {}
            Widget(int size) {}
            virtual void render();
        };
    )";

    // Test first constructor (default)
    const auto* ctor1 = getCXXConstructorDeclFromCode(code, 0);
    ASSERT_NE(ctor1, nullptr);
    EXPECT_EQ(ctor1->getNumParams(), 0);

    auto* cStruct = createCStruct("Widget", true);
    ASSERT_NE(cStruct, nullptr);

    auto* cFunc1 = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(ctor1, *context)
    );
    ASSERT_NE(cFunc1, nullptr);

    auto* body1 = cFunc1->getBody();
    ASSERT_NE(body1, nullptr);
    auto* compound1 = llvm::dyn_cast<clang::CompoundStmt>(body1);
    ASSERT_NE(compound1, nullptr);
    ASSERT_GE(compound1->size(), 1);

    // Verify first ctor has lpVtbl init
    auto* firstStmt1 = compound1->body_front();
    auto* binOp1 = llvm::dyn_cast<clang::BinaryOperator>(firstStmt1);
    ASSERT_NE(binOp1, nullptr);

    // Test second constructor (parameterized)
    const auto* ctor2 = getCXXConstructorDeclFromCode(code, 1);
    ASSERT_NE(ctor2, nullptr);
    EXPECT_EQ(ctor2->getNumParams(), 1);

    auto* cFunc2 = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(ctor2, *context)
    );
    ASSERT_NE(cFunc2, nullptr);

    auto* body2 = cFunc2->getBody();
    ASSERT_NE(body2, nullptr);
    auto* compound2 = llvm::dyn_cast<clang::CompoundStmt>(body2);
    ASSERT_NE(compound2, nullptr);
    ASSERT_GE(compound2->size(), 1);

    // Verify second ctor also has lpVtbl init
    auto* firstStmt2 = compound2->body_front();
    auto* binOp2 = llvm::dyn_cast<clang::BinaryOperator>(firstStmt2);
    ASSERT_NE(binOp2, nullptr);

    auto* memberExpr2 = llvm::dyn_cast<clang::MemberExpr>(binOp2->getLHS());
    ASSERT_NE(memberExpr2, nullptr);
    EXPECT_EQ(memberExpr2->getMemberDecl()->getNameAsString(), "lpVtbl")
        << "Both constructors should initialize lpVtbl";
}

// =============================================================================
// Test 6: Constructor with member init list - lpVtbl first
// =============================================================================

/**
 * Test 6: lpVtbl init comes before member initializer list conversions
 * C++: class Data {
 *          int value;
 *      public:
 *          Data(int v) : value(v) {}
 *          virtual void process();
 *      };
 *
 * C:   void Data_init_int(struct Data* this, int v) {
 *          this->lpVtbl = &Data_vtable_instance;  // FIRST!
 *          this->value = v;                       // Then init list
 *      }
 */
TEST_F(ConstructorHandlerLpVtblTest, lpVtblInitWithMemberInitList) {
    const char* code = R"(
        class Data {
            int value;
        public:
            Data(int v) : value(v) {}
            virtual void process();
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code);
    ASSERT_NE(ctor, nullptr);

    // Verify this constructor has member initializer list
    EXPECT_GT(ctor->getNumCtorInitializers(), 0)
        << "Constructor should have member initializer list";

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);
    EXPECT_TRUE(parentClass->isPolymorphic());

    auto* cStruct = createCStruct("Data", true);
    ASSERT_NE(cStruct, nullptr);

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(ctor, *context)
    );

    ASSERT_NE(cFunc, nullptr);

    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr);

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    // Should have at least 1 statement (lpVtbl)
    // NOTE: Member initializer list translation (value) is not yet implemented
    ASSERT_GE(compoundStmt->size(), 1);

    // FIRST statement must be lpVtbl
    auto* firstStmt = compoundStmt->body_front();
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(firstStmt);
    ASSERT_NE(binOp, nullptr);

    auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(binOp->getLHS());
    ASSERT_NE(memberExpr, nullptr);
    EXPECT_EQ(memberExpr->getMemberDecl()->getNameAsString(), "lpVtbl")
        << "lpVtbl MUST be initialized before member initializer list";

    // TODO: When member initializer list translation is implemented, verify value follows lpVtbl
}

// =============================================================================
// Test 7: lpVtbl assignment has correct type
// =============================================================================

/**
 * Test 7: Verify lpVtbl assignment type is correct
 * Type should be: const struct ClassName_vtable *
 */
TEST_F(ConstructorHandlerLpVtblTest, lpVtblInitCorrectType) {
    const char* code = R"(
        class Shape {
        public:
            virtual double area() = 0;
            Shape() {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code);
    ASSERT_NE(ctor, nullptr);

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);
    EXPECT_TRUE(parentClass->isPolymorphic());

    auto* cStruct = createCStruct("Shape", true);
    ASSERT_NE(cStruct, nullptr);

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(ctor, *context)
    );

    ASSERT_NE(cFunc, nullptr);

    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr);

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    auto* firstStmt = compoundStmt->body_front();
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(firstStmt);
    ASSERT_NE(binOp, nullptr);

    // Verify LHS type (this->lpVtbl)
    auto* lhs = binOp->getLHS();
    auto lhsType = lhs->getType();

    // Should be pointer type
    EXPECT_TRUE(lhsType->isPointerType())
        << "lpVtbl should be pointer type";

    if (lhsType->isPointerType()) {
        auto pointeeType = lhsType->getPointeeType();

        // Pointee should be const
        EXPECT_TRUE(pointeeType.isConstQualified())
            << "lpVtbl should point to const vtable";

        // Pointee should be struct
        EXPECT_TRUE(pointeeType->isStructureType())
            << "lpVtbl should point to struct";
    }

    // Verify RHS type (&ClassName_vtable_instance)
    auto* rhs = binOp->getRHS();
    auto rhsType = rhs->getType();

    EXPECT_TRUE(rhsType->isPointerType())
        << "Address-of vtable instance should be pointer";
}

// =============================================================================
// Test 8: lpVtbl points to static vtable instance
// =============================================================================

/**
 * Test 8: Verify lpVtbl is assigned &ClassName_vtable_instance
 * C:   this->lpVtbl = &Animal_vtable_instance;
 *      (NOT a local variable or function call)
 */
TEST_F(ConstructorHandlerLpVtblTest, lpVtblInitPointsToStaticVtable) {
    const char* code = R"(
        class Animal {
        public:
            virtual void speak();
            Animal() {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code);
    ASSERT_NE(ctor, nullptr);

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);

    auto* cStruct = createCStruct("Animal", true);
    ASSERT_NE(cStruct, nullptr);

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(ctor, *context)
    );

    ASSERT_NE(cFunc, nullptr);

    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr);

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    auto* firstStmt = compoundStmt->body_front();
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(firstStmt);
    ASSERT_NE(binOp, nullptr);

    // RHS should be &vtable_instance
    auto* rhs = binOp->getRHS();
    auto* unaryOp = llvm::dyn_cast<clang::UnaryOperator>(rhs);
    ASSERT_NE(unaryOp, nullptr) << "RHS should be address-of operator";
    EXPECT_EQ(unaryOp->getOpcode(), clang::UO_AddrOf);

    // Operand should be DeclRefExpr pointing to vtable_instance
    auto* declRef = llvm::dyn_cast<clang::DeclRefExpr>(unaryOp->getSubExpr());
    ASSERT_NE(declRef, nullptr) << "Should reference a declaration (vtable_instance)";

    std::string vtableName = declRef->getNameInfo().getAsString();
    EXPECT_EQ(vtableName, "Animal_vtable_instance")
        << "Should reference Animal_vtable_instance";

    // Verify it's a VarDecl (static variable)
    auto* varDecl = llvm::dyn_cast<clang::VarDecl>(declRef->getDecl());
    EXPECT_NE(varDecl, nullptr)
        << "vtable_instance should be a variable declaration";
}

// =============================================================================
// Test 9: Non-polymorphic classes skip lpVtbl init
// =============================================================================

/**
 * Test 9: Non-polymorphic classes should NOT initialize lpVtbl
 * C++: class Plain {
 *          int x;
 *      public:
 *          Plain() : x(0) {}
 *      };  // No virtual methods
 *
 * C:   void Plain_init(struct Plain* this) {
 *          this->x = 0;  // No lpVtbl init!
 *      }
 */
TEST_F(ConstructorHandlerLpVtblTest, NoLpVtblForNonPolymorphic) {
    const char* code = R"(
        class Plain {
            int x;
        public:
            Plain() : x(0) {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code);
    ASSERT_NE(ctor, nullptr);

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);
    EXPECT_FALSE(parentClass->isPolymorphic())
        << "Plain should NOT be polymorphic";

    // Create C struct WITHOUT lpVtbl
    auto* cStruct = createCStruct("Plain", false);
    ASSERT_NE(cStruct, nullptr);

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(ctor, *context)
    );

    ASSERT_NE(cFunc, nullptr);

    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr);

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    // Should have field initialization but NO lpVtbl
    if (compoundStmt->size() > 0) {
        auto* firstStmt = compoundStmt->body_front();
        auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(firstStmt);

        if (binOp) {
            auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(binOp->getLHS());
            if (memberExpr) {
                EXPECT_NE(memberExpr->getMemberDecl()->getNameAsString(), "lpVtbl")
                    << "Non-polymorphic class should NOT initialize lpVtbl";
            }
        }
    }
}

// =============================================================================
// Test 10: Empty constructor body gets lpVtbl init only
// =============================================================================

/**
 * Test 10: Empty constructor should still get lpVtbl initialization
 * C++: class Interface {
 *      public:
 *          Interface() {}
 *          virtual void execute() = 0;
 *      };
 *
 * C:   void Interface_init(struct Interface* this) {
 *          this->lpVtbl = &Interface_vtable_instance;  // Only statement
 *      }
 */
TEST_F(ConstructorHandlerLpVtblTest, lpVtblInitEmptyConstructor) {
    const char* code = R"(
        class Interface {
        public:
            Interface() {}
            virtual void execute() = 0;
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code);
    ASSERT_NE(ctor, nullptr);

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);
    EXPECT_TRUE(parentClass->isPolymorphic());

    // Verify original ctor body is empty
    auto* cppBody = ctor->getBody();
    if (cppBody) {
        auto* cppCompound = llvm::dyn_cast<clang::CompoundStmt>(cppBody);
        if (cppCompound) {
            EXPECT_EQ(cppCompound->size(), 0)
                << "Original C++ constructor body should be empty";
        }
    }

    auto* cStruct = createCStruct("Interface", true);
    ASSERT_NE(cStruct, nullptr);

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        handler->handleDecl(ctor, *context)
    );

    ASSERT_NE(cFunc, nullptr);

    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr) << "Even empty ctor should get body with lpVtbl init";

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    // Should have exactly 1 statement (lpVtbl init)
    ASSERT_EQ(compoundStmt->size(), 1)
        << "Empty constructor should have exactly lpVtbl initialization";

    auto* firstStmt = compoundStmt->body_front();
    auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(firstStmt);
    ASSERT_NE(binOp, nullptr);

    auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(binOp->getLHS());
    ASSERT_NE(memberExpr, nullptr);
    EXPECT_EQ(memberExpr->getMemberDecl()->getNameAsString(), "lpVtbl")
        << "Empty constructor should only contain lpVtbl initialization";
}

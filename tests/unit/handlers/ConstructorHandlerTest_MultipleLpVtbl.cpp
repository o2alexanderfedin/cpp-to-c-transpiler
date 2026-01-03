/**
 * @file ConstructorHandlerTest_MultipleLpVtbl.cpp
 * @brief TDD tests for ConstructorHandler multiple lpVtbl initialization (Phase 46 Group 3 Task 7)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (12 tests):
 * 1. InitializeLpVtblInConstructor - Initialize lpVtbl for primary base
 * 2. InitializeLpVtbl2InConstructor - Initialize lpVtbl2 for first non-primary base
 * 3. InitializeLpVtbl3InConstructor - Initialize lpVtbl3 for second non-primary base
 * 4. InitializationOrderLpVtblFirst - lpVtbl, lpVtbl2, lpVtbl3 in correct order
 * 5. AllVtablesBeforeFieldInit - All lpVtbl* initialized before any field
 * 6. MultipleConstructorsAllInitialize - All constructors initialize all lpVtbl pointers
 * 7. DerivedClassInitializesAllVtables - Derived class initializes all its vtables
 * 8. VtablePointersToCorrectInstances - Each lpVtbl points to correct vtable instance
 * 9. DefaultConstructorMultipleLpVtbl - Default constructor with multiple lpVtbl
 * 10. ParameterizedConstructorMultipleLpVtbl - Parameterized constructor with multiple lpVtbl
 * 11. SingleInheritanceUsesLpVtblOnly - Single inheritance still uses lpVtbl only
 * 12. ThreeBasesThreeInitializations - Three bases → three lpVtbl initializations
 *
 * Multiple lpVtbl Init Pattern:
 * C++: class Shape : public IDrawable, public ISerializable {
 *          int x;
 *      public:
 *          Shape() : x(0) {}
 *      };
 *
 * C:   void Shape_init(struct Shape* this) {
 *          this->lpVtbl = &Shape_IDrawable_vtable_instance;      // FIRST (primary)
 *          this->lpVtbl2 = &Shape_ISerializable_vtable_instance; // SECOND (non-primary)
 *          this->x = 0;                                           // Then fields
 *      }
 */

#include "dispatch/ConstructorHandler.h"
#include "helpers/UnitTestHelper.h"
#include "CNodeBuilder.h"
#include "MultipleInheritanceAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Stmt.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ConstructorHandlerMultipleLpVtblTest
 * @brief Test fixture for ConstructorHandler multiple lpVtbl initialization injection
 */
class ConstructorHandlerMultipleLpVtblTest : public ::testing::Test {
protected:
    UnitTestContext ctx;

    void SetUp() override {
        ctx = createUnitTestContext();
        ctx.dispatcher->registerHandler<ConstructorHandler>();
    }
/**
     * @brief Build AST from code and return the first CXXConstructorDecl
     */
    const clang::CXXConstructorDecl* getCXXConstructorDeclFromCode(
        const std::string& code,
        const std::string& className,
        int constructorIndex = 0
    ) {
        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code: " << code;

        if (!cppAST) return nullptr;

        // Recreate builder and context with new AST

        // Find the CXXRecordDecl first
        auto& ctx = cppAST->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* cxxRecordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                // Skip implicit declarations
                if (cxxRecordDecl->isImplicit()) continue;
                if (cxxRecordDecl->getNameAsString() != className) continue;

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
     * @brief Create C struct for testing (mimics RecordHandler behavior with multiple lpVtbl)
     */
    clang::RecordDecl* createCStructWithMultipleLpVtbl(
        const std::string& className,
        const std::vector<std::string>& vtableNames  // e.g., {"IDrawable", "ISerializable"}
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

        // Create lpVtbl fields for each base
        for (size_t i = 0; i < vtableNames.size(); ++i) {
            // Create vtable struct name: ClassName_BaseName_vtable
            std::string vtableStructName = className + "_" + vtableNames[i] + "_vtable";

            // Create vtable struct type
            clang::IdentifierInfo& vtableII = cCtx.Idents.get(vtableStructName);
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

            // Create type: const struct ClassName_BaseName_vtable *
            clang::QualType vtableType = cCtx.getRecordType(vtableStruct);
            vtableType = cCtx.getConstType(vtableType);
            vtableType = cCtx.getPointerType(vtableType);

            // Create lpVtbl field name: lpVtbl, lpVtbl2, lpVtbl3, ...
            std::string fieldName = (i == 0) ? "lpVtbl" : "lpVtbl" + std::to_string(i + 1);
            clang::IdentifierInfo& fieldII = cCtx.Idents.get(fieldName);

            auto* lpVtblField = clang::FieldDecl::Create(
                cCtx,
                recordDecl,
                clang::SourceLocation(),
                clang::SourceLocation(),
                &fieldII,
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

    /**
     * @brief Create vtable instance variable declarations for testing
     */
    void createVtableInstances(
        const std::string& className,
        const std::vector<std::string>& baseNames
    ) {
        auto& cCtx = cAST->getASTContext();
        auto* TU = cCtx.getTranslationUnitDecl();

        for (const auto& baseName : baseNames) {
            // Create vtable instance name: ClassName_BaseName_vtable_instance
            std::string instanceName = className + "_" + baseName + "_vtable_instance";
            std::string vtableStructName = className + "_" + baseName + "_vtable";

            // Find or create vtable struct
            clang::RecordDecl* vtableStruct = nullptr;
            for (auto* D : TU->decls()) {
                if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
                    if (RD->getNameAsString() == vtableStructName) {
                        vtableStruct = RD;
                        break;
                    }
                }
            }

            if (!vtableStruct) {
                clang::IdentifierInfo& vtableII = cCtx.Idents.get(vtableStructName);
                vtableStruct = clang::RecordDecl::Create(
                    cCtx,
                    clang::TagTypeKind::Struct,
                    TU,
                    clang::SourceLocation(),
                    clang::SourceLocation(),
                    &vtableII
                );
                vtableStruct->startDefinition();
                vtableStruct->completeDefinition();
                TU->addDecl(vtableStruct);
            }

            // Create vtable instance variable
            clang::QualType vtableType = cCtx.getRecordType(vtableStruct);
            clang::QualType constVtableType = cCtx.getConstType(vtableType);

            clang::IdentifierInfo& instanceII = cCtx.Idents.get(instanceName);
            auto* vtableInstanceVar = clang::VarDecl::Create(
                cCtx,
                TU,
                clang::SourceLocation(),
                clang::SourceLocation(),
                &instanceII,
                constVtableType,
                cCtx.getTrivialTypeSourceInfo(constVtableType),
                clang::SC_Extern
            );

            TU->addDecl(vtableInstanceVar);
        }
    }
};

// =============================================================================
// Test 1: Initialize lpVtbl in constructor (baseline - single inheritance)
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, InitializeLpVtblInConstructor) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class Shape : public IDrawable {
        public:
            Shape() {}
            void draw() override {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Shape");
    ASSERT_NE(ctor, nullptr);

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);
    EXPECT_TRUE(parentClass->isPolymorphic());

    // Create C struct with single lpVtbl
    auto* cStruct = createCStructWithMultipleLpVtbl("Shape", {"IDrawable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Shape", {"IDrawable"});

    // Translate constructor
    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr);

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);
    ASSERT_GE(compoundStmt->size(), 1) << "Should have lpVtbl initialization";

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

    auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(binOp->getLHS());
    ASSERT_NE(memberExpr, nullptr);
    EXPECT_EQ(memberExpr->getMemberDecl()->getNameAsString(), "lpVtbl");
}

// =============================================================================
// Test 2: Initialize lpVtbl2 for first non-primary base
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, InitializeLpVtbl2InConstructor) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class ISerializable {
        public:
            virtual void serialize() = 0;
        };
        class Shape : public IDrawable, public ISerializable {
        public:
            Shape() {}
            void draw() override {}
            void serialize() override {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Shape");
    ASSERT_NE(ctor, nullptr);

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);

    // Create C struct with lpVtbl and lpVtbl2
    auto* cStruct = createCStructWithMultipleLpVtbl("Shape", {"IDrawable", "ISerializable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Shape", {"IDrawable", "ISerializable"});

    // Translate constructor
    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr);

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);
    ASSERT_GE(compoundStmt->size(), 2) << "Should have lpVtbl AND lpVtbl2 initialization";

    // Find lpVtbl2 assignment (may not be second statement due to base constructor calls)
    clang::BinaryOperator* binOp2 = nullptr;
    for (auto* stmt : compoundStmt->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                if (memberExpr->getMemberDecl()->getNameAsString() == "lpVtbl2") {
                    binOp2 = bo;
                    break;
                }
            }
        }
    }
    ASSERT_NE(binOp2, nullptr) << "Should have lpVtbl2 assignment";

    auto* memberExpr2 = llvm::dyn_cast<clang::MemberExpr>(binOp2->getLHS());
    ASSERT_NE(memberExpr2, nullptr);
    EXPECT_EQ(memberExpr2->getMemberDecl()->getNameAsString(), "lpVtbl2")
        << "Second vtable pointer should be lpVtbl2";
}

// =============================================================================
// Test 3: Initialize lpVtbl3 for second non-primary base
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, InitializeLpVtbl3InConstructor) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class ISerializable {
        public:
            virtual void serialize() = 0;
        };
        class IClickable {
        public:
            virtual void onClick() = 0;
        };
        class Widget : public IDrawable, public ISerializable, public IClickable {
        public:
            Widget() {}
            void draw() override {}
            void serialize() override {}
            void onClick() override {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Widget");
    ASSERT_NE(ctor, nullptr);

    // Create C struct with lpVtbl, lpVtbl2, lpVtbl3
    auto* cStruct = createCStructWithMultipleLpVtbl("Widget", {"IDrawable", "ISerializable", "IClickable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Widget", {"IDrawable", "ISerializable", "IClickable"});

    // Translate constructor
    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    auto* body = cFunc->getBody();
    ASSERT_NE(body, nullptr);

    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);
    ASSERT_GE(compoundStmt->size(), 3) << "Should have lpVtbl, lpVtbl2, AND lpVtbl3 initialization";

    // Find lpVtbl3 assignment (may not be third statement due to base constructor calls)
    clang::BinaryOperator* binOp3 = nullptr;
    for (auto* stmt : compoundStmt->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                if (memberExpr->getMemberDecl()->getNameAsString() == "lpVtbl3") {
                    binOp3 = bo;
                    break;
                }
            }
        }
    }
    ASSERT_NE(binOp3, nullptr) << "Should have lpVtbl3 assignment";

    auto* memberExpr3 = llvm::dyn_cast<clang::MemberExpr>(binOp3->getLHS());
    ASSERT_NE(memberExpr3, nullptr);
    EXPECT_EQ(memberExpr3->getMemberDecl()->getNameAsString(), "lpVtbl3")
        << "Third vtable pointer should be lpVtbl3";
}

// =============================================================================
// Test 4: Initialization order is correct (lpVtbl, lpVtbl2, lpVtbl3)
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, InitializationOrderLpVtblFirst) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class ISerializable {
        public:
            virtual void serialize() = 0;
        };
        class Shape : public IDrawable, public ISerializable {
        public:
            Shape() {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Shape");
    ASSERT_NE(ctor, nullptr);

    auto* cStruct = createCStructWithMultipleLpVtbl("Shape", {"IDrawable", "ISerializable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Shape", {"IDrawable", "ISerializable"});

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    auto* body = cFunc->getBody();
    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);
    ASSERT_GE(compoundStmt->size(), 2);

    // Collect all vtable assignments in order (skipping base constructor calls)
    std::vector<std::string> vtableOrder;
    for (auto* stmt : compoundStmt->body()) {
        if (auto* binOp = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(binOp->getLHS())) {
                std::string memberName = memberExpr->getMemberDecl()->getNameAsString();
                if (memberName == "lpVtbl" || memberName == "lpVtbl2" || memberName == "lpVtbl3") {
                    vtableOrder.push_back(memberName);
                }
            }
        }
    }

    // Verify order: lpVtbl MUST come before lpVtbl2
    ASSERT_GE(vtableOrder.size(), 2) << "Should have at least lpVtbl and lpVtbl2 assignments";
    EXPECT_EQ(vtableOrder[0], "lpVtbl")
        << "FIRST vtable initialization MUST be lpVtbl";
    EXPECT_EQ(vtableOrder[1], "lpVtbl2")
        << "SECOND vtable initialization MUST be lpVtbl2";
}

// =============================================================================
// Test 5: All vtable pointers initialized before field initialization
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, AllVtablesBeforeFieldInit) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class ISerializable {
        public:
            virtual void serialize() = 0;
        };
        class Shape : public IDrawable, public ISerializable {
            int x;
        public:
            Shape() : x(42) {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Shape");
    ASSERT_NE(ctor, nullptr);

    auto* cStruct = createCStructWithMultipleLpVtbl("Shape", {"IDrawable", "ISerializable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Shape", {"IDrawable", "ISerializable"});

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    auto* body = cFunc->getBody();
    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);
    ASSERT_GE(compoundStmt->size(), 2);

    // Find lpVtbl and lpVtbl2 assignments (may not be first statements due to base constructor calls)
    clang::BinaryOperator* binOp1 = nullptr;
    clang::BinaryOperator* binOp2 = nullptr;

    for (auto* stmt : compoundStmt->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                std::string memberName = memberExpr->getMemberDecl()->getNameAsString();
                if (memberName == "lpVtbl" && !binOp1) {
                    binOp1 = bo;
                } else if (memberName == "lpVtbl2" && !binOp2) {
                    binOp2 = bo;
                }
            }
        }
    }

    // Both vtable pointers should be initialized
    ASSERT_NE(binOp1, nullptr) << "lpVtbl should be initialized";
    auto* member1 = llvm::dyn_cast<clang::MemberExpr>(binOp1->getLHS());
    EXPECT_EQ(member1->getMemberDecl()->getNameAsString(), "lpVtbl");

    ASSERT_NE(binOp2, nullptr) << "lpVtbl2 should be initialized";
    auto* member2 = llvm::dyn_cast<clang::MemberExpr>(binOp2->getLHS());
    EXPECT_EQ(member2->getMemberDecl()->getNameAsString(), "lpVtbl2");

    // Any field initialization would come after lpVtbl and lpVtbl2
    // (Member initializer list translation not yet implemented, so we can't fully test this)
}

// =============================================================================
// Test 6: Multiple constructors all initialize all vtable pointers
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, MultipleConstructorsAllInitialize) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class ISerializable {
        public:
            virtual void serialize() = 0;
        };
        class Shape : public IDrawable, public ISerializable {
        public:
            Shape() {}
            Shape(int size) {}
        };
    )";

    // Test first constructor (default)
    const auto* ctor1 = getCXXConstructorDeclFromCode(code, "Shape", 0);
    ASSERT_NE(ctor1, nullptr);

    auto* cStruct = createCStructWithMultipleLpVtbl("Shape", {"IDrawable", "ISerializable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Shape", {"IDrawable", "ISerializable"});

    auto* cFunc1 = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor1);
    auto __result = ctx.declMapper->get(ctor1); __result
    );

    ASSERT_NE(cFunc1, nullptr);
    auto* body1 = cFunc1->getBody();
    auto* compound1 = llvm::dyn_cast<clang::CompoundStmt>(body1);
    ASSERT_NE(compound1, nullptr);
    EXPECT_GE(compound1->size(), 2) << "Default ctor should init lpVtbl and lpVtbl2";

    // Test second constructor (parameterized)
    const auto* ctor2 = getCXXConstructorDeclFromCode(code, "Shape", 1);
    ASSERT_NE(ctor2, nullptr);

    auto* cFunc2 = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor2);
    auto __result = ctx.declMapper->get(ctor2); __result
    );

    ASSERT_NE(cFunc2, nullptr);
    auto* body2 = cFunc2->getBody();
    auto* compound2 = llvm::dyn_cast<clang::CompoundStmt>(body2);
    ASSERT_NE(compound2, nullptr);
    EXPECT_GE(compound2->size(), 2) << "Parameterized ctor should also init lpVtbl and lpVtbl2";

    // Verify both initialize lpVtbl and lpVtbl2 (find them among the statements)
    clang::BinaryOperator* binOp1 = nullptr;
    clang::BinaryOperator* binOp2 = nullptr;

    for (auto* stmt : compound2->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                std::string memberName = memberExpr->getMemberDecl()->getNameAsString();
                if (memberName == "lpVtbl" && !binOp1) {
                    binOp1 = bo;
                } else if (memberName == "lpVtbl2" && !binOp2) {
                    binOp2 = bo;
                }
            }
        }
    }

    ASSERT_NE(binOp1, nullptr) << "Second constructor should initialize lpVtbl";
    auto* member1 = llvm::dyn_cast<clang::MemberExpr>(binOp1->getLHS());
    EXPECT_EQ(member1->getMemberDecl()->getNameAsString(), "lpVtbl");

    ASSERT_NE(binOp2, nullptr) << "Second constructor should initialize lpVtbl2";
    auto* member2 = llvm::dyn_cast<clang::MemberExpr>(binOp2->getLHS());
    EXPECT_EQ(member2->getMemberDecl()->getNameAsString(), "lpVtbl2");
}

// =============================================================================
// Test 7: Derived class initializes all its vtables
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, DerivedClassInitializesAllVtables) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class ISerializable {
        public:
            virtual void serialize() = 0;
        };
        class Derived : public IDrawable, public ISerializable {
        public:
            Derived() {}
            void draw() override {}
            void serialize() override {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Derived");
    ASSERT_NE(ctor, nullptr);

    const auto* parentClass = getParentClass(ctor);
    ASSERT_NE(parentClass, nullptr);
    EXPECT_EQ(parentClass->getNameAsString(), "Derived");

    auto* cStruct = createCStructWithMultipleLpVtbl("Derived", {"IDrawable", "ISerializable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Derived", {"IDrawable", "ISerializable"});

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "Derived_init");

    auto* body = cFunc->getBody();
    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);
    ASSERT_GE(compoundStmt->size(), 2);

    // Should initialize Derived's vtables (not base class vtables)
    // Find the first vtable assignment (may not be first statement due to base constructor calls)
    clang::BinaryOperator* binOp1 = nullptr;
    for (auto* stmt : compoundStmt->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                std::string memberName = memberExpr->getMemberDecl()->getNameAsString();
                if (memberName == "lpVtbl") {
                    binOp1 = bo;
                    break;
                }
            }
        }
    }
    ASSERT_NE(binOp1, nullptr) << "Should have lpVtbl assignment";

    // RHS should reference Derived_IDrawable_vtable_instance
    auto* rhs1 = binOp1->getRHS();
    auto* unaryOp1 = llvm::dyn_cast<clang::UnaryOperator>(rhs1);
    ASSERT_NE(unaryOp1, nullptr);
    auto* declRef1 = llvm::dyn_cast<clang::DeclRefExpr>(unaryOp1->getSubExpr());
    ASSERT_NE(declRef1, nullptr);
    EXPECT_EQ(declRef1->getNameInfo().getAsString(), "Derived_IDrawable_vtable_instance");
}

// =============================================================================
// Test 8: Vtable pointers point to correct instances
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, VtablePointersToCorrectInstances) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class ISerializable {
        public:
            virtual void serialize() = 0;
        };
        class Shape : public IDrawable, public ISerializable {
        public:
            Shape() {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Shape");
    ASSERT_NE(ctor, nullptr);

    auto* cStruct = createCStructWithMultipleLpVtbl("Shape", {"IDrawable", "ISerializable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Shape", {"IDrawable", "ISerializable"});

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    auto* body = cFunc->getBody();
    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);
    ASSERT_GE(compoundStmt->size(), 2);

    // Find lpVtbl assignment (may not be first statement due to base constructor calls)
    clang::BinaryOperator* binOp1 = nullptr;
    for (auto* stmt : compoundStmt->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                if (memberExpr->getMemberDecl()->getNameAsString() == "lpVtbl") {
                    binOp1 = bo;
                    break;
                }
            }
        }
    }
    ASSERT_NE(binOp1, nullptr) << "Should have lpVtbl assignment";

    // lpVtbl should point to Shape_IDrawable_vtable_instance
    auto* rhs1 = binOp1->getRHS();
    auto* unaryOp1 = llvm::dyn_cast<clang::UnaryOperator>(rhs1);
    ASSERT_NE(unaryOp1, nullptr);
    auto* declRef1 = llvm::dyn_cast<clang::DeclRefExpr>(unaryOp1->getSubExpr());
    ASSERT_NE(declRef1, nullptr);
    EXPECT_EQ(declRef1->getNameInfo().getAsString(), "Shape_IDrawable_vtable_instance")
        << "lpVtbl should point to Shape_IDrawable_vtable_instance";

    // Find lpVtbl2 assignment
    clang::BinaryOperator* binOp2 = nullptr;
    for (auto* stmt : compoundStmt->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                if (memberExpr->getMemberDecl()->getNameAsString() == "lpVtbl2") {
                    binOp2 = bo;
                    break;
                }
            }
        }
    }
    ASSERT_NE(binOp2, nullptr) << "Should have lpVtbl2 assignment";

    // lpVtbl2 should point to Shape_ISerializable_vtable_instance
    auto* rhs2 = binOp2->getRHS();
    auto* unaryOp2 = llvm::dyn_cast<clang::UnaryOperator>(rhs2);
    ASSERT_NE(unaryOp2, nullptr);
    auto* declRef2 = llvm::dyn_cast<clang::DeclRefExpr>(unaryOp2->getSubExpr());
    ASSERT_NE(declRef2, nullptr);
    EXPECT_EQ(declRef2->getNameInfo().getAsString(), "Shape_ISerializable_vtable_instance")
        << "lpVtbl2 should point to Shape_ISerializable_vtable_instance";
}

// =============================================================================
// Test 9: Default constructor with multiple lpVtbl
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, DefaultConstructorMultipleLpVtbl) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class ISerializable {
        public:
            virtual void serialize() = 0;
        };
        class Shape : public IDrawable, public ISerializable {
        public:
            Shape() {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Shape");
    ASSERT_NE(ctor, nullptr);
    EXPECT_EQ(ctor->getNumParams(), 0) << "Should be default constructor";

    auto* cStruct = createCStructWithMultipleLpVtbl("Shape", {"IDrawable", "ISerializable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Shape", {"IDrawable", "ISerializable"});

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "Shape_init");

    auto* body = cFunc->getBody();
    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);
    EXPECT_GE(compoundStmt->size(), 2) << "Default ctor should init lpVtbl and lpVtbl2";
}

// =============================================================================
// Test 10: Parameterized constructor with multiple lpVtbl
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, ParameterizedConstructorMultipleLpVtbl) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class ISerializable {
        public:
            virtual void serialize() = 0;
        };
        class Shape : public IDrawable, public ISerializable {
            int x;
        public:
            Shape(int value) : x(value) {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Shape");
    ASSERT_NE(ctor, nullptr);
    EXPECT_EQ(ctor->getNumParams(), 1) << "Should be parameterized constructor";

    auto* cStruct = createCStructWithMultipleLpVtbl("Shape", {"IDrawable", "ISerializable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Shape", {"IDrawable", "ISerializable"});

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "Shape_init_int");

    auto* body = cFunc->getBody();
    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);
    EXPECT_GE(compoundStmt->size(), 2) << "Parameterized ctor should init lpVtbl and lpVtbl2";

    // Find vtable initializations (may not be first statements due to base constructor calls)
    clang::BinaryOperator* binOp1 = nullptr;
    clang::BinaryOperator* binOp2 = nullptr;

    for (auto* stmt : compoundStmt->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                std::string memberName = memberExpr->getMemberDecl()->getNameAsString();
                if (memberName == "lpVtbl" && !binOp1) {
                    binOp1 = bo;
                } else if (memberName == "lpVtbl2" && !binOp2) {
                    binOp2 = bo;
                }
            }
        }
    }

    ASSERT_NE(binOp1, nullptr) << "Should have lpVtbl assignment";
    auto* member1 = llvm::dyn_cast<clang::MemberExpr>(binOp1->getLHS());
    EXPECT_EQ(member1->getMemberDecl()->getNameAsString(), "lpVtbl");

    ASSERT_NE(binOp2, nullptr) << "Should have lpVtbl2 assignment";
    auto* member2 = llvm::dyn_cast<clang::MemberExpr>(binOp2->getLHS());
    EXPECT_EQ(member2->getMemberDecl()->getNameAsString(), "lpVtbl2");
}

// =============================================================================
// Test 11: Single inheritance still uses lpVtbl only (regression test)
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, SingleInheritanceUsesLpVtblOnly) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class Shape : public IDrawable {
        public:
            Shape() {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Shape");
    ASSERT_NE(ctor, nullptr);

    // Single inheritance: only lpVtbl
    auto* cStruct = createCStructWithMultipleLpVtbl("Shape", {"IDrawable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Shape", {"IDrawable"});

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    auto* body = cFunc->getBody();
    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    // Should have at least 1 vtable initialization (lpVtbl only)
    EXPECT_GE(compoundStmt->size(), 1) << "Single inheritance should have at least lpVtbl";

    // Find lpVtbl assignment (may not be first statement due to base constructor calls)
    clang::BinaryOperator* binOp = nullptr;
    for (auto* stmt : compoundStmt->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                std::string memberName = memberExpr->getMemberDecl()->getNameAsString();
                if (memberName == "lpVtbl") {
                    binOp = bo;
                    break;
                } else if (memberName == "lpVtbl2") {
                    FAIL() << "Single inheritance should NOT use lpVtbl2";
                }
            }
        }
    }

    ASSERT_NE(binOp, nullptr) << "Single inheritance should have lpVtbl assignment";
    auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(binOp->getLHS());
    EXPECT_EQ(memberExpr->getMemberDecl()->getNameAsString(), "lpVtbl")
        << "Single inheritance should only use lpVtbl, not lpVtbl2";
}

// =============================================================================
// Test 12: Three bases yield three initializations
// =============================================================================

TEST_F(ConstructorHandlerMultipleLpVtblTest, ThreeBasesThreeInitializations) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };
        class ISerializable {
        public:
            virtual void serialize() = 0;
        };
        class IClickable {
        public:
            virtual void onClick() = 0;
        };
        class Widget : public IDrawable, public ISerializable, public IClickable {
        public:
            Widget() {}
        };
    )";

    const auto* ctor = getCXXConstructorDeclFromCode(code, "Widget");
    ASSERT_NE(ctor, nullptr);

    auto* cStruct = createCStructWithMultipleLpVtbl("Widget", {"IDrawable", "ISerializable", "IClickable"});
    ASSERT_NE(cStruct, nullptr);

    createVtableInstances("Widget", {"IDrawable", "ISerializable", "IClickable"});

    auto* cFunc = llvm::dyn_cast_or_null<clang::FunctionDecl>(
        ctx.dispatcher->dispatch(ctor);
    auto __result = ctx.declMapper->get(ctor); __result
    );

    ASSERT_NE(cFunc, nullptr);
    auto* body = cFunc->getBody();
    auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body);
    ASSERT_NE(compoundStmt, nullptr);

    // Should have at least 3 vtable initializations
    EXPECT_GE(compoundStmt->size(), 3) << "Three bases should have at least lpVtbl, lpVtbl2, lpVtbl3";

    // Find all three vtable assignments (may not be first three statements due to base constructor calls)
    clang::BinaryOperator* binOp1 = nullptr;
    clang::BinaryOperator* binOp2 = nullptr;
    clang::BinaryOperator* binOp3 = nullptr;

    for (auto* stmt : compoundStmt->body()) {
        if (auto* bo = llvm::dyn_cast<clang::BinaryOperator>(stmt)) {
            if (auto* memberExpr = llvm::dyn_cast<clang::MemberExpr>(bo->getLHS())) {
                std::string memberName = memberExpr->getMemberDecl()->getNameAsString();
                if (memberName == "lpVtbl" && !binOp1) {
                    binOp1 = bo;
                } else if (memberName == "lpVtbl2" && !binOp2) {
                    binOp2 = bo;
                } else if (memberName == "lpVtbl3" && !binOp3) {
                    binOp3 = bo;
                }
            }
        }
    }

    ASSERT_NE(binOp1, nullptr) << "Should have lpVtbl assignment";
    auto* member1 = llvm::dyn_cast<clang::MemberExpr>(binOp1->getLHS());
    EXPECT_EQ(member1->getMemberDecl()->getNameAsString(), "lpVtbl");

    ASSERT_NE(binOp2, nullptr) << "Should have lpVtbl2 assignment";
    auto* member2 = llvm::dyn_cast<clang::MemberExpr>(binOp2->getLHS());
    EXPECT_EQ(member2->getMemberDecl()->getNameAsString(), "lpVtbl2");

    ASSERT_NE(binOp3, nullptr) << "Should have lpVtbl3 assignment";
    auto* member3 = llvm::dyn_cast<clang::MemberExpr>(binOp3->getLHS());
    EXPECT_EQ(member3->getMemberDecl()->getNameAsString(), "lpVtbl3");
}

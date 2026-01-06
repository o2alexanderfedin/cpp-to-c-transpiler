/**
 * @file RecordHandlerDispatcherTest.cpp
 * @brief Unit tests for RecordHandler with dispatcher integration
 *
 * Verifies:
 * - Handler registration
 * - Basic struct translation
 * - Class to struct translation
 * - Field translation via TypeHandler
 * - Nested struct handling (Outer_Inner pattern)
 * - Forward declarations vs complete definitions
 * - Integration with DeclMapper and TypeMapper
 */

#include "dispatch/RecordHandler.h"
#include "dispatch/TypeHandler.h"
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

std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

template<typename T>
T* findDecl(TranslationUnitDecl* TU, const std::string& name) {
    for (auto* D : TU->decls()) {
        if (auto* ND = dyn_cast<NamedDecl>(D)) {
            if (ND->getNameAsString() == name) {
                if (auto* Result = dyn_cast<T>(ND)) {
                    return Result;
                }
            }
        }
        // Check nested classes within namespaces or classes
        if (auto* DC = dyn_cast<DeclContext>(D)) {
            for (auto* Inner : DC->decls()) {
                if (auto* ND = dyn_cast<NamedDecl>(Inner)) {
                    if (ND->getNameAsString() == name) {
                        if (auto* Result = dyn_cast<T>(ND)) {
                            return Result;
                        }
                    }
                }
            }
        }
    }
    return nullptr;
}

// ============================================================================
// Test: RecordHandler Registration
// ============================================================================

TEST(RecordHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    RecordDecl* cppStruct = findDecl<RecordDecl>(TU, "Point");
    ASSERT_NE(cppStruct, nullptr);

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppStruct);
    EXPECT_TRUE(handled);

    Decl* cDecl = declMapper.getCreated(cppStruct);
    EXPECT_NE(cDecl, nullptr);
    EXPECT_TRUE(isa<RecordDecl>(cDecl));
}

// ============================================================================
// Test: Basic Struct Translation
// ============================================================================

TEST(RecordHandlerDispatcherTest, BasicStruct) {
    const char *cpp = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    RecordDecl* cppStruct = findDecl<RecordDecl>(TU, "Point");
    ASSERT_NE(cppStruct, nullptr);
    ASSERT_TRUE(cppStruct->isCompleteDefinition());

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppStruct);
    ASSERT_TRUE(handled);

    Decl* cDecl = declMapper.getCreated(cppStruct);
    ASSERT_NE(cDecl, nullptr);

    auto* cStruct = dyn_cast<RecordDecl>(cDecl);
    ASSERT_NE(cStruct, nullptr);
    EXPECT_EQ(cStruct->getNameAsString(), "Point");
    EXPECT_TRUE(cStruct->isStruct());
    EXPECT_TRUE(cStruct->isCompleteDefinition());

    // Verify fields
    int fieldCount = 0;
    for (auto* field : cStruct->fields()) {
        fieldCount++;
        EXPECT_TRUE(field->getType()->isIntegerType());
    }
    EXPECT_EQ(fieldCount, 2);
}

// ============================================================================
// Test: Class to Struct Translation (normalize TagTypeKind)
// ============================================================================

TEST(RecordHandlerDispatcherTest, ClassToStruct) {
    const char *cpp = R"(
        class Rectangle {
        public:
            int width;
            int height;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXRecordDecl* cppClass = findDecl<CXXRecordDecl>(TU, "Rectangle");
    ASSERT_NE(cppClass, nullptr);
    EXPECT_TRUE(cppClass->isClass());

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppClass);
    ASSERT_TRUE(handled);

    Decl* cDecl = declMapper.getCreated(cppClass);
    ASSERT_NE(cDecl, nullptr);

    auto* cStruct = dyn_cast<RecordDecl>(cDecl);
    ASSERT_NE(cStruct, nullptr);
    EXPECT_EQ(cStruct->getNameAsString(), "Rectangle");
    // Verify it's a struct, not a class
    EXPECT_TRUE(cStruct->isStruct());
    EXPECT_FALSE(cStruct->isClass());
}

// ============================================================================
// Test: Forward Declaration vs Complete Definition
// ============================================================================

TEST(RecordHandlerDispatcherTest, ForwardDeclaration) {
    const char *cpp = R"(
        struct Node;  // Forward declaration

        struct Node {
            int data;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);

    // Find the complete definition (not forward decl)
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    RecordDecl* completeDecl = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* RD = dyn_cast<RecordDecl>(D)) {
            if (RD->getNameAsString() == "Node" && RD->isCompleteDefinition()) {
                completeDecl = RD;
                break;
            }
        }
    }
    ASSERT_NE(completeDecl, nullptr);

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, completeDecl);
    ASSERT_TRUE(handled);

    Decl* cDecl = declMapper.getCreated(completeDecl);
    ASSERT_NE(cDecl, nullptr);

    auto* cStruct = dyn_cast<RecordDecl>(cDecl);
    ASSERT_NE(cStruct, nullptr);
    EXPECT_TRUE(cStruct->isCompleteDefinition());
}

// ============================================================================
// Test: Struct with Different Field Types
// ============================================================================

TEST(RecordHandlerDispatcherTest, FieldTypes) {
    const char *cpp = R"(
        struct Mixed {
            int i;
            float f;
            char c;
            double d;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    RecordDecl* cppStruct = findDecl<RecordDecl>(TU, "Mixed");
    ASSERT_NE(cppStruct, nullptr);

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppStruct);
    ASSERT_TRUE(handled);

    Decl* cDecl = declMapper.getCreated(cppStruct);
    ASSERT_NE(cDecl, nullptr);

    auto* cStruct = dyn_cast<RecordDecl>(cDecl);
    ASSERT_NE(cStruct, nullptr);

    // Verify all fields were translated
    int fieldCount = 0;
    for (auto* field : cStruct->fields()) {
        fieldCount++;
        EXPECT_NE(field->getType().getAsString().find_first_not_of(" "), std::string::npos);
    }
    EXPECT_EQ(fieldCount, 4);
}

// ============================================================================
// Test: Nested Struct (Outer_Inner name mangling)
// ============================================================================

TEST(RecordHandlerDispatcherTest, NestedStruct) {
    const char *cpp = R"(
        struct Outer {
            struct Inner {
                int value;
            };
            Inner nested;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    RecordDecl* cppOuter = findDecl<RecordDecl>(TU, "Outer");
    ASSERT_NE(cppOuter, nullptr);

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppOuter);
    ASSERT_TRUE(handled);

    Decl* cDecl = declMapper.getCreated(cppOuter);
    ASSERT_NE(cDecl, nullptr);

    auto* cOuter = dyn_cast<RecordDecl>(cDecl);
    ASSERT_NE(cOuter, nullptr);
    EXPECT_EQ(cOuter->getNameAsString(), "Outer");

    // Find the nested struct in C++ AST
    RecordDecl* cppInner = nullptr;
    for (auto* D : cppOuter->decls()) {
        if (auto* RD = dyn_cast<RecordDecl>(D)) {
            if (RD->getNameAsString() == "Inner") {
                cppInner = RD;
                break;
            }
        }
    }
    ASSERT_NE(cppInner, nullptr);

    // Verify nested struct was translated
    Decl* cInnerDecl = declMapper.getCreated(cppInner);
    ASSERT_NE(cInnerDecl, nullptr);

    auto* cInner = dyn_cast<RecordDecl>(cInnerDecl);
    ASSERT_NE(cInner, nullptr);

    // Verify nested struct has mangled name (Outer__Inner pattern with double underscore)
    EXPECT_EQ(cInner->getNameAsString(), "Outer__Inner")
        << "Nested struct should have mangled name Outer__Inner";
}

// ============================================================================
// Test: Skip Polymorphic Classes (with virtual functions)
// ============================================================================

TEST(RecordHandlerDispatcherTest, SkipPolymorphicClass) {
    const char *cpp = R"(
        class Base {
        public:
            virtual void foo() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXRecordDecl* cppClass = findDecl<CXXRecordDecl>(TU, "Base");
    ASSERT_NE(cppClass, nullptr);
    ASSERT_TRUE(cppClass->isPolymorphic());

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppClass);
    // Handler should process it but skip translation (log warning)
    EXPECT_TRUE(handled);

    // Should NOT create a C struct for polymorphic class
    Decl* cDecl = declMapper.getCreated(cppClass);
    EXPECT_EQ(cDecl, nullptr) << "Polymorphic classes should not be translated to structs";
}

// ============================================================================
// Test: Duplicate Detection (via declMapper.hasCreated)
// ============================================================================

TEST(RecordHandlerDispatcherTest, DuplicateDetection) {
    const char *cpp = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    RecordDecl* cppStruct = findDecl<RecordDecl>(TU, "Point");
    ASSERT_NE(cppStruct, nullptr);

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    // First dispatch
    bool handled1 = dispatcher.dispatch(cppCtx, cCtx, cppStruct);
    ASSERT_TRUE(handled1);

    Decl* cDecl1 = declMapper.getCreated(cppStruct);
    ASSERT_NE(cDecl1, nullptr);

    // Second dispatch should detect duplicate and return same decl
    bool handled2 = dispatcher.dispatch(cppCtx, cCtx, cppStruct);
    EXPECT_TRUE(handled2);

    Decl* cDecl2 = declMapper.getCreated(cppStruct);
    EXPECT_EQ(cDecl1, cDecl2) << "Should return same C decl for duplicate dispatch";
}

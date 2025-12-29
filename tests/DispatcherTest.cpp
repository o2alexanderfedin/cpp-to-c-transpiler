// Tests for CppToCVisitorDispatcher
// Demonstrates Chain of Responsibility pattern for AST node handling

#include "CppToCVisitorDispatcher.h"
#include "PathMapper.h"
#include "TargetContext.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <iostream>

using namespace clang;

// Helper to build AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

// ============================================================================
// Test: TranslationUnitDecl Handler
// ============================================================================

TEST(DispatcherTest, TranslationUnitHandler) {
    const char *cpp = R"(
        class Point {
            int x, y;
        public:
            int getX() { return x; }
        };

        int globalFunc() { return 42; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr) << "Failed to parse C++ code";

    // Setup components
    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();
    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");

    // Create dispatcher with PathMapper
    CppToCVisitorDispatcher dispatcher(mapper);

    // Track which declarations we process
    std::vector<std::string> processedDecls;

    // Register TranslationUnitDecl handler
    dispatcher.addHandler(
        // Predicate: Match TranslationUnitDecl
        [](const clang::Decl* D) -> bool {
            return llvm::isa<clang::TranslationUnitDecl>(D);
        },

        // Visitor: Process TranslationUnit and recursively dispatch child decls
        [&processedDecls](const CppToCVisitorDispatcher& disp,
                          const clang::ASTContext& cppASTContext,
                          clang::ASTContext& cASTContext,
                          const clang::Decl* D) {
            auto* TU = llvm::cast<clang::TranslationUnitDecl>(D);

            processedDecls.push_back("TranslationUnit");

            // Recursively dispatch all top-level declarations
            for (auto* TopLevelDecl : TU->decls()) {
                // For this test, just record what we see
                if (auto* ClassDecl = llvm::dyn_cast<clang::CXXRecordDecl>(TopLevelDecl)) {
                    if (ClassDecl->isThisDeclarationADefinition()) {
                        processedDecls.push_back("Class: " + ClassDecl->getNameAsString());
                    }
                } else if (auto* FuncDecl = llvm::dyn_cast<clang::FunctionDecl>(TopLevelDecl)) {
                    processedDecls.push_back("Function: " + FuncDecl->getNameAsString());
                }

                // Could recursively dispatch here:
                // disp.dispatch(cppASTContext, cASTContext, TopLevelDecl);
            }
        }
    );

    // Dispatch the TranslationUnit
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    bool handled = dispatcher.dispatch(cppCtx, cCtx, TU);

    // Verify handler was invoked
    EXPECT_TRUE(handled) << "TranslationUnit should be handled";

    // Verify we processed the expected declarations
    ASSERT_GE(processedDecls.size(), 3) << "Should process TU + class + function";
    EXPECT_EQ(processedDecls[0], "TranslationUnit");
    EXPECT_EQ(processedDecls[1], "Class: Point");
    EXPECT_EQ(processedDecls[2], "Function: globalFunc");
}

// ============================================================================
// Test: Handler Chain (Multiple Handlers)
// ============================================================================

TEST(DispatcherTest, HandlerChainOrder) {
    const char *cpp = R"(
        class TestClass {};
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();
    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");

    CppToCVisitorDispatcher dispatcher(mapper);

    std::vector<std::string> invocations;

    // Register first handler (catches all Decls)
    dispatcher.addHandler(
        [](const clang::Decl* D) { return true; },  // Match all
        [&invocations](const CppToCVisitorDispatcher&, const clang::ASTContext&,
                       clang::ASTContext&, const clang::Decl*) {
            invocations.push_back("FirstHandler");
        }
    );

    // Register second handler (never invoked - first handler matches)
    dispatcher.addHandler(
        [](const clang::Decl* D) { return true; },
        [&invocations](const CppToCVisitorDispatcher&, const clang::ASTContext&,
                       clang::ASTContext&, const clang::Decl*) {
            invocations.push_back("SecondHandler");
        }
    );

    // Dispatch any declaration
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    dispatcher.dispatch(cppCtx, cCtx, TU);

    // Verify only first handler was invoked (chain stops after first match)
    ASSERT_EQ(invocations.size(), 1);
    EXPECT_EQ(invocations[0], "FirstHandler");
}

// ============================================================================
// Test: No Handler Match
// ============================================================================

TEST(DispatcherTest, NoHandlerMatch) {
    const char *cpp = "class Test {};";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();
    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");

    CppToCVisitorDispatcher dispatcher(mapper);

    // No handlers registered
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    bool handled = dispatcher.dispatch(cppCtx, cCtx, TU);

    // Should return false when no handler matches
    EXPECT_FALSE(handled);
}

// ============================================================================
// Test: PathMapper Access
// ============================================================================

TEST(DispatcherTest, PathMapperAccess) {
    const char *cpp = "int x;";
    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();
    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");

    CppToCVisitorDispatcher dispatcher(mapper);

    bool mapperAccessed = false;

    // Handler that accesses PathMapper
    dispatcher.addHandler(
        [](const clang::Decl* D) { return llvm::isa<clang::TranslationUnitDecl>(D); },
        [&mapperAccessed](const CppToCVisitorDispatcher& disp,
                          const clang::ASTContext&, clang::ASTContext&,
                          const clang::Decl*) {
            cpptoc::PathMapper& pm = disp.getPathMapper();
            std::string target = pm.mapSourceToTarget("/src/test.cpp");
            EXPECT_EQ(target, "/output/test.c");
            mapperAccessed = true;
        }
    );

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    dispatcher.dispatch(cppCtx, cCtx, TU);

    EXPECT_TRUE(mapperAccessed) << "Handler should access PathMapper";
}

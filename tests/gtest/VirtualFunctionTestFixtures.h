// tests/gtest/VirtualFunctionTestFixtures.h
// Shared test fixtures for virtual function and RTTI tests
// Provides common utilities for building AST and finding declarations

#ifndef VIRTUAL_FUNCTION_TEST_FIXTURES_H
#define VIRTUAL_FUNCTION_TEST_FIXTURES_H

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "../../include/VirtualMethodAnalyzer.h"
#include "../../include/VtableGenerator.h"
#include "../../include/VptrInjector.h"
#include "../../include/OverrideResolver.h"
#include "../../include/VtableInitializer.h"
#include "../../include/VirtualCallTranslator.h"
#include "../../include/PureVirtualHandler.h"
#include "../../include/VirtualDestructorHandler.h"
#include "../../include/TypeidTranslator.h"
#include "../../include/DynamicCastTranslator.h"
#include "../../include/TypeInfoGenerator.h"
#include <memory>
#include <vector>
#include <string>

using namespace clang;

// Base fixture for virtual function tests
class VirtualFunctionTestBase : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> AST;

    // Build AST from C++ code
    std::unique_ptr<ASTUnit> buildAST(const char* code) {
        std::vector<std::string> args = {"-std=c++17"};
        return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
    }

    // Helper to find class by name
    CXXRecordDecl* findClass(ASTContext& Context, const std::string& name) {
        for (auto* D : Context.getTranslationUnitDecl()->decls()) {
            if (auto* RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == name && RD->isCompleteDefinition()) {
                    return RD;
                }
            }
        }
        return nullptr;
    }

    // Find all classes matching a predicate
    template<typename Pred>
    std::vector<CXXRecordDecl*> findClasses(ASTContext& Context, Pred predicate) {
        std::vector<CXXRecordDecl*> results;
        for (auto* D : Context.getTranslationUnitDecl()->decls()) {
            if (auto* RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->isCompleteDefinition() && predicate(RD)) {
                    results.push_back(RD);
                }
            }
        }
        return results;
    }
};

// Fixture for RTTI tests
class RTTITestBase : public VirtualFunctionTestBase {
protected:
    // Helper to find first CXXTypeidExpr in AST
    const CXXTypeidExpr* findTypeidExpr(ASTContext& Context) {
        class TypeidFinder : public RecursiveASTVisitor<TypeidFinder> {
        public:
            const CXXTypeidExpr* Found = nullptr;
            bool VisitCXXTypeidExpr(CXXTypeidExpr* E) {
                if (!Found) Found = E;
                return true;
            }
        };
        TypeidFinder Finder;
        Finder.TraverseDecl(Context.getTranslationUnitDecl());
        return Finder.Found;
    }

    // Helper to find all CXXTypeidExpr in AST
    std::vector<const CXXTypeidExpr*> findAllTypeidExprs(ASTContext& Context) {
        class TypeidFinder : public RecursiveASTVisitor<TypeidFinder> {
        public:
            std::vector<const CXXTypeidExpr*> Found;
            bool VisitCXXTypeidExpr(CXXTypeidExpr* E) {
                Found.push_back(E);
                return true;
            }
        };
        TypeidFinder Finder;
        Finder.TraverseDecl(Context.getTranslationUnitDecl());
        return Finder.Found;
    }

    // Helper to find first CXXDynamicCastExpr in AST
    const CXXDynamicCastExpr* findDynamicCastExpr(ASTContext& Context) {
        class DynamicCastFinder : public RecursiveASTVisitor<DynamicCastFinder> {
        public:
            const CXXDynamicCastExpr* Found = nullptr;
            bool VisitCXXDynamicCastExpr(CXXDynamicCastExpr* E) {
                if (!Found) Found = E;
                return true;
            }
        };
        DynamicCastFinder Finder;
        Finder.TraverseDecl(Context.getTranslationUnitDecl());
        return Finder.Found;
    }

    // Helper to find all CXXDynamicCastExpr in AST
    std::vector<const CXXDynamicCastExpr*> findAllDynamicCastExprs(ASTContext& Context) {
        class DynamicCastFinder : public RecursiveASTVisitor<DynamicCastFinder> {
        public:
            std::vector<const CXXDynamicCastExpr*> Found;
            bool VisitCXXDynamicCastExpr(CXXDynamicCastExpr* E) {
                Found.push_back(E);
                return true;
            }
        };
        DynamicCastFinder Finder;
        Finder.TraverseDecl(Context.getTranslationUnitDecl());
        return Finder.Found;
    }
};

#endif // VIRTUAL_FUNCTION_TEST_FIXTURES_H

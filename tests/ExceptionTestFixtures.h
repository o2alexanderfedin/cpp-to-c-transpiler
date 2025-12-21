//

 ExceptionTestFixtures.h - Common GTest fixtures for exception handling tests
// Migrated from custom test framework to Google Test (GTest)
// Provides shared utilities for exception handling test migration

#ifndef EXCEPTION_TEST_FIXTURES_H
#define EXCEPTION_TEST_FIXTURES_H

#include <gtest/gtest.h>
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include "CppToCVisitor.h"
#include "CNodeBuilder.h"
#include <memory>
#include <string>
#include <vector>

using namespace clang;

// ============================================================================
// Base Test Fixture for Exception Tests
// ============================================================================

class ExceptionTestBase : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }

    void TearDown() override {
        // Common teardown if needed
    }

    // Helper: Parse C++ code and build AST
    std::unique_ptr<ASTUnit> parseCode(const std::string& code) {
        return tooling::buildASTFromCode(code);
    }

    // Helper: Check if string contains substring
    bool contains(const std::string& haystack, const std::string& needle) {
        return haystack.find(needle) != std::string::npos;
    }
};

// ============================================================================
// AST Visitor Helpers
// ============================================================================

// Helper visitor to find try statements in AST
class TryStmtFinder : public RecursiveASTVisitor<TryStmtFinder> {
public:
    CXXTryStmt *foundTryStmt = nullptr;

    bool VisitCXXTryStmt(CXXTryStmt *tryStmt) {
        if (!foundTryStmt) {
            foundTryStmt = tryStmt;
        }
        return true;
    }
};

// Helper: Parse C++ code and find first try statement
inline CXXTryStmt* parseTryStatement(const std::string& code) {
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
    if (!AST) {
        return nullptr;
    }

    TryStmtFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    return finder.foundTryStmt;
}

// Helper: Find function by name in TU
inline FunctionDecl* findFunction(ASTContext &Ctx, const std::string& name) {
    TranslationUnitDecl *TU = Ctx.getTranslationUnitDecl();
    for (Decl *D : TU->decls()) {
        if (FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == name) {
                return FD;
            }
        }
    }
    return nullptr;
}

// Helper: Count return statements in a function
class ReturnStmtCounter : public RecursiveASTVisitor<ReturnStmtCounter> {
public:
    int count = 0;

    bool VisitReturnStmt(ReturnStmt *RS) {
        count++;
        return true;
    }
};

inline int countReturns(FunctionDecl *FD) {
    if (!FD || !FD->hasBody()) return 0;
    ReturnStmtCounter counter;
    counter.TraverseStmt(FD->getBody());
    return counter.count;
}

// Helper: Find all VarDecls with non-trivial destructors
class DestructorVarFinder : public RecursiveASTVisitor<DestructorVarFinder> {
public:
    std::vector<VarDecl*> vars;
    ASTContext &Ctx;

    explicit DestructorVarFinder(ASTContext &Ctx) : Ctx(Ctx) {}

    bool VisitVarDecl(VarDecl *VD) {
        QualType type = VD->getType().getCanonicalType();
        if (const RecordType *RT = type->getAs<RecordType>()) {
            if (CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
                if (RD->hasDefinition() && RD->hasNonTrivialDestructor()) {
                    vars.push_back(VD);
                }
            }
        }
        return true;
    }
};

inline std::vector<VarDecl*> findDestructorVars(ASTContext &Ctx, FunctionDecl *FD) {
    DestructorVarFinder finder(Ctx);
    if (FD && FD->hasBody()) {
        finder.TraverseStmt(FD->getBody());
    }
    return finder.vars;
}

// Helper: Count CompoundStmt nodes (scopes) in a function
class ScopeCounter : public RecursiveASTVisitor<ScopeCounter> {
public:
    int count = 0;

    bool VisitCompoundStmt(CompoundStmt *CS) {
        count++;
        return true;
    }
};

inline int countScopes(FunctionDecl *FD) {
    if (!FD || !FD->hasBody()) return 0;
    ScopeCounter counter;
    counter.TraverseStmt(FD->getBody());
    return counter.count;
}

// ============================================================================
// Fixture for TryCatchTransformer Tests
// ============================================================================

class TryCatchTransformerTest : public ExceptionTestBase {
protected:
    // Add TryCatchTransformer-specific helpers if needed
};

// ============================================================================
// Fixture for Exception Frame Tests
// ============================================================================

class ExceptionFrameTest : public ExceptionTestBase {
protected:
    // Add ExceptionFrame-specific helpers if needed
};

// ============================================================================
// Fixture for Exception Performance Tests
// ============================================================================

class ExceptionPerformanceTest : public ExceptionTestBase {
protected:
    // Helper for timing measurements
    template<typename Func>
    long measureMicroseconds(Func&& func) {
        auto start = std::chrono::high_resolution_clock::now();
        func();
        auto end = std::chrono::high_resolution_clock::now();
        return std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
    }
};

// ============================================================================
// Fixture for Thread Safety Tests
// ============================================================================

class ExceptionThreadSafetyTest : public ExceptionTestBase {
protected:
    // Thread-safe counters and helpers
};

// ============================================================================
// Fixture for Type Matching Tests
// ============================================================================

class CatchHandlerTypeMatchingTest : public ExceptionTestBase {
protected:
    // Type matching specific helpers
};

// ============================================================================
// Fixture for Destructor Tests (RAII)
// ============================================================================

class DestructorTestBase : public ExceptionTestBase {
protected:
    // Common destructor test helpers
};

#endif // EXCEPTION_TEST_FIXTURES_H

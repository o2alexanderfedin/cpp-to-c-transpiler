/**
 * @file MoveSemanticTestFixture.h
 * @brief Shared test fixture for Move Semantics test suite
 *
 * Provides common setup, helper functions, and AST visitors for all
 * move semantics tests migrated to Google Test.
 */

#ifndef MOVE_SEMANTIC_TEST_FIXTURE_H
#define MOVE_SEMANTIC_TEST_FIXTURE_H

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>
#include <vector>

using namespace clang;

/**
 * @brief Helper visitor to find move semantics related AST nodes
 */
class MoveSemanticsFinder : public RecursiveASTVisitor<MoveSemanticsFinder> {
public:
    std::vector<const CXXMethodDecl*> moveConstructors;
    std::vector<const CXXMethodDecl*> moveAssignments;
    std::vector<const CXXConstructExpr*> moveConstructorCalls;
    std::vector<const CallExpr*> stdMoveCalls;
    std::vector<const ValueDecl*> rvalueRefs;
    std::vector<const FunctionDecl*> forwardingFunctions;

    bool VisitCXXConstructorDecl(CXXConstructorDecl *D) {
        if (D->isMoveConstructor()) {
            moveConstructors.push_back(D);
        }
        return true;
    }

    bool VisitCXXMethodDecl(CXXMethodDecl *D) {
        if (D->isMoveAssignmentOperator()) {
            moveAssignments.push_back(D);
        }
        return true;
    }

    bool VisitCXXConstructExpr(CXXConstructExpr *E) {
        if (E->getConstructor()->isMoveConstructor()) {
            moveConstructorCalls.push_back(E);
        }
        return true;
    }

    bool VisitCallExpr(CallExpr *E) {
        if (auto *Callee = E->getDirectCallee()) {
            std::string name = Callee->getNameAsString();
            if (name == "move") {
                stdMoveCalls.push_back(E);
            } else if (name == "forward") {
                forwardingFunctions.push_back(Callee);
            }
        }
        return true;
    }

    bool VisitValueDecl(ValueDecl *D) {
        if (auto *VD = dyn_cast<VarDecl>(D)) {
            if (VD->getType()->isRValueReferenceType()) {
                rvalueRefs.push_back(VD);
            }
        } else if (auto *PD = dyn_cast<ParmVarDecl>(D)) {
            if (PD->getType()->isRValueReferenceType()) {
                rvalueRefs.push_back(PD);
            }
        }
        return true;
    }
};

/**
 * @brief Helper visitor to find function declarations
 */
class FunctionFinder : public RecursiveASTVisitor<FunctionFinder> {
public:
    std::vector<const FunctionDecl*> functions;
    std::vector<const ParmVarDecl*> rvalueRefParams;

    bool VisitFunctionDecl(const FunctionDecl *FD) {
        if (FD->isThisDeclarationADefinition()) {
            functions.push_back(FD);

            // Check for rvalue reference parameters
            for (unsigned i = 0; i < FD->getNumParams(); ++i) {
                const ParmVarDecl *Param = FD->getParamDecl(i);
                if (Param->getType()->isRValueReferenceType()) {
                    rvalueRefParams.push_back(Param);
                }
            }
        }
        return true;
    }
};

/**
 * @brief Helper visitor to find std::move() calls
 */
class StdMoveFinder : public RecursiveASTVisitor<StdMoveFinder> {
public:
    std::vector<const CallExpr*> moveCallExprs;

    bool VisitCallExpr(const CallExpr *Call) {
        if (Call->getDirectCallee()) {
            std::string name = Call->getDirectCallee()->getQualifiedNameAsString();
            if (name == "std::move") {
                moveCallExprs.push_back(Call);
            }
        }
        return true;
    }
};

/**
 * @brief Helper visitor to collect copy and move constructors/assignments
 */
class CopyMoveCollector : public RecursiveASTVisitor<CopyMoveCollector> {
public:
    std::vector<CXXConstructorDecl*> copyConstructors;
    std::vector<CXXConstructorDecl*> moveConstructors;
    std::vector<CXXMethodDecl*> copyAssignments;
    std::vector<CXXMethodDecl*> moveAssignments;

    bool VisitCXXConstructorDecl(CXXConstructorDecl *D) {
        if (!D->isImplicit()) {
            if (D->isCopyConstructor()) {
                copyConstructors.push_back(D);
            } else if (D->isMoveConstructor()) {
                moveConstructors.push_back(D);
            }
        }
        return true;
    }

    bool VisitCXXMethodDecl(CXXMethodDecl *D) {
        if (!D->isImplicit()) {
            if (D->isCopyAssignmentOperator()) {
                copyAssignments.push_back(D);
            } else if (D->isMoveAssignmentOperator()) {
                moveAssignments.push_back(D);
            }
        }
        return true;
    }
};

/**
 * @brief Helper visitor to find call expressions
 */
class CallExprFinder : public RecursiveASTVisitor<CallExprFinder> {
public:
    std::vector<CallExpr*> callExprs;
    std::vector<CXXConstructExpr*> constructExprs;

    bool VisitCallExpr(CallExpr *E) {
        callExprs.push_back(E);
        return true;
    }

    bool VisitCXXConstructExpr(CXXConstructExpr *E) {
        constructExprs.push_back(E);
        return true;
    }
};

/**
 * @brief Helper visitor to find move constructors
 */
class MoveConstructorFinder : public RecursiveASTVisitor<MoveConstructorFinder> {
public:
    std::vector<CXXConstructorDecl*> moveConstructors;

    bool VisitCXXConstructorDecl(CXXConstructorDecl *D) {
        if (D->isMoveConstructor()) {
            moveConstructors.push_back(D);
        }
        return true;
    }
};

/**
 * @brief Helper visitor to find move assignment operators
 */
class MoveAssignmentFinder : public RecursiveASTVisitor<MoveAssignmentFinder> {
public:
    std::vector<CXXMethodDecl*> moveAssignmentOperators;

    bool VisitCXXMethodDecl(CXXMethodDecl *D) {
        if (D->isMoveAssignmentOperator()) {
            moveAssignmentOperators.push_back(D);
        }
        return true;
    }
};

/**
 * @brief Base test fixture for Move Semantics tests
 *
 * Provides common functionality:
 * - Building AST from C++ code
 * - Helper visitors for finding move semantics constructs
 * - Common assertions and utilities
 */
class MoveSemanticTestFixture : public ::testing::Test {
protected:
    /**
     * @brief Build AST from C++ code string
     * @param code C++ source code
     * @return Unique pointer to ASTUnit
     */
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }

    /**
     * @brief Find a method by name in a class
     * @param RD Class record declaration
     * @param methodName Name of the method to find
     * @return Pointer to method or nullptr if not found
     */
    const CXXMethodDecl* findMethodByName(const CXXRecordDecl *RD, const std::string &methodName) {
        if (!RD) return nullptr;

        for (auto *M : RD->methods()) {
            if (M->getNameAsString() == methodName) {
                return M;
            }
        }
        return nullptr;
    }

    /**
     * @brief Find a class by name in translation unit
     * @param TU Translation unit declaration
     * @param className Name of the class to find
     * @return Pointer to class or nullptr if not found
     */
    const CXXRecordDecl* findClassByName(const TranslationUnitDecl *TU, const std::string &className) {
        if (!TU) return nullptr;

        for (auto *D : TU->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == className && RD->isCompleteDefinition()) {
                    return RD;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Find a function by name in translation unit
     * @param TU Translation unit declaration
     * @param functionName Name of the function to find
     * @return Pointer to function or nullptr if not found
     */
    const FunctionDecl* findFunctionByName(const TranslationUnitDecl *TU, const std::string &functionName) {
        if (!TU) return nullptr;

        for (auto *D : TU->decls()) {
            if (auto *FD = dyn_cast<FunctionDecl>(D)) {
                if (FD->getNameAsString() == functionName) {
                    return FD;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Check if a string contains all given substrings
     * @param str String to search
     * @param substrings Vector of substrings to find
     * @return true if all substrings are found
     */
    bool containsAll(const std::string &str, const std::vector<std::string> &substrings) {
        for (const auto &sub : substrings) {
            if (str.find(sub) == std::string::npos) {
                return false;
            }
        }
        return true;
    }

    /**
     * @brief Count occurrences of a substring in a string
     * @param str String to search
     * @param substr Substring to count
     * @return Number of occurrences
     */
    size_t countOccurrences(const std::string &str, const std::string &substr) {
        size_t count = 0;
        size_t pos = 0;
        while ((pos = str.find(substr, pos)) != std::string::npos) {
            count++;
            pos += substr.length();
        }
        return count;
    }
};

#endif // MOVE_SEMANTIC_TEST_FIXTURE_H

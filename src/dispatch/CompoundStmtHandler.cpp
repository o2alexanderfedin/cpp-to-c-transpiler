/**
 * @file CompoundStmtHandler.cpp
 * @brief Implementation of CompoundStmtHandler dispatcher pattern
 */

#include "dispatch/CompoundStmtHandler.h"
#include "dispatch/RecordHandler.h"
#include "mapping/StmtMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/ExprMapper.h"
#include "SourceLocationMapper.h"
#include "NameMangler.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <vector>

namespace cpptoc {

void CompoundStmtHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Cast to StmtPredicate and StmtVisitor to avoid ambiguity
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&CompoundStmtHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&CompoundStmtHandler::handleCompoundStmt)
    );
}

bool CompoundStmtHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");

    // Use exact type matching with getStmtClass
    return S->getStmtClass() == clang::Stmt::CompoundStmtClass;
}

void CompoundStmtHandler::handleCompoundStmt(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(canHandle(S) && "Statement must be CompoundStmt");

    const auto* cppCompound = llvm::cast<clang::CompoundStmt>(S);

    // Get StmtMapper for retrieving and storing statement mappings
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();

    // Check if already processed
    if (stmtMapper.hasCreated(S)) {
        llvm::outs() << "[CompoundStmtHandler] CompoundStmt already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CompoundStmtHandler] Processing CompoundStmt with "
                 << cppCompound->size() << " statements\n";

    // Translate each statement in the compound statement body
    std::vector<clang::Stmt*> cStmts;
    cStmts.reserve(cppCompound->size());

    for (const clang::Stmt* cppStmt : cppCompound->body()) {
        llvm::outs() << "[CompoundStmtHandler] Dispatching statement: "
                     << cppStmt->getStmtClassName() << "\n";

        clang::Stmt* cStmt = nullptr;
        bool handled = false;

        // CRITICAL FIX: Check if it's an expression first
        // In C/C++, expressions can be used as statements (expression statements)
        // Examples: "a = b;", "foo();", "x++;", etc.
        // BinaryOperator, CallExpr, etc. are registered as EXPRESSION handlers
        if (llvm::isa<clang::Expr>(cppStmt)) {
            llvm::outs() << "[CompoundStmtHandler] Statement is an Expr, dispatching as expression\n";

            // Cast to Expr* and dispatch via expression handlers
            const clang::Expr* cppExpr = llvm::cast<clang::Expr>(cppStmt);
            handled = disp.dispatch(
                cppASTContext,
                cASTContext,
                const_cast<clang::Expr*>(cppExpr)
            );

            if (handled) {
                // Get the translated expression from ExprMapper
                clang::Expr* cExpr = disp.getExprMapper().getCreated(cppExpr);
                if (cExpr) {
                    // Use the expression directly as a statement
                    // (in C AST, expressions can be statements)
                    cStmt = cExpr;
                    llvm::outs() << "[CompoundStmtHandler] Expression successfully translated and will be used as statement\n";
                } else {
                    llvm::errs() << "[CompoundStmtHandler] WARNING: Expression dispatched but not in ExprMapper: "
                                 << cppStmt->getStmtClassName() << "\n";
                }
            }
        } else {
            // Not an expression, try statement handlers
            llvm::outs() << "[CompoundStmtHandler] Statement is not an Expr, dispatching as statement\n";
            handled = disp.dispatch(
                cppASTContext,
                cASTContext,
                const_cast<clang::Stmt*>(cppStmt)
            );

            if (handled) {
                // Retrieve translated statement from StmtMapper
                cStmt = stmtMapper.getCreated(cppStmt);
                if (!cStmt) {
                    llvm::errs() << "[CompoundStmtHandler] WARNING: Statement dispatched but not in StmtMapper: "
                                 << cppStmt->getStmtClassName() << "\n";
                }
            }
        }

        if (!handled || !cStmt) {
            llvm::errs() << "[CompoundStmtHandler] WARNING: Statement not handled: "
                         << cppStmt->getStmtClassName() << "\n";
            llvm::errs() << "  Skipping unhandled statement in compound statement\n";
            // Continue with next statement instead of failing
            // This allows partial translation during development
            continue;
        }

        // Add translated statement to collection
        cStmts.push_back(cStmt);
        llvm::outs() << "[CompoundStmtHandler] Statement translated successfully: "
                     << cStmt->getStmtClassName() << "\n";

        // PHASE 56: Check if this is a DeclStmt with variables that need constructor calls
        // For each VarDecl with a CXXConstructExpr initializer, generate a constructor call
        if (const auto* cppDeclStmt = llvm::dyn_cast<clang::DeclStmt>(cppStmt)) {
            llvm::outs() << "[CompoundStmtHandler] DeclStmt detected, checking for constructor calls\n";

            for (auto* cppDecl : cppDeclStmt->decls()) {
                auto* cppVar = llvm::dyn_cast<clang::VarDecl>(cppDecl);
                if (!cppVar) continue;

                // Check if variable has a CXXConstructExpr initializer
                const clang::Expr* initExpr = cppVar->getInit();
                if (!initExpr) continue;

                const auto* ctorExpr = llvm::dyn_cast<clang::CXXConstructExpr>(initExpr);
                if (!ctorExpr) continue;

                const clang::CXXConstructorDecl* cppCtor = ctorExpr->getConstructor();
                if (!cppCtor) continue;

                llvm::outs() << "[CompoundStmtHandler] Variable " << cppVar->getNameAsString()
                             << " has CXXConstructExpr, generating constructor call\n";

                // Get the C variable declaration from DeclMapper
                cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
                clang::Decl* cVarDecl = declMapper.getCreated(cppVar);
                if (!cVarDecl) {
                    llvm::errs() << "[CompoundStmtHandler] ERROR: C variable not found in DeclMapper\n";
                    continue;
                }

                auto* cVar = llvm::dyn_cast<clang::VarDecl>(cVarDecl);
                if (!cVar) {
                    llvm::errs() << "[CompoundStmtHandler] ERROR: C decl is not VarDecl\n";
                    continue;
                }

                // PHASE 57: Check if class has virtual bases - if so, use C1 constructor variant
                const clang::CXXRecordDecl* parentClass = cppCtor->getParent();
                bool needsC1Constructor = false;
                std::string constructorName;

                if (parentClass && RecordHandler::needsDualLayout(parentClass)) {
                    needsC1Constructor = true;
                    constructorName = cpptoc::mangle_constructor(cppCtor) + "_C1";
                    llvm::outs() << "[CompoundStmtHandler] Class " << parentClass->getNameAsString()
                                 << " has virtual bases, using C1 constructor: " << constructorName << "\n";
                } else {
                    // Regular constructor for classes without virtual bases
                    clang::Decl* cCtorDecl = declMapper.getCreated(cppCtor);
                    if (!cCtorDecl) {
                        llvm::errs() << "[CompoundStmtHandler] WARNING: C constructor not found in DeclMapper for "
                                     << cppCtor->getNameAsString() << "\n";
                        continue;
                    }

                    auto* cCtorFunc = llvm::dyn_cast<clang::FunctionDecl>(cCtorDecl);
                    if (!cCtorFunc) {
                        llvm::errs() << "[CompoundStmtHandler] ERROR: C constructor is not FunctionDecl\n";
                        continue;
                    }
                    constructorName = cCtorFunc->getNameAsString();
                }

                llvm::outs() << "[CompoundStmtHandler] Using constructor function: " << constructorName << "\n";

                // Find or create the constructor function declaration by name
                auto* TU = cASTContext.getTranslationUnitDecl();
                clang::FunctionDecl* cCtorFunc = nullptr;
                for (auto* D : TU->decls()) {
                    if (auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
                        if (FD->getNameAsString() == constructorName) {
                            cCtorFunc = FD;
                            break;
                        }
                    }
                }

                if (!cCtorFunc) {
                    llvm::errs() << "[CompoundStmtHandler] ERROR: Constructor function not found: "
                                 << constructorName << "\n";
                    continue;
                }

                // Get source location for generated code
                SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
                std::string targetPath = disp.getCurrentTargetPath();
                if (targetPath.empty()) {
                    targetPath = disp.getTargetPath(cppASTContext, nullptr);
                }
                clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

                // Create DeclRefExpr for the variable
                clang::DeclRefExpr* varRef = clang::DeclRefExpr::Create(
                    cASTContext,
                    clang::NestedNameSpecifierLoc(),
                    targetLoc,
                    cVar,
                    false,
                    targetLoc,
                    cVar->getType(),
                    clang::VK_LValue
                );

                // Create UnaryOperator for address-of (&variable)
                clang::UnaryOperator* addrOf = clang::UnaryOperator::Create(
                    cASTContext,
                    varRef,
                    clang::UO_AddrOf,
                    cASTContext.getPointerType(cVar->getType()),
                    clang::VK_PRValue,
                    clang::OK_Ordinary,
                    targetLoc,
                    false,
                    clang::FPOptionsOverride()
                );

                // Create DeclRefExpr for the constructor function
                clang::DeclRefExpr* ctorFuncRef = clang::DeclRefExpr::Create(
                    cASTContext,
                    clang::NestedNameSpecifierLoc(),
                    targetLoc,
                    cCtorFunc,
                    false,
                    targetLoc,
                    cCtorFunc->getType(),
                    clang::VK_LValue
                );

                // Create CallExpr for constructor call: Constructor__ctor(&var)
                std::vector<clang::Expr*> ctorArgs;
                ctorArgs.push_back(addrOf);

                // C1 constructors need VTT parameter (NULL for now)
                if (needsC1Constructor) {
                    // Create NULL literal for VTT parameter
                    clang::QualType vttType = cASTContext.getPointerType(
                        cASTContext.getPointerType(cASTContext.getConstType(cASTContext.VoidTy))
                    );
                    clang::Expr* nullExpr = clang::CStyleCastExpr::Create(
                        cASTContext,
                        vttType,
                        clang::VK_PRValue,
                        clang::CK_NullToPointer,
                        clang::IntegerLiteral::Create(
                            cASTContext,
                            llvm::APInt(32, 0),
                            cASTContext.IntTy,
                            targetLoc
                        ),
                        nullptr,
                        clang::FPOptionsOverride(),
                        cASTContext.getTrivialTypeSourceInfo(vttType),
                        targetLoc,
                        targetLoc
                    );
                    ctorArgs.push_back(nullExpr);
                    llvm::outs() << "[CompoundStmtHandler] Added VTT parameter (NULL) to C1 constructor call\n";
                }

                // Add any additional constructor arguments from the CXXConstructExpr
                cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
                for (unsigned i = 0; i < ctorExpr->getNumArgs(); ++i) {
                    const clang::Expr* cppArg = ctorExpr->getArg(i);
                    clang::Expr* cArg = exprMapper.getCreated(cppArg);
                    if (cArg) {
                        ctorArgs.push_back(cArg);
                    }
                }

                clang::CallExpr* ctorCall = clang::CallExpr::Create(
                    cASTContext,
                    ctorFuncRef,
                    ctorArgs,
                    cASTContext.VoidTy,
                    clang::VK_PRValue,
                    targetLoc,
                    clang::FPOptionsOverride()
                );

                llvm::outs() << "[CompoundStmtHandler] Created constructor call: "
                             << cCtorFunc->getNameAsString() << "(&" << cVar->getNameAsString() << ")\n";

                // Add constructor call statement after the DeclStmt
                cStmts.push_back(ctorCall);
            }
        }
    }

    llvm::outs() << "[CompoundStmtHandler] Collected " << cStmts.size()
                 << " translated statements (out of " << cppCompound->size() << " original)\n";

    // Get source location for SourceLocation initialization
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile("");

    // Create C CompoundStmt with translated statements
    clang::CompoundStmt* cCompound = clang::CompoundStmt::Create(
        cASTContext,
        cStmts,
        clang::FPOptionsOverride(),
        targetLoc,
        targetLoc
    );

    llvm::outs() << "[CompoundStmtHandler] Created C CompoundStmt with "
                 << cCompound->size() << " statements\n";

    // Store mapping in StmtMapper
    stmtMapper.setCreated(S, cCompound);

    llvm::outs() << "[CompoundStmtHandler] CompoundStmt translation complete and stored in StmtMapper\n";
}

} // namespace cpptoc

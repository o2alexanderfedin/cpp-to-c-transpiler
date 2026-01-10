/**
 * @file DeclStmtHandler.cpp
 * @brief Implementation of DeclStmtHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle declaration statement translation.
 */

#include "dispatch/DeclStmtHandler.h"
#include "mapping/DeclMapper.h"
#include "mapping/StmtMapper.h"
#include "SourceLocationMapper.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void DeclStmtHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&DeclStmtHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&DeclStmtHandler::handleDeclStmt)
    );
}

bool DeclStmtHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");
    return S->getStmtClass() == clang::Stmt::DeclStmtClass;
}

void DeclStmtHandler::handleDeclStmt(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(S->getStmtClass() == clang::Stmt::DeclStmtClass && "Must be DeclStmt");

    const auto* cppDeclStmt = llvm::cast<clang::DeclStmt>(S);

    llvm::outs() << "[DeclStmtHandler] Handling DeclStmt\n";

    // Check if already translated
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
    if (stmtMapper.getCreated(cppDeclStmt)) {
        llvm::outs() << "[DeclStmtHandler] DeclStmt already translated\n";
        return;
    }

    // Dispatch all declarations in the statement
    std::vector<clang::Decl*> cDecls;
    for (auto* cppDecl : cppDeclStmt->decls()) {
        // Dispatch declaration to appropriate handler (usually VariableHandler)
        bool declHandled = disp.dispatch(cppASTContext, cASTContext, cppDecl);

        if (!declHandled) {
            llvm::errs() << "[DeclStmtHandler] WARNING: Declaration not handled: "
                         << cppDecl->getDeclKindName() << "\n";
            // Continue with other declarations
            continue;
        }

        // Retrieve translated declaration from DeclMapper
        cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
        clang::Decl* cDecl = declMapper.getCreated(cppDecl);

        if (cDecl) {
            // CRITICAL: Skip static local variables that were hoisted to global scope
            // They should not appear in the function's DeclStmt
            // How to detect: C++ VarDecl had static storage, C VarDecl is at global scope
            bool isHoistedStatic = false;
            if (auto* cppVar = llvm::dyn_cast<clang::VarDecl>(cppDecl)) {
                if (cppVar->getStorageClass() == clang::SC_Static) {
                    // Check if C decl is at global scope (TranslationUnit)
                    if (auto* cVar = llvm::dyn_cast<clang::VarDecl>(cDecl)) {
                        if (llvm::isa<clang::TranslationUnitDecl>(cVar->getDeclContext())) {
                            isHoistedStatic = true;
                            llvm::outs() << "[DeclStmtHandler] Skipping hoisted static local: "
                                         << cppVar->getNameAsString() << "\n";
                        }
                    }
                }
            }

            if (!isHoistedStatic) {
                cDecls.push_back(cDecl);
                llvm::outs() << "[DeclStmtHandler] Declaration translated: "
                             << cppDecl->getDeclKindName() << "\n";
            }
        } else {
            llvm::errs() << "[DeclStmtHandler] ERROR: Declaration not in DeclMapper after successful dispatch\n";
        }
    }

    // Create C DeclStmt with all translated declarations
    clang::DeclStmt* cDeclStmt = nullptr;

    // Get source location for SourceLocation initialization
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile("");

    if (cDecls.size() == 1) {
        // Single declaration
        cDeclStmt = new (cASTContext) clang::DeclStmt(
            clang::DeclGroupRef(cDecls[0]),
            targetLoc,
            targetLoc
        );
    } else if (cDecls.size() > 1) {
        // Multiple declarations (e.g., "int a, b;")
        clang::DeclGroup* declGroup = clang::DeclGroup::Create(
            cASTContext,
            cDecls.data(),
            cDecls.size()
        );
        cDeclStmt = new (cASTContext) clang::DeclStmt(
            clang::DeclGroupRef(declGroup),
            targetLoc,
            targetLoc
        );
    } else {
        // No declarations translated - create empty DeclStmt
        llvm::errs() << "[DeclStmtHandler] WARNING: No declarations translated in DeclStmt\n";
        // Return without creating a statement - parent handler will skip it
        return;
    }

    assert(cDeclStmt && "Failed to create C DeclStmt");

    // Store in StmtMapper
    stmtMapper.setCreated(cppDeclStmt, cDeclStmt);

    llvm::outs() << "[DeclStmtHandler] Created C DeclStmt with "
                 << cDecls.size() << " declaration(s)\n";
}

} // namespace cpptoc

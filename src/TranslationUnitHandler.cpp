#include "TranslationUnitHandler.h"
#include "llvm/Support/Casting.h"
#include <cassert>

namespace cpptoc {

void TranslationUnitHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &TranslationUnitHandler::canHandle,
        &TranslationUnitHandler::handleTranslationUnit
    );
}

bool TranslationUnitHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Check for EXACT type match (not derived classes)
    // Important: Other handlers should follow this pattern for type safety
    return D->getKind() == clang::Decl::TranslationUnit;
}

void TranslationUnitHandler::handleTranslationUnit(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::TranslationUnit && "Must be TranslationUnitDecl");

    auto* TU = llvm::cast<clang::TranslationUnitDecl>(D);

    // Recursively dispatch all top-level declarations
    for (auto* TopLevelDecl : TU->decls()) {
        // Dispatch to appropriate handler via dispatcher
        disp.dispatch(cppASTContext, cASTContext, TopLevelDecl);
    }
}

} // namespace cpptoc

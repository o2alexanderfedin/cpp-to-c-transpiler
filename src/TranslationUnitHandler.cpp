#include "TranslationUnitHandler.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

void TranslationUnitHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &TranslationUnitHandler::canHandle,
        &TranslationUnitHandler::handleTranslationUnit
    );
}

bool TranslationUnitHandler::canHandle(const clang::Decl* D) {
    return llvm::isa<clang::TranslationUnitDecl>(D);
}

void TranslationUnitHandler::handleTranslationUnit(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    auto* TU = llvm::cast<clang::TranslationUnitDecl>(D);

    // Recursively dispatch all top-level declarations
    for (auto* TopLevelDecl : TU->decls()) {
        // Dispatch to appropriate handler via dispatcher
        disp.dispatch(cppASTContext, cASTContext, TopLevelDecl);
    }
}

} // namespace cpptoc

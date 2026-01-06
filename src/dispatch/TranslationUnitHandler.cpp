#include "dispatch/TranslationUnitHandler.h"
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

    const auto* cppTU = llvm::cast<clang::TranslationUnitDecl>(D);

    // Get C target path from dispatcher (uses AST node's actual location)
    std::string targetPath = disp.getTargetPath(cppASTContext, D);

    // Set current target path so child handlers know which file is being processed
    // CRITICAL: This must be set BEFORE dispatching child declarations
    // RecordHandler, EnumHandler, etc. use getCurrentTargetPath() for file origin filtering
    disp.setCurrentTargetPath(targetPath);

    // Get or create C TranslationUnit for this target file
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);
    assert(cTU && "Failed to create C TranslationUnit");

    // Recursively dispatch all top-level declarations
    // Child handlers will add their C declarations to cTU
    for (auto* TopLevelDecl : cppTU->decls()) {
        disp.dispatch(cppASTContext, cASTContext, TopLevelDecl);
    }
}

} // namespace cpptoc

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

    const auto* cppTU = llvm::cast<clang::TranslationUnitDecl>(D);

    // Get PathMapper from dispatcher to map C++ source → C target
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();

    // Get source file path from C++ TranslationUnit via SourceManager
    const clang::SourceManager& SM = cppASTContext.getSourceManager();
    clang::FileID MainFileID = SM.getMainFileID();
    const clang::FileEntry* MainFile = SM.getFileEntryForID(MainFileID);

    std::string sourcePath;
    if (MainFile) {
        sourcePath = MainFile->tryGetRealPathName().str();
    } else {
        // Fallback for in-memory sources (e.g., tests with buildASTFromCode)
        sourcePath = "<stdin>";
    }

    // Map C++ source path to C target path
    std::string targetPath = pathMapper.mapSourceToTarget(sourcePath);

    // Get or create C TranslationUnit for this target file
    clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);
    assert(cTU && "Failed to create C TranslationUnit");

    // Recursively dispatch all top-level declarations
    // Child handlers will add their C declarations to cTU
    for (auto* TopLevelDecl : cppTU->decls()) {
        // Dispatch to appropriate handler via dispatcher
        disp.dispatch(cppASTContext, cASTContext, TopLevelDecl);
    }
}

} // namespace cpptoc

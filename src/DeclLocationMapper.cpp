#include "DeclLocationMapper.h"
#include "clang/Basic/SourceManager.h"
#include <cassert>

namespace cpptoc {

std::string DeclLocationMapper::getTargetPath(const clang::ASTContext& cppASTContext, const clang::Decl* D) const {
    assert(D && "Declaration must not be null");

    // Get source file path from AST node's location
    const clang::SourceManager& SM = cppASTContext.getSourceManager();
    clang::SourceLocation Loc = D->getLocation();
    clang::FileID FID = SM.getFileID(Loc);
    const clang::FileEntry* File = SM.getFileEntryForID(FID);

    std::string sourcePath;
    if (File) {
        sourcePath = File->tryGetRealPathName().str();
    } else {
        // Fallback for in-memory sources (e.g., tests with buildASTFromCode)
        sourcePath = "<stdin>";
    }

    // Map source path to target path via PathMapper
    return pathMapper_.mapSourceToTarget(sourcePath);
}

} // namespace cpptoc

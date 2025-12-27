/**
 * @file HandlerContext.cpp
 * @brief Implementation of HandlerContext
 */

#include "handlers/HandlerContext.h"

namespace cpptoc {

HandlerContext::HandlerContext(
    clang::ASTContext& cppCtx,
    clang::ASTContext& cCtx,
    clang::CNodeBuilder& builder
)
    : cppContext_(cppCtx)
    , cContext_(cCtx)
    , builder_(builder)
{}

HandlerContext::~HandlerContext() {
    // Clean up maps
    declMap_.clear();
    typeMap_.clear();
}

void HandlerContext::registerDecl(const clang::Decl* cppDecl, clang::Decl* cDecl) {
    if (cppDecl && cDecl) {
        declMap_[cppDecl] = cDecl;
    }
}

clang::Decl* HandlerContext::lookupDecl(const clang::Decl* cppDecl) const {
    auto it = declMap_.find(cppDecl);
    return it != declMap_.end() ? it->second : nullptr;
}

clang::QualType HandlerContext::translateType(clang::QualType cppType) {
    // Check cache first
    auto it = typeMap_.find(cppType);
    if (it != typeMap_.end()) {
        return it->second;
    }

    clang::QualType cType;

    // Handle reference types: T& → T*
    if (cppType->isReferenceType()) {
        clang::QualType pointee = cppType->getPointeeType();
        cType = cContext_.getPointerType(translateType(pointee));
    }
    // Handle record types (classes/structs)
    else if (auto* recordType = cppType->getAs<clang::RecordType>()) {
        // For now, pass through - full class translation will be handled later
        // TODO: Lookup translated struct in declMap
        cType = cppType;
    }
    // Basic types pass through
    else {
        cType = cppType;
    }

    // Cache result
    typeMap_[cppType] = cType;
    return cType;
}

} // namespace cpptoc

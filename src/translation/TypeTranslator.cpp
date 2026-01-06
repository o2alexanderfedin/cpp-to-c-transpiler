/**
 * @file TypeTranslator.cpp
 * @brief Implementation of type translation utilities
 */

#include "translation/TypeTranslator.h"
#include "clang/AST/Type.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

clang::QualType TypeTranslator::translateType(
    clang::QualType cppType,
    clang::ASTContext& cASTContext
) {
    // Check for lvalue reference (T&)
    if (const auto* lvalRefType = llvm::dyn_cast<clang::LValueReferenceType>(cppType.getTypePtr())) {
        // Transform T& → T*
        clang::QualType pointeeType = lvalRefType->getPointeeType();
        return cASTContext.getPointerType(pointeeType);
    }

    // Check for rvalue reference (T&&)
    if (const auto* rvalRefType = llvm::dyn_cast<clang::RValueReferenceType>(cppType.getTypePtr())) {
        // Transform T&& → T*
        // Note: C has no equivalent for move semantics, but we translate to pointer
        clang::QualType pointeeType = rvalRefType->getPointeeType();
        return cASTContext.getPointerType(pointeeType);
    }

    // For non-reference types, pass through unchanged
    // IMPORTANT: Types must be compatible between AST contexts
    // If type mismatch errors occur, need to recreate type in cASTContext
    return cppType;
}

} // namespace cpptoc

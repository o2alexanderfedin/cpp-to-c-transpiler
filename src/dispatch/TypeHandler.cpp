/**
 * @file TypeHandler.cpp
 * @brief Implementation of TypeHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle type translation.
 * Phase 1 implementation: Reference type translation only.
 */

#include "dispatch/TypeHandler.h"
#include "mapping/TypeMapper.h"
#include "clang/AST/Type.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void TypeHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &TypeHandler::canHandle,
        &TypeHandler::handleType
    );
}

bool TypeHandler::canHandle(const clang::Type* T) {
    assert(T && "Type must not be null");

    // Handle reference types: LValueReferenceType (T&) and RValueReferenceType (T&&)
    // Phase 1: Only these types need translation (reference → pointer)
    return llvm::isa<clang::LValueReferenceType>(T) ||
           llvm::isa<clang::RValueReferenceType>(T);
}

void TypeHandler::handleType(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Type* T
) {
    assert(T && "Type must not be null");

    cpptoc::TypeMapper& typeMapper = disp.getTypeMapper();

    // Check if already processed
    if (typeMapper.hasCreatedType(T)) {
        llvm::outs() << "[TypeHandler] Type already translated, skipping: "
                     << clang::QualType(T, 0).getAsString() << "\n";
        return;
    }

    clang::QualType cType;

    // Handle lvalue reference (T&)
    if (const auto* lvalRefType = llvm::dyn_cast<clang::LValueReferenceType>(T)) {
        // Transform T& → T*
        clang::QualType pointeeType = lvalRefType->getPointeeType();
        cType = cASTContext.getPointerType(pointeeType);

        llvm::outs() << "[TypeHandler] Translated lvalue reference: "
                     << clang::QualType(T, 0).getAsString()
                     << " → " << cType.getAsString() << "\n";
    }
    // Handle rvalue reference (T&&)
    else if (const auto* rvalRefType = llvm::dyn_cast<clang::RValueReferenceType>(T)) {
        // Transform T&& → T*
        // Note: C has no equivalent for move semantics, but we translate to pointer
        clang::QualType pointeeType = rvalRefType->getPointeeType();
        cType = cASTContext.getPointerType(pointeeType);

        llvm::outs() << "[TypeHandler] Translated rvalue reference: "
                     << clang::QualType(T, 0).getAsString()
                     << " → " << cType.getAsString() << "\n";
    }
    // Pass through other types unchanged (Phase 1)
    else {
        // For non-reference types, pass through as-is
        // IMPORTANT: Types must be compatible between AST contexts
        // If type mismatch errors occur, need to recreate type in cASTContext
        cType = clang::QualType(T, 0);

        llvm::outs() << "[TypeHandler] Pass-through type (no translation needed): "
                     << cType.getAsString() << "\n";
    }

    // Store type mapping in TypeMapper
    typeMapper.setCreatedType(T, cType);
}

} // namespace cpptoc

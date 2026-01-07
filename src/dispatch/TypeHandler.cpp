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
    if (typeMapper.hasCreated(T)) {
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
    typeMapper.setCreated(T, cType);
}

clang::QualType TypeHandler::translateType(
    clang::QualType cppType,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    // Remove qualifiers for type matching
    clang::QualType unqualifiedCppType = cppType.getUnqualifiedType();
    const clang::Type* cppTypePtr = unqualifiedCppType.getTypePtr();

    // Handle builtin types - map to C ASTContext builtins
    if (const auto* builtinType = llvm::dyn_cast<clang::BuiltinType>(cppTypePtr)) {
        clang::QualType cType;
        switch (builtinType->getKind()) {
            case clang::BuiltinType::Void:
                cType = cASTContext.VoidTy;
                break;
            case clang::BuiltinType::Bool:
                cType = cASTContext.BoolTy;
                break;
            case clang::BuiltinType::Char_S:
            case clang::BuiltinType::Char_U:
                cType = cASTContext.CharTy;
                break;
            case clang::BuiltinType::SChar:
                cType = cASTContext.SignedCharTy;
                break;
            case clang::BuiltinType::UChar:
                cType = cASTContext.UnsignedCharTy;
                break;
            case clang::BuiltinType::Short:
                cType = cASTContext.ShortTy;
                break;
            case clang::BuiltinType::UShort:
                cType = cASTContext.UnsignedShortTy;
                break;
            case clang::BuiltinType::Int:
                cType = cASTContext.IntTy;
                break;
            case clang::BuiltinType::UInt:
                cType = cASTContext.UnsignedIntTy;
                break;
            case clang::BuiltinType::Long:
                cType = cASTContext.LongTy;
                break;
            case clang::BuiltinType::ULong:
                cType = cASTContext.UnsignedLongTy;
                break;
            case clang::BuiltinType::LongLong:
                cType = cASTContext.LongLongTy;
                break;
            case clang::BuiltinType::ULongLong:
                cType = cASTContext.UnsignedLongLongTy;
                break;
            case clang::BuiltinType::Float:
                cType = cASTContext.FloatTy;
                break;
            case clang::BuiltinType::Double:
                cType = cASTContext.DoubleTy;
                break;
            case clang::BuiltinType::LongDouble:
                cType = cASTContext.LongDoubleTy;
                break;
            default:
                // For other builtin types, use the C context's equivalent
                // This is safe because builtin types are canonical
                cType = cASTContext.getCanonicalType(cppType);
                break;
        }
        // Re-apply qualifiers
        return cASTContext.getQualifiedType(cType, cppType.getQualifiers());
    }

    // Handle pointer types - recursively translate pointee
    if (const auto* ptrType = llvm::dyn_cast<clang::PointerType>(cppTypePtr)) {
        clang::QualType cppPointee = ptrType->getPointeeType();
        clang::QualType cPointee = translateType(cppPointee, cppASTContext, cASTContext);
        clang::QualType cType = cASTContext.getPointerType(cPointee);
        // Re-apply qualifiers
        return cASTContext.getQualifiedType(cType, cppType.getQualifiers());
    }

    // Handle reference types - convert to pointers
    if (const auto* refType = llvm::dyn_cast<clang::ReferenceType>(cppTypePtr)) {
        clang::QualType cppPointee = refType->getPointeeType();
        clang::QualType cPointee = translateType(cppPointee, cppASTContext, cASTContext);
        clang::QualType cType = cASTContext.getPointerType(cPointee);
        // Re-apply qualifiers
        return cASTContext.getQualifiedType(cType, cppType.getQualifiers());
    }

    // Handle array types - recursively translate element type
    if (const auto* arrayType = llvm::dyn_cast<clang::ConstantArrayType>(cppTypePtr)) {
        clang::QualType cppElement = arrayType->getElementType();
        clang::QualType cElement = translateType(cppElement, cppASTContext, cASTContext);
        clang::QualType cType = cASTContext.getConstantArrayType(
            cElement,
            arrayType->getSize(),
            arrayType->getSizeExpr(),
            arrayType->getSizeModifier(),
            arrayType->getIndexTypeCVRQualifiers()
        );
        // Re-apply qualifiers
        return cASTContext.getQualifiedType(cType, cppType.getQualifiers());
    }

    // Handle record types (struct/class) - pass through
    // Struct types are canonical and work across contexts
    if (llvm::isa<clang::RecordType>(cppTypePtr)) {
        // Record types need special handling - for now pass through
        // TODO: Look up translated struct in DeclMapper if needed
        return cppType;
    }

    // Handle enum types - pass through
    if (llvm::isa<clang::EnumType>(cppTypePtr)) {
        // Enum types need special handling - for now pass through
        // TODO: Look up translated enum in DeclMapper if needed
        return cppType;
    }

    // Fallback: pass through unchanged with warning
    llvm::outs() << "[TypeHandler::translateType] WARNING: Unhandled type kind, passing through: "
                 << cppType.getAsString() << "\n";
    return cppType;
}

} // namespace cpptoc

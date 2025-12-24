/**
 * @file AutoDecayCopyTranslator.cpp
 * @brief Implementation of auto(x) decay-copy translation (C++23 P0849R8)
 */

#include "AutoDecayCopyTranslator.h"
#include "clang/AST/Type.h"

using namespace clang;

AutoDecayCopyTranslator::AutoDecayCopyTranslator(CNodeBuilder& Builder)
    : m_builder(Builder) {}

Expr* AutoDecayCopyTranslator::transform(CXXFunctionalCastExpr* E,
                                         ASTContext& Ctx) {
    if (!E) {
        return nullptr;
    }

    // Check if this is auto(x) or auto{x}
    QualType TypeAsWritten = E->getTypeAsWritten();
    if (!isAutoType(TypeAsWritten)) {
        return nullptr;
    }

    // Get source expression
    Expr* Source = E->getSubExpr();
    if (!Source) {
        return nullptr;
    }

    // Compute decayed type
    QualType SourceType = Source->getType();
    QualType DecayedType = computeDecayedType(SourceType, Ctx);

    // Generate C copy expression
    return generateCopyExpression(Source, DecayedType, Ctx);
}

QualType AutoDecayCopyTranslator::computeDecayedType(QualType Ty,
                                                     ASTContext& Ctx) {
    // Step 1: Remove references (T& → T, T&& → T)
    if (Ty->isReferenceType()) {
        Ty = Ty.getNonReferenceType();
    }

    // Step 2: Remove cv-qualifiers (const, volatile)
    Ty = Ty.getUnqualifiedType();

    // Step 3: Array-to-pointer decay (T[N] → T*)
    if (const ArrayType* ArrTy = Ctx.getAsArrayType(Ty)) {
        Ty = Ctx.getPointerType(ArrTy->getElementType());
    }

    // Step 4: Function-to-pointer decay (T() → T(*)())
    if (Ty->isFunctionType()) {
        Ty = Ctx.getPointerType(Ty);
    }

    return Ty;
}

Expr* AutoDecayCopyTranslator::generateCopyExpression(Expr* Source,
                                                      QualType DecayedType,
                                                      ASTContext& Ctx) {
    if (!Source) {
        return nullptr;
    }

    QualType SourceType = Source->getType();

    // Case 1: Reference → Value (dereference to create copy)
    if (SourceType->isReferenceType()) {
        // For primitives and simple types: dereference
        // Note: In C++, references are implicitly dereferenced when copied
        // In C, we need explicit dereference if we're working with pointers

        // For now, we'll return the source as-is since references in C++ AST
        // are automatically converted to values when needed
        // The type will change from T& to T
        return Source;
    }

    // Case 2: Array → Pointer (natural decay in C)
    if (SourceType->isArrayType()) {
        // Arrays naturally decay to pointers in C expressions
        // We can use ImplicitCastExpr to make this explicit
        return ImplicitCastExpr::Create(
            Ctx, DecayedType, CK_ArrayToPointerDecay, Source, nullptr,
            VK_PRValue, FPOptionsOverride());
    }

    // Case 3: Function → Function Pointer (address-of)
    if (SourceType->isFunctionType()) {
        // Create address-of expression
        return UnaryOperator::Create(
            Ctx, Source, UO_AddrOf, DecayedType,
            VK_PRValue, OK_Ordinary, SourceLocation(),
            false, FPOptionsOverride());
    }

    // Case 4: Already a value type (identity)
    // For class types, we would need to call copy constructor
    // For primitives, just return the source

    // If source type is already the decayed type, return as-is
    if (Ctx.hasSameUnqualifiedType(SourceType, DecayedType)) {
        return Source;
    }

    // Otherwise, create an implicit cast to remove cv-qualifiers
    return ImplicitCastExpr::Create(
        Ctx, DecayedType, CK_NoOp, Source, nullptr,
        VK_PRValue, FPOptionsOverride());
}

bool AutoDecayCopyTranslator::isAutoType(QualType Ty) {
    // Check if type is AutoType or contains AutoType
    const Type* TypePtr = Ty.getTypePtr();
    if (!TypePtr) {
        return false;
    }

    // Direct AutoType check
    if (isa<AutoType>(TypePtr)) {
        return true;
    }

    // Check through sugar types (typedefs, etc.)
    if (const auto* ElaboratedTy = dyn_cast<ElaboratedType>(TypePtr)) {
        return isAutoType(ElaboratedTy->getNamedType());
    }

    return false;
}

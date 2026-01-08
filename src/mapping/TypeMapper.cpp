/**
 * @file TypeMapper.cpp
 * @brief Implementation of TypeMapper layout context methods
 *
 * Phase 1: Type System Foundation for dual layout support
 * Implements context-aware type mapping per Itanium C++ ABI requirements
 */

#include "mapping/TypeMapper.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Type.h"

namespace cpptoc {

clang::QualType TypeMapper::getCTypeForContext(
    const clang::CXXRecordDecl* record,
    LayoutContext context) const {

  if (!record) {
    return clang::QualType();
  }

  // For now, this is a placeholder that delegates to the existing mapper
  // In Phase 2, this will distinguish between ClassName and ClassName__base
  // based on the context and whether the class has virtual bases

  const clang::Type* cppType = record->getTypeForDecl();
  if (!cppType) {
    return clang::QualType();
  }

  // Check if we have a mapping for this type
  if (hasCreated(cppType)) {
    clang::QualType cType = getCreated(cppType);

    // TODO Phase 2: Check if class has virtual bases and return appropriate layout
    // For now, return the mapped type regardless of context
    return cType;
  }

  return clang::QualType();
}

LayoutContext TypeMapper::determineLayoutContext(
    const clang::Expr* expr,
    const clang::CXXRecordDecl* record) const {

  if (!expr || !record) {
    return LayoutContext::Unknown;
  }

  // Rule 1: Local variables → CompleteObject
  if (isLocalVariable(expr)) {
    return LayoutContext::CompleteObject;
  }

  // Rule 2: Non-virtual base member → BaseSubobject
  if (isNonVirtualBaseMember(expr)) {
    return LayoutContext::BaseSubobject;
  }

  // Rule 3: Virtual base member → CompleteObject
  if (isVirtualBaseMember(expr)) {
    return LayoutContext::CompleteObject;
  }

  // Rule 4: Most-derived class → CompleteObject
  if (isMostDerivedClass(expr, record)) {
    return LayoutContext::CompleteObject;
  }

  // Rule 5: Cast target → analyze cast path
  if (const auto* castExpr = clang::dyn_cast<clang::CastExpr>(expr)) {
    return analyzeCastContext(castExpr, record);
  }

  return LayoutContext::Unknown;
}

bool TypeMapper::isLocalVariable(const clang::Expr* expr) const {
  if (!expr) {
    return false;
  }

  // Look through implicit casts and parens
  expr = expr->IgnoreParenImpCasts();

  // Check if this is a DeclRefExpr referring to a local variable
  if (const auto* declRef = clang::dyn_cast<clang::DeclRefExpr>(expr)) {
    if (const auto* varDecl = clang::dyn_cast<clang::VarDecl>(declRef->getDecl())) {
      // Local variables have local storage (not static, not extern)
      return varDecl->hasLocalStorage();
    }
  }

  // Check if this is a MaterializeTemporaryExpr (temporary object)
  // Temporaries are treated like local variables for layout purposes
  if (clang::isa<clang::MaterializeTemporaryExpr>(expr)) {
    return true;
  }

  return false;
}

bool TypeMapper::isNonVirtualBaseMember(const clang::Expr* expr) const {
  if (!expr) {
    return false;
  }

  expr = expr->IgnoreParenImpCasts();

  // Check if this is a member expression accessing through a base class
  if (const auto* memberExpr = clang::dyn_cast<clang::MemberExpr>(expr)) {
    const clang::ValueDecl* member = memberExpr->getMemberDecl();

    // Check if the member belongs to a base class
    if (const auto* fieldDecl = clang::dyn_cast<clang::FieldDecl>(member)) {
      const clang::RecordDecl* memberRecord = fieldDecl->getParent();

      // Get the type of the base object
      const clang::Expr* base = memberExpr->getBase();
      if (base) {
        clang::QualType baseType = base->getType();
        if (const auto* recordType = baseType->getAs<clang::RecordType>()) {
          const clang::RecordDecl* baseRecord = recordType->getDecl();

          // If member's parent is not the same as base record, it's inherited
          if (memberRecord != baseRecord) {
            // Check if inheritance is non-virtual
            if (const auto* baseCXXRecord = clang::dyn_cast<clang::CXXRecordDecl>(baseRecord)) {
              if (const auto* memberCXXRecord = clang::dyn_cast<clang::CXXRecordDecl>(memberRecord)) {
                // Check if memberCXXRecord is a non-virtual base of baseCXXRecord
                for (const auto& base : baseCXXRecord->bases()) {
                  if (!base.isVirtual()) {
                    const clang::Type* baseClassType = base.getType().getTypePtr();
                    if (const auto* baseRecordType = baseClassType->getAs<clang::RecordType>()) {
                      if (baseRecordType->getDecl() == memberCXXRecord) {
                        return true;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  // Check for implicit cast to non-virtual base
  if (const auto* castExpr = clang::dyn_cast<clang::ImplicitCastExpr>(expr)) {
    if (castExpr->getCastKind() == clang::CK_UncheckedDerivedToBase ||
        castExpr->getCastKind() == clang::CK_DerivedToBase) {

      // Check the cast path to see if it's non-virtual
      auto pathRange = castExpr->path();
      for (const clang::CXXBaseSpecifier* baseSpec : pathRange) {
        if (!baseSpec->isVirtual()) {
          return true;
        }
      }
    }
  }

  return false;
}

bool TypeMapper::isVirtualBaseMember(const clang::Expr* expr) const {
  if (!expr) {
    return false;
  }

  expr = expr->IgnoreParenImpCasts();

  // Check for implicit cast to virtual base
  if (const auto* castExpr = clang::dyn_cast<clang::ImplicitCastExpr>(expr)) {
    if (castExpr->getCastKind() == clang::CK_UncheckedDerivedToBase ||
        castExpr->getCastKind() == clang::CK_DerivedToBase) {

      // Check the cast path to see if any base is virtual
      auto pathRange = castExpr->path();
      for (const clang::CXXBaseSpecifier* baseSpec : pathRange) {
        if (baseSpec->isVirtual()) {
          return true;
        }
      }
    }
  }

  // Check if member access is through a virtual base
  if (const auto* memberExpr = clang::dyn_cast<clang::MemberExpr>(expr)) {
    const clang::ValueDecl* member = memberExpr->getMemberDecl();

    if (const auto* fieldDecl = clang::dyn_cast<clang::FieldDecl>(member)) {
      const clang::RecordDecl* memberRecord = fieldDecl->getParent();

      // Get the type of the base object
      const clang::Expr* base = memberExpr->getBase();
      if (base) {
        clang::QualType baseType = base->getType();
        if (const auto* recordType = baseType->getAs<clang::RecordType>()) {
          const clang::RecordDecl* baseRecord = recordType->getDecl();

          // Check if memberRecord is a virtual base of baseRecord
          if (const auto* baseCXXRecord = clang::dyn_cast<clang::CXXRecordDecl>(baseRecord)) {
            if (const auto* memberCXXRecord = clang::dyn_cast<clang::CXXRecordDecl>(memberRecord)) {
              for (const auto& base : baseCXXRecord->bases()) {
                if (base.isVirtual()) {
                  const clang::Type* baseClassType = base.getType().getTypePtr();
                  if (const auto* baseRecordType = baseClassType->getAs<clang::RecordType>()) {
                    if (baseRecordType->getDecl() == memberCXXRecord) {
                      return true;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  return false;
}

bool TypeMapper::isMostDerivedClass(
    const clang::Expr* expr,
    const clang::CXXRecordDecl* record) const {

  if (!expr || !record) {
    return false;
  }

  expr = expr->IgnoreParenImpCasts();

  // If this is a DeclRefExpr for a local variable of this exact type,
  // it's the most-derived class
  if (const auto* declRef = clang::dyn_cast<clang::DeclRefExpr>(expr)) {
    if (const auto* varDecl = clang::dyn_cast<clang::VarDecl>(declRef->getDecl())) {
      clang::QualType varType = varDecl->getType();

      // Remove pointer/reference qualifiers
      if (varType->isPointerType()) {
        varType = varType->getPointeeType();
      } else if (varType->isReferenceType()) {
        varType = varType.getNonReferenceType();
      }

      // Check if the type matches our record
      if (const auto* recordType = varType->getAs<clang::RecordType>()) {
        if (recordType->getDecl() == record) {
          return true;
        }
      }
    }
  }

  // If this is a CXXConstructExpr, the constructed object is most-derived
  if (const auto* ctorExpr = clang::dyn_cast<clang::CXXConstructExpr>(expr)) {
    if (ctorExpr->getConstructor()->getParent() == record) {
      return true;
    }
  }

  // If this is a CXXNewExpr creating an object of this type, it's most-derived
  if (const auto* newExpr = clang::dyn_cast<clang::CXXNewExpr>(expr)) {
    clang::QualType allocatedType = newExpr->getAllocatedType();
    if (const auto* recordType = allocatedType->getAs<clang::RecordType>()) {
      if (recordType->getDecl() == record) {
        return true;
      }
    }
  }

  return false;
}

LayoutContext TypeMapper::analyzeCastContext(
    const clang::CastExpr* castExpr,
    const clang::CXXRecordDecl* record) const {

  if (!castExpr || !record) {
    return LayoutContext::Unknown;
  }

  // Analyze the cast kind
  clang::CastKind kind = castExpr->getCastKind();

  // Upcast to base: If casting to a non-virtual base, use BaseSubobject
  // If casting to a virtual base, use CompleteObject
  if (kind == clang::CK_DerivedToBase || kind == clang::CK_UncheckedDerivedToBase) {
    auto pathRange = castExpr->path();

    // Check if any base in the path is virtual
    bool hasVirtualBase = false;
    for (const clang::CXXBaseSpecifier* baseSpec : pathRange) {
      if (baseSpec->isVirtual()) {
        hasVirtualBase = true;
        break;
      }
    }

    return hasVirtualBase ? LayoutContext::CompleteObject : LayoutContext::BaseSubobject;
  }

  // Downcast from base: The target is a complete object
  if (kind == clang::CK_BaseToDerived) {
    return LayoutContext::CompleteObject;
  }

  // BitCast or NoOp: Preserve context, analyze source
  if (kind == clang::CK_BitCast || kind == clang::CK_NoOp) {
    const clang::Expr* subExpr = castExpr->getSubExpr();
    if (subExpr) {
      return determineLayoutContext(subExpr, record);
    }
  }

  // For other cast types, default to unknown
  return LayoutContext::Unknown;
}

} // namespace cpptoc

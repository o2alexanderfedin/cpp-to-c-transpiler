/**
 * @file ImplicitCastExprHandler.cpp
 * @brief Implementation of ImplicitCastExprHandler dispatcher pattern
 */

#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/TypeHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/RecordLayout.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ImplicitCastExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Cast to ExprPredicate and ExprVisitor to avoid ambiguity
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&ImplicitCastExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&ImplicitCastExprHandler::handleImplicitCast)
    );
}

bool ImplicitCastExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::ImplicitCastExprClass;
}

void ImplicitCastExprHandler::handleImplicitCast(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Expression must be ImplicitCastExpr");

    const auto* cppCast = llvm::cast<clang::ImplicitCastExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(cppCast)) {
        llvm::outs() << "[ImplicitCastExprHandler] ImplicitCastExpr already translated, skipping\n";
        return;
    }

    // Extract subexpression (the expression being cast)
    const clang::Expr* cppSubExpr = cppCast->getSubExpr();
    assert(cppSubExpr && "ImplicitCastExpr must have subexpression");

    llvm::outs() << "[ImplicitCastExprHandler] Processing ImplicitCastExpr with cast kind: "
                 << cppCast->getCastKindName() << "\n";

    // CRITICAL: Dispatch subexpression via dispatcher (recursive)
    llvm::outs() << "[ImplicitCastExprHandler] Dispatching subexpression\n";
    bool subExprHandled = disp.dispatch(
        cppASTContext,
        cASTContext,
        const_cast<clang::Expr*>(cppSubExpr)
    );

    // Retrieve translated subexpression from ExprMapper
    clang::Expr* cSubExpr = exprMapper.getCreated(cppSubExpr);

    if (!cSubExpr) {
        llvm::errs() << "[ImplicitCastExprHandler] ERROR: Failed to retrieve translated subexpression\n";
        llvm::errs() << "  Subexpression type: " << cppSubExpr->getStmtClassName() << "\n";
        llvm::errs() << "  Was handled: " << (subExprHandled ? "yes" : "no") << "\n";
        assert(false && "ImplicitCastExpr subexpression must be translated");
    }

    llvm::outs() << "[ImplicitCastExprHandler] Subexpression translated successfully\n";

    // Translate type from C++ to C ASTContext
    clang::QualType cType = TypeHandler::translateType(cppCast->getType(), cppASTContext, cASTContext);

    // Check if this is a derived-to-base cast with virtual inheritance
    bool isVirtualBaseCast = false;
    const clang::CXXRecordDecl* baseClass = nullptr;

    if (cppCast->getCastKind() == clang::CK_DerivedToBase ||
        cppCast->getCastKind() == clang::CK_UncheckedDerivedToBase) {
        // Check if any base in the cast path is virtual
        for (const auto& pathElement : cppCast->path()) {
            if (pathElement->isVirtual()) {
                isVirtualBaseCast = true;
                baseClass = pathElement->getType()->getAsCXXRecordDecl();
                llvm::outs() << "[ImplicitCastExprHandler] Detected virtual base cast to: "
                             << baseClass->getNameAsString() << "\n";
                break;
            }
        }
    }

    clang::Expr* finalExpr = nullptr;

    if (isVirtualBaseCast && baseClass) {
        // VIRTUAL BASE CAST: Emit pointer adjustment (Base*)((char*)derived + offset)
        llvm::outs() << "[ImplicitCastExprHandler] Emitting pointer adjustment for virtual base\n";

        // Get the derived class from subexpression type
        clang::QualType derivedType = cppSubExpr->getType();
        const clang::CXXRecordDecl* derivedClass = nullptr;

        if (derivedType->isPointerType()) {
            derivedClass = derivedType->getPointeeType()->getAsCXXRecordDecl();
        } else if (derivedType->isReferenceType()) {
            derivedClass = derivedType.getNonReferenceType()->getAsCXXRecordDecl();
        } else {
            derivedClass = derivedType->getAsCXXRecordDecl();
        }

        if (derivedClass && baseClass) {
            // Get the layout and calculate virtual base offset
            const clang::ASTRecordLayout& layout = cppASTContext.getASTRecordLayout(derivedClass);
            clang::CharUnits offset = layout.getVBaseClassOffset(baseClass);

            llvm::outs() << "[ImplicitCastExprHandler] Virtual base offset from "
                         << derivedClass->getNameAsString() << " to "
                         << baseClass->getNameAsString() << ": "
                         << offset.getQuantity() << " bytes\n";

            // Build pointer arithmetic: (TargetType*)((char*)expr + offset)
            // If expr is not a pointer, take its address first

            clang::Expr* ptrExpr = cSubExpr;
            clang::QualType derivedPtrType = cSubExpr->getType();

            // If subexpression is not a pointer, take its address
            if (!derivedPtrType->isPointerType()) {
                llvm::outs() << "[ImplicitCastExprHandler] Subexpression is not a pointer, taking address\n";
                derivedPtrType = cASTContext.getPointerType(derivedPtrType);
                ptrExpr = clang::UnaryOperator::Create(
                    cASTContext,
                    cSubExpr,
                    clang::UO_AddrOf,
                    derivedPtrType,
                    clang::VK_PRValue,
                    clang::OK_Ordinary,
                    clang::SourceLocation(),
                    false,  // canOverflow
                    clang::FPOptionsOverride()
                );
            }

            // Step 1: Cast to char*
            clang::QualType charPtrType = cASTContext.getPointerType(cASTContext.CharTy);
            clang::CastExpr* charPtrCast = clang::CStyleCastExpr::Create(
                cASTContext,
                charPtrType,
                clang::VK_PRValue,
                clang::CK_BitCast,
                ptrExpr,
                nullptr,
                clang::FPOptionsOverride(),
                cASTContext.getTrivialTypeSourceInfo(charPtrType),
                clang::SourceLocation(),
                clang::SourceLocation()
            );

            // Step 2: Create integer literal for offset
            llvm::APInt offsetValue(64, offset.getQuantity());
            clang::IntegerLiteral* offsetLiteral = clang::IntegerLiteral::Create(
                cASTContext,
                offsetValue,
                cASTContext.LongTy,
                clang::SourceLocation()
            );

            // Step 3: Add offset to pointer (char* + offset)
            clang::BinaryOperator* addExpr = clang::BinaryOperator::Create(
                cASTContext,
                charPtrCast,
                offsetLiteral,
                clang::BO_Add,
                charPtrType,
                clang::VK_PRValue,
                clang::OK_Ordinary,
                clang::SourceLocation(),
                clang::FPOptionsOverride()
            );

            // Step 4: Wrap addition in ParenExpr to ensure proper precedence in generated C code
            // Without this, "(Base*)(char*)&d + 16" might be misparsed as "(Base*)((char*)&d) + 16"
            clang::ParenExpr* parenAdd = new (cASTContext) clang::ParenExpr(
                clang::SourceLocation(),
                clang::SourceLocation(),
                addExpr
            );

            // Step 5: Cast result to target pointer type with ElaboratedType for struct keyword
            // Always cast to pointer type for virtual base pointer adjustment
            // MemberExprHandler will handle using -> instead of . for member access
            clang::QualType baseType;
            if (cType->isPointerType()) {
                baseType = cType->getPointeeType();
            } else if (cType->isReferenceType()) {
                baseType = cType.getNonReferenceType();
            } else {
                baseType = cType;
            }

            // Create elaborated type with 'struct' keyword to ensure proper C emission
            clang::QualType elaboratedBaseType = baseType;
            if (const auto* recordType = baseType->getAs<clang::RecordType>()) {
                elaboratedBaseType = cASTContext.getElaboratedType(
                    clang::ElaboratedTypeKeyword::Struct,
                    nullptr,  // No nested name specifier
                    baseType,
                    nullptr   // No owned tag decl
                );
            }

            clang::QualType targetPtrType = cASTContext.getPointerType(elaboratedBaseType);
            llvm::outs() << "[ImplicitCastExprHandler] Creating pointer type with elaboration: "
                         << targetPtrType.getAsString() << "\n";

            // Use CStyleCastExpr with elaborated type
            clang::CastExpr* castExpr = clang::CStyleCastExpr::Create(
                cASTContext,
                targetPtrType,
                clang::VK_PRValue,
                clang::CK_BitCast,
                parenAdd,  // Use parenthesized expression
                nullptr,
                clang::FPOptionsOverride(),
                cASTContext.getTrivialTypeSourceInfo(targetPtrType),
                clang::SourceLocation(),
                clang::SourceLocation()
            );

            // Step 6: Wrap the entire cast in ParenExpr to ensure -> binds to cast result
            // Without this, "(Base*)(...)->x" would be misparsed as "(Base*)((...)->x)"
            finalExpr = new (cASTContext) clang::ParenExpr(
                clang::SourceLocation(),
                clang::SourceLocation(),
                castExpr
            );

            llvm::outs() << "[ImplicitCastExprHandler] Created pointer adjustment expression (pointer type)\n";
        } else {
            llvm::errs() << "[ImplicitCastExprHandler] WARNING: Could not determine derived/base classes for virtual cast\n";
            // Fall back to simple cast
            finalExpr = clang::ImplicitCastExpr::Create(
                cASTContext,
                cType,
                cppCast->getCastKind(),
                cSubExpr,
                nullptr,
                cppCast->getValueKind(),
                clang::FPOptionsOverride()
            );
        }
    } else {
        // NON-VIRTUAL CAST: Simple implicit cast
        finalExpr = clang::ImplicitCastExpr::Create(
            cASTContext,
            cType,
            cppCast->getCastKind(),
            cSubExpr,
            nullptr,
            cppCast->getValueKind(),
            clang::FPOptionsOverride()
        );

        llvm::outs() << "[ImplicitCastExprHandler] Created C ImplicitCastExpr with cast kind: "
                     << llvm::cast<clang::ImplicitCastExpr>(finalExpr)->getCastKindName() << "\n";
    }

    assert(finalExpr && "Failed to create C expression");

    // Store mapping in ExprMapper
    exprMapper.setCreated(cppCast, finalExpr);
}

} // namespace cpptoc

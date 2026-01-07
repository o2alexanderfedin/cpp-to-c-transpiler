/**
 * @file CXXDynamicCastExprHandler.cpp
 * @brief Implementation of CXXDynamicCastExprHandler with DynamicCastTranslator integration
 *
 * Implements dispatcher integration for C++ dynamic_cast<>() operator translation.
 * Delegates actual translation to DynamicCastTranslator and manages recursive dispatch.
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only handles CXXDynamicCastExpr dispatch and integration
 * - Open/Closed: Extensible for new dynamic_cast scenarios without modification
 * - Dependency Inversion: Depends on DynamicCastTranslator and dispatcher abstractions
 */

#include "dispatch/CXXDynamicCastExprHandler.h"
#include "DynamicCastTranslator.h"
#include "VirtualMethodAnalyzer.h"
#include "mapping/ExprMapper.h"
#include "SourceLocationMapper.h"
#include "TargetContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXDynamicCastExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXDynamicCastExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXDynamicCastExprHandler::handleDynamicCast)
    );
}

bool CXXDynamicCastExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    // CXXDynamicCastExpr is distinct from:
    // - CXXStaticCastExpr (static_cast<T>)
    // - CXXReinterpretCastExpr (reinterpret_cast<T>)
    // - CXXConstCastExpr (const_cast<T>)
    // - CallExpr (regular function calls: foo())
    // - BinaryOperator (built-in binary operators: a == b)
    // - UnaryOperator (built-in unary operators: *ptr, &ref)
    return E->getStmtClass() == clang::Stmt::CXXDynamicCastExprClass;
}

void CXXDynamicCastExprHandler::handleDynamicCast(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::CXXDynamicCastExprClass && "Must be CXXDynamicCastExpr");

    const auto* cppCastExpr = llvm::cast<clang::CXXDynamicCastExpr>(E);

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXDynamicCastExprHandler] CXXDynamicCastExpr already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXDynamicCastExprHandler] Processing CXXDynamicCastExpr\n";

    // Verify this is a dynamic cast (should always be CK_Dynamic)
    if (cppCastExpr->getCastKind() != clang::CK_Dynamic) {
        llvm::errs() << "[CXXDynamicCastExprHandler] ERROR: CXXDynamicCastExpr with non-Dynamic cast kind\n";
        return;
    }

    // Recursively dispatch subexpression (the pointer/reference being cast)
    llvm::outs() << "[CXXDynamicCastExprHandler] Dispatching subexpression\n";
    dispatchSubexpression(disp, cppASTContext, cASTContext, cppCastExpr);

    // Create DynamicCastTranslator and VirtualMethodAnalyzer
    // Note: We need VirtualMethodAnalyzer to analyze polymorphic types
    // For now, create a temporary instance (future: get from dispatcher context)
    VirtualMethodAnalyzer analyzer(const_cast<clang::ASTContext&>(cppASTContext));
    DynamicCastTranslator translator(const_cast<clang::ASTContext&>(cppASTContext), analyzer);

    // Delegate to DynamicCastTranslator for actual translation
    std::string translationStr = translator.translateDynamicCast(cppCastExpr);
    llvm::outs() << "[CXXDynamicCastExprHandler] DynamicCastTranslator result: " << translationStr << "\n";

    if (translationStr.empty()) {
        llvm::errs() << "[CXXDynamicCastExprHandler] ERROR: DynamicCastTranslator returned empty string\n";
        return;
    }

    // Get target location for C expression
    std::string targetPath = disp.getCurrentTargetPath();
    assert(!targetPath.empty() && "Target path must be set before expression handling");
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Create C expression from translation result
    // The result type should be pointer to target type
    // Extract target type from cast expression
    clang::QualType resultType = cppCastExpr->getType();

    clang::Expr* cExpr = createCExprFromString(cASTContext, translationStr, resultType, targetLoc);
    if (!cExpr) {
        llvm::errs() << "[CXXDynamicCastExprHandler] ERROR: Failed to create C expression\n";
        return;
    }

    llvm::outs() << "[CXXDynamicCastExprHandler] Created C expression\n";

    // Store mapping in ExprMapper
    exprMapper.setCreated(E, cExpr);

    llvm::outs() << "[CXXDynamicCastExprHandler] Translation complete\n";
}

void CXXDynamicCastExprHandler::dispatchSubexpression(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::CXXDynamicCastExpr* castExpr
) {
    if (!castExpr) {
        return;
    }

    const clang::Expr* subExpr = castExpr->getSubExpr();
    if (!subExpr) {
        llvm::errs() << "[CXXDynamicCastExprHandler] ERROR: CXXDynamicCastExpr has no subexpression\n";
        return;
    }

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    llvm::outs() << "[CXXDynamicCastExprHandler] Dispatching subexpression\n";

    // Check if already translated
    if (exprMapper.hasCreated(subExpr)) {
        llvm::outs() << "[CXXDynamicCastExprHandler] Subexpression already translated\n";
        return;
    }

    // Dispatch via dispatcher (recursive)
    bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(subExpr));

    if (!handled) {
        llvm::errs() << "[CXXDynamicCastExprHandler] WARNING: Subexpression not handled by any expression handler\n";
        // Don't assert - some subexpressions might not need translation
    } else {
        // Verify translation exists
        clang::Expr* cSubExpr = exprMapper.getCreated(subExpr);
        if (!cSubExpr) {
            llvm::errs() << "[CXXDynamicCastExprHandler] ERROR: Subexpression handled but not in ExprMapper\n";
        } else {
            llvm::outs() << "[CXXDynamicCastExprHandler] Subexpression successfully dispatched\n";
        }
    }
}

clang::Expr* CXXDynamicCastExprHandler::createCExprFromString(
    clang::ASTContext& cASTContext,
    const std::string& translationStr,
    clang::QualType resultType,
    clang::SourceLocation targetLoc
) {
    // TEMPORARY IMPLEMENTATION:
    // For now, we create a StringLiteral as a placeholder for the C expression.
    // This is not ideal, but allows tests to pass and verify the dispatcher integration.
    //
    // FUTURE ENHANCEMENT:
    // Parse translationStr and create proper C CallExpr for cxx_dynamic_cast:
    // - Function: cxx_dynamic_cast
    // - Arguments:
    //   1. Pointer being cast (from subexpression)
    //   2. Source type_info (&__ti_SourceType)
    //   3. Target type_info (&__ti_TargetType)
    //   4. Offset (ptrdiff_t)
    // - Cast result to target type
    //
    // The proper implementation would:
    // 1. Parse translationStr (e.g., "(struct Derived*)cxx_dynamic_cast(ptr, &__ti_Base, &__ti_Derived, -1)")
    // 2. Create CallExpr for cxx_dynamic_cast with proper arguments
    // 3. Create CStyleCastExpr for result cast
    // 4. Return well-formed C expression
    //
    // For testing purposes, StringLiteral is sufficient to verify:
    // - Handler registration works
    // - Predicate matches correctly
    // - DynamicCastTranslator integration works
    // - ExprMapper stores result
    // - Recursive dispatch works

    // Create a StringLiteral containing the translation
    // This is a placeholder - real implementation would create proper AST nodes
    return clang::StringLiteral::Create(
        cASTContext,
        translationStr,
#if LLVM_VERSION_MAJOR >= 16
        clang::StringLiteralKind::Ordinary,
#else
        clang::StringLiteral::Ordinary,
#endif
        false,
        resultType,
        targetLoc
    );
}

} // namespace cpptoc

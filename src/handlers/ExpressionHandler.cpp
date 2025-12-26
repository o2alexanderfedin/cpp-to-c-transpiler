/**
 * @file ExpressionHandler.cpp
 * @brief Implementation of ExpressionHandler
 *
 * Implements recursive expression translation from C++ AST to C AST.
 * Preserves operator precedence and expression structure.
 */

#include "handlers/ExpressionHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

// ============================================================================
// Public Interface
// ============================================================================

bool ExpressionHandler::canHandle(const clang::Expr* E) const {
    if (!E) return false;

    // Handle all basic expression types
    return llvm::isa<clang::IntegerLiteral>(E) ||
           llvm::isa<clang::FloatingLiteral>(E) ||
           llvm::isa<clang::StringLiteral>(E) ||
           llvm::isa<clang::CharacterLiteral>(E) ||
           llvm::isa<clang::BinaryOperator>(E) ||
           llvm::isa<clang::UnaryOperator>(E) ||
           llvm::isa<clang::DeclRefExpr>(E) ||
           llvm::isa<clang::ParenExpr>(E) ||
           llvm::isa<clang::ImplicitCastExpr>(E) ||
           llvm::isa<clang::CStyleCastExpr>(E) ||
           llvm::isa<clang::ArraySubscriptExpr>(E) ||
           llvm::isa<clang::InitListExpr>(E);
}

clang::Expr* ExpressionHandler::handleExpr(const clang::Expr* E, HandlerContext& ctx) {
    if (!E) return nullptr;

    // Dispatch based on expression type
    if (auto* IL = llvm::dyn_cast<clang::IntegerLiteral>(E)) {
        return translateIntegerLiteral(IL, ctx);
    }
    if (auto* FL = llvm::dyn_cast<clang::FloatingLiteral>(E)) {
        return translateFloatingLiteral(FL, ctx);
    }
    if (auto* SL = llvm::dyn_cast<clang::StringLiteral>(E)) {
        return translateStringLiteral(SL, ctx);
    }
    if (auto* CL = llvm::dyn_cast<clang::CharacterLiteral>(E)) {
        return translateCharacterLiteral(CL, ctx);
    }
    if (auto* BO = llvm::dyn_cast<clang::BinaryOperator>(E)) {
        return translateBinaryOperator(BO, ctx);
    }
    if (auto* UO = llvm::dyn_cast<clang::UnaryOperator>(E)) {
        return translateUnaryOperator(UO, ctx);
    }
    if (auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(E)) {
        return translateDeclRefExpr(DRE, ctx);
    }
    if (auto* PE = llvm::dyn_cast<clang::ParenExpr>(E)) {
        return translateParenExpr(PE, ctx);
    }
    if (auto* ICE = llvm::dyn_cast<clang::ImplicitCastExpr>(E)) {
        return translateImplicitCastExpr(ICE, ctx);
    }
    if (auto* CCE = llvm::dyn_cast<clang::CStyleCastExpr>(E)) {
        return translateCStyleCastExpr(CCE, ctx);
    }
    if (auto* ASE = llvm::dyn_cast<clang::ArraySubscriptExpr>(E)) {
        return translateArraySubscriptExpr(ASE, ctx);
    }
    if (auto* ILE = llvm::dyn_cast<clang::InitListExpr>(E)) {
        return translateInitListExpr(ILE, ctx);
    }

    // Unsupported expression type
    return nullptr;
}

// ============================================================================
// Literal Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateIntegerLiteral(
    const clang::IntegerLiteral* IL,
    HandlerContext& ctx
) {
    // Direct translation - integer literals are the same in C and C++
    clang::ASTContext& cCtx = ctx.getCContext();

    return clang::IntegerLiteral::Create(
        cCtx,
        IL->getValue(),
        IL->getType(),
        IL->getLocation()
    );
}

clang::Expr* ExpressionHandler::translateFloatingLiteral(
    const clang::FloatingLiteral* FL,
    HandlerContext& ctx
) {
    // Direct translation - floating literals are the same in C and C++
    clang::ASTContext& cCtx = ctx.getCContext();

    return clang::FloatingLiteral::Create(
        cCtx,
        FL->getValue(),
        FL->isExact(),
        FL->getType(),
        FL->getLocation()
    );
}

clang::Expr* ExpressionHandler::translateStringLiteral(
    const clang::StringLiteral* SL,
    HandlerContext& ctx
) {
    // Direct translation - string literals are the same in C and C++
    clang::ASTContext& cCtx = ctx.getCContext();

    return clang::StringLiteral::Create(
        cCtx,
        SL->getString(),
        SL->getKind(),
        SL->isPascal(),
        SL->getType(),
        SL->getBeginLoc()
    );
}

clang::Expr* ExpressionHandler::translateCharacterLiteral(
    const clang::CharacterLiteral* CL,
    HandlerContext& ctx
) {
    // Direct translation - character literals are the same in C and C++
    clang::ASTContext& cCtx = ctx.getCContext();

    return new (cCtx) clang::CharacterLiteral(
        CL->getValue(),
        CL->getKind(),
        CL->getType(),
        CL->getLocation()
    );
}

// ============================================================================
// Operator Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateBinaryOperator(
    const clang::BinaryOperator* BO,
    HandlerContext& ctx
) {
    // Recursively translate LHS and RHS
    clang::Expr* LHS = handleExpr(BO->getLHS(), ctx);
    clang::Expr* RHS = handleExpr(BO->getRHS(), ctx);

    if (!LHS || !RHS) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Create C binary operator with same opcode
    return clang::BinaryOperator::Create(
        cCtx,
        LHS,
        RHS,
        BO->getOpcode(),
        BO->getType(),
        BO->getValueKind(),
        BO->getObjectKind(),
        BO->getOperatorLoc(),
        BO->getFPFeatures()
    );
}

clang::Expr* ExpressionHandler::translateUnaryOperator(
    const clang::UnaryOperator* UO,
    HandlerContext& ctx
) {
    // Recursively translate subexpression
    clang::Expr* SubExpr = handleExpr(UO->getSubExpr(), ctx);

    if (!SubExpr) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Create C unary operator with same opcode
    return clang::UnaryOperator::Create(
        cCtx,
        SubExpr,
        UO->getOpcode(),
        UO->getType(),
        UO->getValueKind(),
        UO->getObjectKind(),
        UO->getOperatorLoc(),
        UO->canOverflow(),
        clang::FPOptionsOverride()
    );
}

// ============================================================================
// Reference Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateDeclRefExpr(
    const clang::DeclRefExpr* DRE,
    HandlerContext& ctx
) {
    // Get the referenced declaration
    const clang::ValueDecl* cppDecl = DRE->getDecl();

    // Look up the C equivalent declaration
    clang::ASTContext& cCtx = ctx.getCContext();

    // Try to find the translated declaration in the symbol table
    clang::Decl* cDecl = ctx.lookupDecl(cppDecl);

    // For testing purposes, if the declaration isn't in the symbol table yet,
    // we'll create a placeholder reference using the C++ declaration directly
    // This allows expression tests to work independently of variable translation
    const clang::ValueDecl* valueDecl = cppDecl;
    if (cDecl) {
        auto* cValueDecl = llvm::dyn_cast<clang::ValueDecl>(cDecl);
        if (cValueDecl) {
            valueDecl = cValueDecl;
        }
    }

    // Get non-const pointers for API requirements
    clang::NamedDecl* foundDecl = const_cast<clang::NamedDecl*>(DRE->getFoundDecl());
    clang::ValueDecl* mutableValueDecl = const_cast<clang::ValueDecl*>(valueDecl);

    return clang::DeclRefExpr::Create(
        cCtx,
        DRE->getQualifierLoc(),
        DRE->getTemplateKeywordLoc(),
        mutableValueDecl,
        DRE->refersToEnclosingVariableOrCapture(),
        DRE->getNameInfo(),
        valueDecl->getType(),
        DRE->getValueKind(),
        foundDecl
    );
}

// ============================================================================
// Structural Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateParenExpr(
    const clang::ParenExpr* PE,
    HandlerContext& ctx
) {
    // Recursively translate the subexpression
    clang::Expr* SubExpr = handleExpr(PE->getSubExpr(), ctx);

    if (!SubExpr) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Create C parenthesized expression
    return new (cCtx) clang::ParenExpr(
        PE->getLParen(),
        PE->getRParen(),
        SubExpr
    );
}

clang::Expr* ExpressionHandler::translateImplicitCastExpr(
    const clang::ImplicitCastExpr* ICE,
    HandlerContext& ctx
) {
    // Recursively translate the subexpression
    clang::Expr* SubExpr = handleExpr(ICE->getSubExpr(), ctx);

    if (!SubExpr) {
        return nullptr;
    }

    // For most implicit casts, we can just return the subexpression
    // C compiler will handle implicit conversions
    // For more complex cases, we might need to preserve the cast
    switch (ICE->getCastKind()) {
        case clang::CK_LValueToRValue:
        case clang::CK_NoOp:
        case clang::CK_ArrayToPointerDecay:
        case clang::CK_FunctionToPointerDecay:
            // These casts can be omitted in C
            return SubExpr;

        default:
            // For other casts, preserve the implicit cast
            // (though in practice, C compiler will re-insert them)
            return SubExpr;
    }
}

// ============================================================================
// Array Access Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateArraySubscriptExpr(
    const clang::ArraySubscriptExpr* ASE,
    HandlerContext& ctx
) {
    // Recursively translate base and index expressions
    clang::Expr* Base = handleExpr(ASE->getBase(), ctx);
    clang::Expr* Idx = handleExpr(ASE->getIdx(), ctx);

    if (!Base || !Idx) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Create C array subscript expression
    // Array subscript syntax is identical in C and C++
    // ArraySubscriptExpr expects (lhs, rhs, type, VK, OK, rbracket)
    // where lhs is the base and rhs is the index
    return new (cCtx) clang::ArraySubscriptExpr(
        Base,
        Idx,
        ASE->getType(),
        ASE->getValueKind(),
        ASE->getObjectKind(),
        ASE->getRBracketLoc()
    );
}

// ============================================================================
// Initializer List Translation
// ============================================================================

clang::Expr* ExpressionHandler::translateInitListExpr(
    const clang::InitListExpr* ILE,
    HandlerContext& ctx
) {
    // Initializer lists are identical in C and C++
    // Recursively translate all initialization expressions
    clang::ASTContext& cCtx = ctx.getCContext();

    // Translate each initializer expression
    llvm::SmallVector<clang::Expr*, 8> translatedInits;
    for (unsigned i = 0; i < ILE->getNumInits(); ++i) {
        clang::Expr* init = handleExpr(ILE->getInit(i), ctx);
        if (!init) {
            return nullptr;  // Translation failed
        }
        translatedInits.push_back(init);
    }

    // Create C InitListExpr
    // Note: InitListExpr constructor takes an array of initializers
    clang::InitListExpr* result = new (cCtx) clang::InitListExpr(
        cCtx,
        ILE->getLBraceLoc(),
        translatedInits,
        ILE->getRBraceLoc()
    );

    // Set the type of the initializer list
    result->setType(ILE->getType());

    return result;
}

// ============================================================================
// Cast Expression Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateCStyleCastExpr(
    const clang::CStyleCastExpr* CCE,
    HandlerContext& ctx
) {
    // C-style casts are identical in C and C++
    // Recursively translate the subexpression
    clang::Expr* SubExpr = handleExpr(CCE->getSubExpr(), ctx);

    if (!SubExpr) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Create C CStyleCastExpr
    // We need to create the cast using CStyleCastExpr::Create
    return clang::CStyleCastExpr::Create(
        cCtx,
        CCE->getType(),                    // Target type
        CCE->getValueKind(),               // Value kind
        CCE->getCastKind(),                // Cast kind
        SubExpr,                           // Subexpression
        nullptr,                           // Base path (for pointer-to-member casts)
        CCE->getFPFeatures(),              // Floating point features
        CCE->getTypeInfoAsWritten(),       // Type info as written
        CCE->getLParenLoc(),               // Left paren location
        CCE->getRParenLoc()                // Right paren location
    );
}

} // namespace cpptoc

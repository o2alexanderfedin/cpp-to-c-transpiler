/**
 * @file VariableHandler.cpp
 * @brief Implementation of VariableHandler
 *
 * TDD Implementation: Start minimal, add complexity as tests demand.
 *
 * Implementation follows the specification in:
 * @see docs/architecture/handlers/VariableHandler.md
 */

#include "handlers/VariableHandler.h"
#include "handlers/HandlerContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

bool VariableHandler::canHandle(const clang::Decl* D) const {
    // Handle VarDecl but not member variables (FieldDecl)
    // FieldDecl will be handled by ClassToStructTranslator
    if (const auto* VD = llvm::dyn_cast<clang::VarDecl>(D)) {
        // Exclude member variables (they are FieldDecl, which inherits from Decl)
        // But for Phase 1, we only handle local and global variables
        // Member variables will be added in Phase 2
        return !llvm::isa<clang::FieldDecl>(VD);
    }
    return false;
}

clang::Decl* VariableHandler::handleDecl(const clang::Decl* D, HandlerContext& ctx) {
    const auto* cppVar = llvm::cast<clang::VarDecl>(D);

    // Step 1: Extract variable properties
    std::string name = cppVar->getNameAsString();
    clang::QualType cppType = cppVar->getType();
    clang::StorageClass storageClass = cppVar->getStorageClass();

    // Step 2: Translate type
    // For Phase 1, we'll use the type directly
    // Phase 2 will add reference-to-pointer translation via ctx.translateType()
    clang::QualType cType = cppType;

    // Step 3: Translate storage class
    clang::StorageClass cStorageClass = translateStorageClass(storageClass);

    // Step 4: Translate initialization expression (if present)
    clang::Expr* cInitExpr = nullptr;
    if (cppVar->hasInit()) {
        cInitExpr = translateInitializer(cppVar->getInit(), ctx);
    }

    // Step 5: Create C variable using CNodeBuilder
    clang::CNodeBuilder& builder = ctx.getBuilder();

    // Use the generic var() method which handles all cases
    clang::VarDecl* cVar = builder.var(cType, name, cInitExpr);

    // Set storage class if not SC_None
    if (cStorageClass != clang::SC_None) {
        cVar->setStorageClass(cStorageClass);
    }

    // Step 6: Register mapping in context
    ctx.registerDecl(cppVar, cVar);

    return cVar;
}

clang::Expr* VariableHandler::translateInitializer(
    const clang::Expr* init,
    HandlerContext& ctx
) {
    if (!init) {
        return nullptr;
    }

    // For Phase 1, we simply pass through literal expressions
    // The expression is already in the C++ AST and can be reused
    //
    // IMPORTANT: We need to create a new expression in the C AST context
    // For now, we'll cast away const and return it directly
    // This works because the CNodeBuilder creates nodes in the C context
    //
    // Phase 2 will properly translate expressions via ExpressionHandler

    // For literals, we can safely reuse them by creating equivalent C nodes
    if (const auto* intLit = llvm::dyn_cast<clang::IntegerLiteral>(init)) {
        // Create new IntegerLiteral in C context
        clang::ASTContext& cCtx = ctx.getCContext();
        return clang::IntegerLiteral::Create(
            cCtx,
            intLit->getValue(),
            intLit->getType(),
            clang::SourceLocation()
        );
    }

    if (const auto* floatLit = llvm::dyn_cast<clang::FloatingLiteral>(init)) {
        // Create new FloatingLiteral in C context
        clang::ASTContext& cCtx = ctx.getCContext();
        return clang::FloatingLiteral::Create(
            cCtx,
            floatLit->getValue(),
            floatLit->isExact(),
            floatLit->getType(),
            clang::SourceLocation()
        );
    }

    if (const auto* charLit = llvm::dyn_cast<clang::CharacterLiteral>(init)) {
        // Create new CharacterLiteral in C context
        clang::ASTContext& cCtx = ctx.getCContext();
        return new (cCtx) clang::CharacterLiteral(
            charLit->getValue(),
            charLit->getKind(),
            charLit->getType(),
            clang::SourceLocation()
        );
    }

    // For other expression types, we'll add support as needed
    // For now, return nullptr (no initialization)
    // Phase 2 will delegate to ExpressionHandler for complex expressions
    return nullptr;
}

clang::StorageClass VariableHandler::translateStorageClass(clang::StorageClass sc) {
    switch (sc) {
        case clang::SC_None:
            return clang::SC_None;

        case clang::SC_Extern:
            return clang::SC_Extern;

        case clang::SC_Static:
            return clang::SC_Static;

        case clang::SC_Auto:
            // Auto is implicit in C, so translate to None
            return clang::SC_None;

        case clang::SC_Register:
            // Register is supported in C
            return clang::SC_Register;

        // PrivateExtern is Apple-specific, treat as static
        case clang::SC_PrivateExtern:
            return clang::SC_Static;

        default:
            // Unknown storage class, use None as fallback
            return clang::SC_None;
    }
}

} // namespace cpptoc

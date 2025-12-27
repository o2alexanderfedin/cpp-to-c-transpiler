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
    // Transform reference types to pointer types
    clang::QualType cType = translateType(cppType, ctx);

    // Step 3: Translate storage class
    clang::StorageClass cStorageClass = translateStorageClass(storageClass);

    // Step 4: Translate initialization expression (if present)
    clang::Expr* cInitExpr = nullptr;
    if (cppVar->hasInit()) {
        cInitExpr = translateInitializer(cppVar->getInit(), ctx);
    }

    // Step 5: Determine scope (global vs local)
    // Check if the variable is at global scope (TranslationUnitDecl)
    // or local scope (within a function)
    const clang::DeclContext* parentContext = cppVar->getDeclContext();
    bool isGlobalScope = llvm::isa<clang::TranslationUnitDecl>(parentContext);

    // Step 6: Create C variable
    // For global variables, use the TranslationUnitDecl
    // For local variables, we need to create them in the appropriate function context
    // Since we're building the C AST, we need to use the C context's TranslationUnitDecl
    // for global variables, but preserve the local context for local variables.
    //
    // For Phase 3 Task 6, we focus on global variables. Local variables
    // should be created in their appropriate function scope, but for now
    // we'll create all variables at the TranslationUnit scope and document
    // that local variable scope handling needs enhancement.

    clang::CNodeBuilder& builder = ctx.getBuilder();
    clang::ASTContext& cCtx = ctx.getCContext();

    // Create the variable declaration in the C AST
    // Note: builder.var() creates variables at TranslationUnitDecl by default
    // We'll use VarDecl::Create directly to have full control over the scope
    clang::IdentifierInfo& II = cCtx.Idents.get(name);

    // Use TranslationUnitDecl for global variables
    // For local variables, look up the translated parent function context
    clang::DeclContext* cDeclContext;
    if (isGlobalScope) {
        cDeclContext = cCtx.getTranslationUnitDecl();
    } else {
        // For local variables, find the C function they belong to
        // Walk up the declaration context chain to find the parent function
        const clang::Decl* parentDecl = llvm::dyn_cast<clang::Decl>(parentContext);
        if (parentDecl) {
            clang::Decl* translatedParent = ctx.lookupDecl(parentDecl);
            if (translatedParent && llvm::isa<clang::DeclContext>(translatedParent)) {
                cDeclContext = llvm::cast<clang::DeclContext>(translatedParent);
            } else {
                // Fallback to global scope if parent not found (shouldn't happen)
                cDeclContext = cCtx.getTranslationUnitDecl();
            }
        } else {
            // Fallback to global scope
            cDeclContext = cCtx.getTranslationUnitDecl();
        }
    }

    clang::VarDecl* cVar = clang::VarDecl::Create(
        cCtx,
        cDeclContext,
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        cType,
        cCtx.getTrivialTypeSourceInfo(cType),
        cStorageClass
    );

    // Set initializer if present
    if (cInitExpr) {
        cVar->setInit(cInitExpr);
    }

    // Step 7: Register mapping in context
    ctx.registerDecl(cppVar, cVar);

    return cVar;
}

clang::QualType VariableHandler::translateType(
    clang::QualType cppType,
    HandlerContext& ctx
) {
    clang::ASTContext& cCtx = ctx.getCContext();

    // Check for lvalue reference (T&)
    if (const auto* lvalRefType = llvm::dyn_cast<clang::LValueReferenceType>(cppType.getTypePtr())) {
        // Transform T& → T*
        clang::QualType pointeeType = lvalRefType->getPointeeType();
        return cCtx.getPointerType(pointeeType);
    }

    // Check for rvalue reference (T&&)
    if (const auto* rvalRefType = llvm::dyn_cast<clang::RValueReferenceType>(cppType.getTypePtr())) {
        // Transform T&& → T*
        // Note: C has no equivalent for move semantics, but we translate to pointer
        clang::QualType pointeeType = rvalRefType->getPointeeType();
        return cCtx.getPointerType(pointeeType);
    }

    // Preserve const qualifiers on top level (e.g., const T → const T)
    // For reference types, the const was already transferred to the pointee above
    // For non-reference types, pass through unchanged
    return cppType;
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

/**
 * @file VariableHandler.cpp
 * @brief Implementation of VariableHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle variable translation.
 * Translates C++ variables to C variables with type and initialization translation.
 */

#include "dispatch/VariableHandler.h"
#include "CNodeBuilder.h"
#include "mapping/DeclMapper.h"
#include "mapping/PathMapper.h"
#include "mapping/TypeMapper.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void VariableHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &VariableHandler::canHandle,
        &VariableHandler::handleVariable
    );
}

bool VariableHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Accept VarDecl but exclude FieldDecl (member variables)
    // FieldDecl is handled by RecordHandler
    if (D->getKind() == clang::Decl::Var) {
        // Double-check it's not a FieldDecl (which inherits from ValueDecl, not VarDecl)
        // Actually, FieldDecl has its own kind (Decl::Field), so this check is sufficient
        return true;
    }

    return false;
}

void VariableHandler::handleVariable(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::Var && "Must be VarDecl");

    const auto* cppVar = llvm::cast<clang::VarDecl>(D);

    // Check if already translated (avoid duplicates)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    if (declMapper.hasCreated(cppVar)) {
        llvm::outs() << "[VariableHandler] Already translated variable: "
                     << cppVar->getNameAsString() << " (skipping)\n";
        return;
    }

    // Extract variable properties
    std::string name = cppVar->getNameAsString();
    clang::QualType cppType = cppVar->getType();
    clang::StorageClass storageClass = cppVar->getStorageClass();

    llvm::outs() << "[VariableHandler] Translating variable: " << name
                 << " (type: " << cppType.getAsString() << ")\n";

    // Dispatch type via TypeHandler (handles reference → pointer conversion)
    // For reference types, TypeHandler will create pointer types
    // For other types, it passes through
    cpptoc::TypeMapper& typeMapper = disp.getTypeMapper();

    // Check if type is already translated
    clang::QualType cType;
    if (typeMapper.hasCreated(cppType.getTypePtr())) {
        cType = typeMapper.getCreated(cppType.getTypePtr());
        llvm::outs() << "[VariableHandler] Using cached translated type: "
                     << cType.getAsString() << "\n";
    } else {
        // Dispatch type to TypeHandler
        // TypeHandler will handle reference types (T& → T*, T&& → T*)
        const clang::Type* cppTypePtr = cppType.getTypePtr();

        // For reference types, dispatch to TypeHandler
        if (llvm::isa<clang::LValueReferenceType>(cppTypePtr) ||
            llvm::isa<clang::RValueReferenceType>(cppTypePtr)) {

            // TypeHandler should have been registered and will handle this
            // It will store the translated type in TypeMapper
            disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Type*>(cppTypePtr));

            // Retrieve translated type
            if (typeMapper.hasCreated(cppTypePtr)) {
                cType = typeMapper.getCreated(cppTypePtr);
                llvm::outs() << "[VariableHandler] Type translated by TypeHandler: "
                             << cppType.getAsString() << " → " << cType.getAsString() << "\n";
            } else {
                // TypeHandler didn't translate (shouldn't happen for reference types)
                llvm::errs() << "[VariableHandler] Warning: TypeHandler didn't translate reference type\n";
                cType = cppType;
            }
        } else {
            // For non-reference types, pass through unchanged
            cType = cppType;
            llvm::outs() << "[VariableHandler] Type passed through: " << cType.getAsString() << "\n";
        }
    }

    // Translate storage class
    clang::StorageClass cStorageClass = translateStorageClass(storageClass);

    // Translate initialization expression (if present)
    clang::Expr* cInitExpr = nullptr;
    if (cppVar->hasInit()) {
        cInitExpr = translateInitializer(cppVar->getInit(), cASTContext);
        if (cInitExpr) {
            llvm::outs() << "[VariableHandler] Translated initializer\n";
        } else {
            llvm::outs() << "[VariableHandler] No initializer translation (complex expression)\n";
        }
    }

    // Determine scope (global vs local)
    const clang::DeclContext* parentContext = cppVar->getDeclContext();
    bool isGlobalScope = llvm::isa<clang::TranslationUnitDecl>(parentContext);

    // Determine target DeclContext
    clang::DeclContext* cDeclContext;
    if (isGlobalScope) {
        cDeclContext = cASTContext.getTranslationUnitDecl();
        llvm::outs() << "[VariableHandler] Global scope variable\n";
    } else {
        // For local variables, find the translated parent function
        // DeclContext might be null or might not be a Decl, so use dyn_cast_or_null
        const clang::Decl* parentDecl = llvm::dyn_cast_or_null<clang::Decl>(parentContext);
        if (parentDecl && declMapper.hasCreated(parentDecl)) {
            clang::Decl* translatedParent = declMapper.getCreated(parentDecl);
            if (translatedParent && llvm::isa<clang::DeclContext>(translatedParent)) {
                cDeclContext = llvm::cast<clang::DeclContext>(translatedParent);
                llvm::outs() << "[VariableHandler] Local scope variable (parent found)\n";
            } else {
                // Fallback to global scope
                cDeclContext = cASTContext.getTranslationUnitDecl();
                llvm::outs() << "[VariableHandler] Warning: Parent not a DeclContext, using global scope\n";
            }
        } else {
            // Fallback to global scope
            cDeclContext = cASTContext.getTranslationUnitDecl();
            llvm::outs() << "[VariableHandler] Warning: Parent not translated, using global scope\n";
        }
    }

    // Create identifier for variable name
    clang::IdentifierInfo& II = cASTContext.Idents.get(name);

    // Create C variable
    clang::VarDecl* cVar = clang::VarDecl::Create(
        cASTContext,
        cDeclContext,
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        cType,
        cASTContext.getTrivialTypeSourceInfo(cType),
        cStorageClass
    );

    assert(cVar && "Failed to create C VarDecl");

    // Set initializer if present
    if (cInitExpr) {
        cVar->setInit(cInitExpr);
    }

    // IMPORTANT: For global variables, add to TU. For local variables, DON'T add to DeclContext
    // Local variables are owned by the DeclStmt, not the function's decl list
    if (isGlobalScope) {
        cDeclContext->addDecl(cVar);
        llvm::outs() << "[VariableHandler] Added global variable to TU\n";
    } else {
        // Local variable - don't add to function's decl list (it's in the DeclStmt)
        llvm::outs() << "[VariableHandler] Local variable - not added to function decl list\n";
    }

    // Store mapping
    declMapper.setCreated(cppVar, cVar);

    // Get target path and register location
    std::string targetPath = disp.getTargetPath(cppASTContext, D);
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    pathMapper.setNodeLocation(cVar, targetPath);

    llvm::outs() << "[VariableHandler] Created C variable: " << name
                 << " (type: " << cType.getAsString() << ")\n";
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

        case clang::SC_PrivateExtern:
            // PrivateExtern is Apple-specific, treat as static
            return clang::SC_Static;

        default:
            // Unknown storage class, use None as fallback
            return clang::SC_None;
    }
}

clang::Expr* VariableHandler::translateInitializer(
    const clang::Expr* init,
    clang::ASTContext& cASTContext
) {
    if (!init) {
        return nullptr;
    }

    // For Phase 1, handle literal expressions only
    // Create equivalent literals in C ASTContext

    if (const auto* intLit = llvm::dyn_cast<clang::IntegerLiteral>(init)) {
        // Create new IntegerLiteral in C context
        return clang::IntegerLiteral::Create(
            cASTContext,
            intLit->getValue(),
            intLit->getType(),
            clang::SourceLocation()
        );
    }

    if (const auto* floatLit = llvm::dyn_cast<clang::FloatingLiteral>(init)) {
        // Create new FloatingLiteral in C context
        return clang::FloatingLiteral::Create(
            cASTContext,
            floatLit->getValue(),
            floatLit->isExact(),
            floatLit->getType(),
            clang::SourceLocation()
        );
    }

    if (const auto* charLit = llvm::dyn_cast<clang::CharacterLiteral>(init)) {
        // Create new CharacterLiteral in C context
        return new (cASTContext) clang::CharacterLiteral(
            charLit->getValue(),
            charLit->getKind(),
            charLit->getType(),
            clang::SourceLocation()
        );
    }

    if (const auto* strLit = llvm::dyn_cast<clang::StringLiteral>(init)) {
        // Create new StringLiteral in C context
        return clang::StringLiteral::Create(
            cASTContext,
            strLit->getString(),
            strLit->getKind(),
            strLit->isPascal(),
            strLit->getType(),
            clang::SourceLocation()
        );
    }

    // For other expression types, we'll add support as needed
    // For now, return nullptr (no initialization)
    // Phase 2 will delegate to ExpressionHandler for complex expressions
    return nullptr;
}

} // namespace cpptoc

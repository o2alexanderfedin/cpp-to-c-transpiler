/**
 * @file VariableHandler.cpp
 * @brief Implementation of VariableHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle variable translation.
 * Translates C++ variables to C variables with type and initialization translation.
 */

#include "dispatch/VariableHandler.h"
#include "dispatch/TypeHandler.h"
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

    // Determine scope EARLY (we need this to decide on name mangling)
    const clang::DeclContext* parentContext = cppVar->getDeclContext();
    bool isGlobalScope = llvm::isa<clang::TranslationUnitDecl>(parentContext);
    bool isStaticLocal = !isGlobalScope && (storageClass == clang::SC_Static);

    llvm::outs() << "[VariableHandler] Translating variable: " << name
                 << " (type: " << cppType.getAsString()
                 << ", isGlobal: " << isGlobalScope
                 << ", isStaticLocal: " << isStaticLocal << ")\n";

    // Translate type via TypeHandler (handles all type conversions including reference → pointer)
    clang::QualType cType = TypeHandler::translateType(cppType, cppASTContext, cASTContext);

    llvm::outs() << "[VariableHandler] Translated variable type: "
                 << cppType.getAsString() << " → " << cType.getAsString() << "\n";

    // Mangle name for static local variables
    // Static locals need unique names when hoisted to global scope
    // Format: functionName__varName
    std::string mangledName = name;
    if (isStaticLocal) {
        // Find the enclosing function
        const clang::FunctionDecl* enclosingFunc = nullptr;
        const clang::DeclContext* ctx = parentContext;
        while (ctx && !enclosingFunc) {
            enclosingFunc = llvm::dyn_cast<clang::FunctionDecl>(ctx);
            ctx = ctx->getParent();
        }

        if (enclosingFunc) {
            mangledName = enclosingFunc->getNameAsString() + "__" + name;
            llvm::outs() << "[VariableHandler] Static local variable mangled: "
                         << name << " → " << mangledName << "\n";
        } else {
            llvm::errs() << "[VariableHandler] Warning: Could not find enclosing function for static local\n";
        }
    }

    // Translate storage class
    clang::StorageClass cStorageClass = translateStorageClass(storageClass);

    // Translate initialization expression (if present)
    clang::Expr* cInitExpr = nullptr;
    if (cppVar->hasInit()) {
        const clang::Expr* cppInit = cppVar->getInit();

        // Dispatch the initializer expression through the dispatcher
        // This allows complex expressions (like a+b) to be properly translated
        bool initHandled = disp.dispatch(cppASTContext, cASTContext, cppInit);

        if (initHandled) {
            // Retrieve translated expression from ExprMapper
            cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
            cInitExpr = exprMapper.getCreated(cppInit);

            if (cInitExpr) {
                llvm::outs() << "[VariableHandler] Initializer translated via dispatcher\n";
            } else {
                llvm::errs() << "[VariableHandler] Warning: Initializer dispatched but not in ExprMapper\n";
            }
        } else {
            llvm::outs() << "[VariableHandler] Initializer not handled by dispatcher\n";
        }
    }

    // Get target path early - needed for both DeclContext and location registration
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, D);
    }
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();

    // Determine target DeclContext
    // CRITICAL: Static local variables MUST be hoisted to global scope
    // They retain their value between function calls, so they act like globals
    clang::DeclContext* cDeclContext;
    if (isGlobalScope || isStaticLocal) {
        // CRITICAL FIX: For global variables, use PathMapper to get the correct C TU
        // Don't use cASTContext.getTranslationUnitDecl() - that's the root TU, not the per-file TU!
        // This matches the pattern used by FunctionHandler, MethodHandler, etc.
        cDeclContext = pathMapper.getOrCreateTU(targetPath);
        if (isStaticLocal) {
            llvm::outs() << "[VariableHandler] Static local variable hoisted to global scope (PathMapper TU for: "
                         << targetPath << ")\n";
        } else {
            llvm::outs() << "[VariableHandler] Global scope variable (using PathMapper TU for: "
                         << targetPath << ")\n";
        }
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
                // Fallback to global scope - use PathMapper here too
                cDeclContext = pathMapper.getOrCreateTU(targetPath);
                llvm::outs() << "[VariableHandler] Warning: Parent not a DeclContext, using PathMapper TU\n";
            }
        } else {
            // Fallback to global scope - use PathMapper here too
            cDeclContext = pathMapper.getOrCreateTU(targetPath);
            llvm::outs() << "[VariableHandler] Warning: Parent not translated, using PathMapper TU\n";
        }
    }

    // Create identifier for variable name (use mangled name for static locals)
    clang::IdentifierInfo& II = cASTContext.Idents.get(mangledName);

    // Get valid SourceLocation for C AST node
    clang::SourceLocation targetLoc = disp.getTargetSourceLocation(cppASTContext, D);

    // Create C variable
    clang::VarDecl* cVar = clang::VarDecl::Create(
        cASTContext,
        cDeclContext,
        targetLoc,
        targetLoc,
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

    // IMPORTANT: For global variables and static locals, add to TU.
    // For regular local variables, DON'T add to DeclContext - they're owned by the DeclStmt
    if (isGlobalScope || isStaticLocal) {
        cDeclContext->addDecl(cVar);
        if (isStaticLocal) {
            llvm::outs() << "[VariableHandler] Added static local variable to TU (hoisted to global)\n";
        } else {
            llvm::outs() << "[VariableHandler] Added global variable to TU\n";
        }
    } else {
        // Regular local variable - don't add to function's decl list (it's in the DeclStmt)
        llvm::outs() << "[VariableHandler] Local variable - not added to function decl list\n";
    }

    // Store mapping
    declMapper.setCreated(cppVar, cVar);

    // Register location (targetPath and pathMapper already retrieved earlier)
    pathMapper.setNodeLocation(cVar, targetPath);

    llvm::outs() << "[VariableHandler] Created C variable: " << mangledName
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
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    if (!init) {
        return nullptr;
    }

    // For Phase 1, handle literal expressions only
    // Create equivalent literals in C ASTContext

    if (const auto* intLit = llvm::dyn_cast<clang::IntegerLiteral>(init)) {
        // Create new IntegerLiteral in C context
        // IMPORTANT: Use C ASTContext's int type, not C++ type
        return clang::IntegerLiteral::Create(
            cASTContext,
            intLit->getValue(),
            cASTContext.IntTy,  // Get int type from C context
            targetLoc
        );
    }

    if (const auto* floatLit = llvm::dyn_cast<clang::FloatingLiteral>(init)) {
        // Create new FloatingLiteral in C context
        // IMPORTANT: Use C ASTContext's float/double type
        // Determine if it's float or double based on the semantics
        clang::QualType cFloatType = cASTContext.DoubleTy;  // Default to double
        if (floatLit->getType()->getAs<clang::BuiltinType>()) {
            const auto* builtinType = floatLit->getType()->getAs<clang::BuiltinType>();
            if (builtinType->getKind() == clang::BuiltinType::Float) {
                cFloatType = cASTContext.FloatTy;
            }
        }
        return clang::FloatingLiteral::Create(
            cASTContext,
            floatLit->getValue(),
            floatLit->isExact(),
            cFloatType,
            targetLoc
        );
    }

    if (const auto* charLit = llvm::dyn_cast<clang::CharacterLiteral>(init)) {
        // Create new CharacterLiteral in C context
        // IMPORTANT: Use C ASTContext's char type
        return new (cASTContext) clang::CharacterLiteral(
            charLit->getValue(),
            charLit->getKind(),
            cASTContext.CharTy,  // Get char type from C context
            targetLoc
        );
    }

    if (const auto* strLit = llvm::dyn_cast<clang::StringLiteral>(init)) {
        // Create new StringLiteral in C context
        // IMPORTANT: Use C ASTContext's string type
        // For string literals, we need to create array type based on string length
        unsigned length = strLit->getLength();
        clang::QualType charType = cASTContext.CharTy;
        clang::QualType arrayType = cASTContext.getConstantArrayType(
            charType,
            llvm::APInt(32, length + 1),  // +1 for null terminator
            nullptr,
            clang::ArraySizeModifier::Normal,
            0
        );
        return clang::StringLiteral::Create(
            cASTContext,
            strLit->getString(),
            strLit->getKind(),
            strLit->isPascal(),
            arrayType,
            targetLoc
        );
    }

    // For other expression types, we'll add support as needed
    // For now, return nullptr (no initialization)
    // Phase 2 will delegate to ExpressionHandler for complex expressions
    return nullptr;
}

} // namespace cpptoc

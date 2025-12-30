/**
 * @file StaticMethodHandler.cpp
 * @brief Implementation of StaticMethodHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle static method translation.
 * Translates C++ static methods to C free functions with class name prefixing.
 *
 * Phase 3: OverloadRegistry Integration
 * - Uses NameMangler for all name mangling (replaces custom getMangledName)
 * - Ensures deterministic cross-file naming via OverloadRegistry
 */

#include "dispatch/StaticMethodHandler.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include "OverloadRegistry.h"
#include "mapping/DeclMapper.h"
#include "mapping/StmtMapper.h"
#include "mapping/TypeMapper.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void StaticMethodHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &StaticMethodHandler::canHandle,
        &StaticMethodHandler::handleStaticMethod
    );
}

bool StaticMethodHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // CRITICAL: Must use exact type checking (getKind), NOT isa<>
    // We want CXXMethodDecl, but ONLY static methods
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    // Cast to CXXMethodDecl to check if static
    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);

    // Exclude constructors and destructors (they have dedicated handlers)
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // Accept ONLY static methods
    return method->isStatic();
}

void StaticMethodHandler::handleStaticMethod(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::CXXMethod && "Must be CXXMethodDecl");

    const auto* cppMethod = llvm::cast<clang::CXXMethodDecl>(D);

    // Additional safety check: Must be static
    if (!cppMethod->isStatic()) {
        llvm::errs() << "StaticMethodHandler: Unexpected non-static method - should be filtered by canHandle\n";
        return;
    }

    // Get parent class
    const clang::CXXRecordDecl* classDecl = cppMethod->getParent();
    assert(classDecl && "Static method must have parent class");

    // Phase 3: Use NameMangler with OverloadRegistry for deterministic naming
    // Static methods are treated as standalone functions (no 'this' parameter)
    // NameMangler handles: namespace prefix, class prefix, overload resolution
    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    NameMangler mangler(const_cast<clang::ASTContext&>(cppASTContext), registry);
    std::string mangledName = mangler.mangleStandaloneFunction(const_cast<clang::CXXMethodDecl*>(cppMethod));

    // Extract method properties
    clang::QualType cppReturnType = cppMethod->getReturnType();

    // Translate return type via TypeHandler (convert references to pointers)
    // Dispatch the return type to TypeHandler, which stores mapping in TypeMapper
    const clang::Type* cppReturnTypePtr = cppReturnType.getTypePtr();
    bool typeHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Type*>(cppReturnTypePtr));

    // Retrieve translated type from TypeMapper
    cpptoc::TypeMapper& typeMapper = disp.getTypeMapper();
    clang::QualType cReturnType = typeMapper.getCreated(cppReturnTypePtr);

    // If TypeHandler didn't handle this type (pass-through), use original type
    if (cReturnType.isNull()) {
        cReturnType = cppReturnType;
        llvm::outs() << "[StaticMethodHandler] TypeHandler pass-through for return type: "
                     << cppReturnType.getAsString() << "\n";
    }

    // Translate parameters by dispatching to ParameterHandler
    // NO "this" parameter for static methods (they are free functions)
    std::vector<clang::ParmVarDecl*> cParams = translateParameters(cppMethod, disp, cppASTContext, cASTContext);

    // Translate function body (if exists) via CompoundStmtHandler
    clang::CompoundStmt* cBody = nullptr;
    if (cppMethod->hasBody()) {
        const clang::Stmt* cppBody = cppMethod->getBody();
        if (cppBody) {
            // Dispatch body to CompoundStmtHandler
            bool bodyHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));
            if (bodyHandled) {
                // Retrieve created C body from StmtMapper
                cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
                clang::Stmt* cStmt = stmtMapper.getCreated(cppBody);

                if (cStmt) {
                    // Ensure it's a CompoundStmt as expected for function bodies
                    cBody = llvm::dyn_cast<clang::CompoundStmt>(cStmt);
                    if (cBody) {
                        llvm::outs() << "[StaticMethodHandler] Body dispatched and retrieved successfully "
                                     << "(" << cBody->size() << " statements)\n";
                    } else {
                        llvm::errs() << "[StaticMethodHandler] Error: Retrieved statement is not CompoundStmt for static method: "
                                     << mangledName << "\n";
                    }
                } else {
                    llvm::errs() << "[StaticMethodHandler] Warning: CompoundStmtHandler did not create C body for static method: "
                                 << mangledName << "\n";
                }
            }
        }
    }

    // Create C function using CNodeBuilder
    // CNodeBuilder will set the body on the function if cBody is not nullptr
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(
        mangledName,
        cReturnType,
        cParams,
        cBody  // Body is nullptr if not translated, or CompoundStmt if successfully translated
    );

    assert(cFunc && "Failed to create C FunctionDecl");

    // Verify body was properly attached
    if (cBody) {
        assert(cFunc->hasBody() && "Function should have body after creation");
        assert(cFunc->getBody() == cBody && "Function body should match provided body");
        llvm::outs() << "[StaticMethodHandler] Function body successfully attached to: " << mangledName << "\n";
    }

    // Get target path for this C++ source file
    std::string targetPath = disp.getTargetPath(cppASTContext, D);

    // Get or create C TranslationUnit for this target file
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);
    assert(cTU && "Failed to get/create C TranslationUnit");

    // Add C function to C TranslationUnit
    cFunc->setDeclContext(cTU);
    cTU->addDecl(cFunc);

    // Register node location in PathMapper for tracking
    pathMapper.setNodeLocation(cFunc, targetPath);

    // Store declaration mapping in DeclMapper
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    declMapper.setCreated(cppMethod, cFunc);

    // Debug output for verification
    llvm::outs() << "[StaticMethodHandler] Translated static method: "
                 << classDecl->getNameAsString() << "::" << cppMethod->getNameAsString()
                 << " → " << mangledName << " → " << targetPath << "\n";
}

// Phase 3: Removed custom getMangledName() - now uses NameMangler::mangleStandaloneFunction()
// This ensures deterministic naming via OverloadRegistry across all translation units

std::vector<clang::ParmVarDecl*> StaticMethodHandler::translateParameters(
    const clang::CXXMethodDecl* method,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    std::vector<clang::ParmVarDecl*> cParams;

    // Dispatch each parameter to ParameterHandler
    // Following Chain of Responsibility pattern: Let child handler translate children
    // NO "this" parameter for static methods (they are free functions)
    for (const auto* cppParam : method->parameters()) {
        // Cast away const for dispatch (dispatcher interface requires non-const)
        clang::ParmVarDecl* cppParamNonConst = const_cast<clang::ParmVarDecl*>(cppParam);

        // Dispatch parameter to ParameterHandler
        // ParameterHandler will create C parameter and store mapping in DeclMapper
        bool handled = disp.dispatch(cppASTContext, cASTContext, cppParamNonConst);

        if (!handled) {
            llvm::errs() << "[StaticMethodHandler] Error: No handler for parameter: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        // Retrieve created C parameter from DeclMapper
        cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
        clang::Decl* cDecl = declMapper.getCreated(cppParam);

        if (!cDecl) {
            llvm::errs() << "[StaticMethodHandler] Error: ParameterHandler did not create C parameter for: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        // Cast to ParmVarDecl (we know ParameterHandler creates ParmVarDecl)
        clang::ParmVarDecl* cParam = llvm::cast<clang::ParmVarDecl>(cDecl);
        cParams.push_back(cParam);
    }

    return cParams;
}

} // namespace cpptoc

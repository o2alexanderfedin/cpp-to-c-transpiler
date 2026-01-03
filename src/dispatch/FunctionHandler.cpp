/**
 * @file FunctionHandler.cpp
 * @brief Implementation of FunctionHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle free function translation.
 * Translates C++ function signatures and bodies to C equivalents.
 * Retrieves translated function bodies from StmtMapper via CompoundStmtHandler.
 */

#include "dispatch/FunctionHandler.h"
#include "dispatch/NamespaceHandler.h"
#include "CNodeBuilder.h"
#include "mapping/DeclMapper.h"
#include "mapping/StmtMapper.h"
#include "mapping/TypeMapper.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void FunctionHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &FunctionHandler::canHandle,
        &FunctionHandler::handleFunction
    );
}

bool FunctionHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // CRITICAL: Must use exact type checking (getKind), NOT isa<>
    // isa<> would match CXXMethodDecl (which is derived from FunctionDecl)
    // We ONLY want free functions, NOT methods
    if (D->getKind() != clang::Decl::Function) {
        return false;
    }

    // Double-check: Ensure this is not a method
    // This should never trigger if getKind() check is correct, but provides safety
    const auto* FD = llvm::cast<clang::FunctionDecl>(D);
    return !llvm::isa<clang::CXXMethodDecl>(FD);
}

void FunctionHandler::handleFunction(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::Function && "Must be FunctionDecl");

    const auto* cppFunc = llvm::cast<clang::FunctionDecl>(D);

    // Additional safety check: Exclude methods
    if (llvm::isa<clang::CXXMethodDecl>(cppFunc)) {
        llvm::errs() << "FunctionHandler: Unexpected CXXMethodDecl - should be filtered by canHandle\n";
        return;
    }

    // Extract function properties
    std::string name = cppFunc->getNameAsString();

    // Check if function is in a namespace and apply namespace prefix
    if (const auto* nsDecl = llvm::dyn_cast<clang::NamespaceDecl>(cppFunc->getDeclContext())) {
        std::string nsPrefix = cpptoc::NamespaceHandler::getNamespacePath(nsDecl);
        if (!nsPrefix.empty()) {
            name = nsPrefix + "_" + name;
            llvm::outs() << "[FunctionHandler] Applied namespace prefix: "
                         << cppFunc->getNameAsString() << " → " << name << "\n";
        }
    }

    clang::QualType cppReturnType = cppFunc->getReturnType();

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
        llvm::outs() << "[FunctionHandler] TypeHandler pass-through for return type: "
                     << cppReturnType.getAsString() << "\n";
    }

    // Translate parameters by dispatching to ParameterHandler
    std::vector<clang::ParmVarDecl*> cParams = translateParameters(cppFunc, disp, cppASTContext, cASTContext);

    // Create C function FIRST (without body) so local variables can find it as parent
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(
        name,
        cReturnType,
        cParams,
        nullptr  // Body will be set later
    );

    assert(cFunc && "Failed to create C FunctionDecl");

    // Store in DeclMapper BEFORE translating body (so local variables can find parent)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    declMapper.setCreated(cppFunc, cFunc);
    llvm::outs() << "[FunctionHandler] Created C function and stored in DeclMapper: " << name << "\n";

    // NOW translate function body (if exists) via CompoundStmtHandler
    // Local variables will be able to find this function as their parent
    clang::CompoundStmt* cBody = nullptr;
    if (cppFunc->hasBody()) {
        const clang::Stmt* cppBody = cppFunc->getBody();
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
                        llvm::outs() << "[FunctionHandler] Body dispatched and retrieved successfully "
                                     << "(" << cBody->size() << " statements)\n";
                    } else {
                        llvm::errs() << "[FunctionHandler] Error: Retrieved statement is not CompoundStmt for function: "
                                     << name << "\n";
                    }
                } else {
                    llvm::errs() << "[FunctionHandler] Warning: CompoundStmtHandler did not create C body for function: "
                                 << name << "\n";
                }
            }
        }
    }

    // Set the body on the function if it was translated
    if (cBody) {
        cFunc->setBody(cBody);
        assert(cFunc->hasBody() && "Function should have body after setBody");
        assert(cFunc->getBody() == cBody && "Function body should match provided body");
        llvm::outs() << "[FunctionHandler] Function body successfully attached to: " << name << "\n";
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

    // Debug output for verification
    llvm::outs() << "[FunctionHandler] Translated function: " << name
                 << " → " << targetPath << "\n";
}

std::vector<clang::ParmVarDecl*> FunctionHandler::translateParameters(
    const clang::FunctionDecl* cppFunc,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    std::vector<clang::ParmVarDecl*> cParams;

    // Dispatch each parameter to ParameterHandler
    // Following Chain of Responsibility pattern: Let child handler translate children
    for (const auto* cppParam : cppFunc->parameters()) {
        // Cast away const for dispatch (dispatcher interface requires non-const)
        clang::ParmVarDecl* cppParamNonConst = const_cast<clang::ParmVarDecl*>(cppParam);

        // Dispatch parameter to ParameterHandler
        // ParameterHandler will create C parameter and store mapping in PathMapper
        bool handled = disp.dispatch(cppASTContext, cASTContext, cppParamNonConst);

        if (!handled) {
            llvm::errs() << "[FunctionHandler] Error: No handler for parameter: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        // Retrieve created C parameter from DeclMapper
        cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
        clang::Decl* cDecl = declMapper.getCreated(cppParam);

        if (!cDecl) {
            llvm::errs() << "[FunctionHandler] Error: ParameterHandler did not create C parameter for: "
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

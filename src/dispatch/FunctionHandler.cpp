/**
 * @file FunctionHandler.cpp
 * @brief Implementation of FunctionHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle free function translation.
 * Phase 1 implementation: Signature translation only (no function bodies).
 */

#include "dispatch/FunctionHandler.h"
#include "CNodeBuilder.h"
#include "mapping/DeclMapper.h"
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
    clang::QualType cppReturnType = cppFunc->getReturnType();

    // Translate return type via TypeHandler (convert references to pointers)
    // Dispatch the return type to TypeHandler, which stores mapping in TypeMapper
    const clang::Type* cppReturnTypePtr = cppReturnType.getTypePtr();
    bool typeHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Type*>(cppReturnTypePtr));

    // Retrieve translated type from TypeMapper
    cpptoc::TypeMapper& typeMapper = disp.getTypeMapper();
    clang::QualType cReturnType = typeMapper.getCreatedType(cppReturnTypePtr);

    // If TypeHandler didn't handle this type (pass-through), use original type
    if (cReturnType.isNull()) {
        cReturnType = cppReturnType;
        llvm::outs() << "[FunctionHandler] TypeHandler pass-through for return type: "
                     << cppReturnType.getAsString() << "\n";
    }

    // Translate parameters by dispatching to ParameterHandler
    std::vector<clang::ParmVarDecl*> cParams = translateParameters(cppFunc, disp, cppASTContext, cASTContext);

    // Create C function using CNodeBuilder
    // PHASE 1 LIMITATION: Body is nullptr (no statement translation yet)
    // Body translation will be added in future phase with StatementHandler
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(
        name,
        cReturnType,
        cParams,
        nullptr  // Phase 1: No body translation - explicitly nullptr
    );

    assert(cFunc && "Failed to create C FunctionDecl");

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
        clang::Decl* cDecl = declMapper.getCreatedDecl(cppParam);

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

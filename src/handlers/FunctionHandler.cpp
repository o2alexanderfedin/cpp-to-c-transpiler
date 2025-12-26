/**
 * @file FunctionHandler.cpp
 * @brief Implementation of FunctionHandler
 *
 * TDD Implementation: Start minimal, add complexity as tests demand.
 */

#include "handlers/FunctionHandler.h"
#include "handlers/HandlerContext.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

bool FunctionHandler::canHandle(const clang::Decl* D) const {
    // Only handle FunctionDecl, not methods (CXXMethodDecl is subclass of FunctionDecl)
    if (const auto* FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
        // Exclude methods
        return !llvm::isa<clang::CXXMethodDecl>(FD);
    }
    return false;
}

clang::Decl* FunctionHandler::handleDecl(const clang::Decl* D, HandlerContext& ctx) {
    const auto* cppFunc = llvm::cast<clang::FunctionDecl>(D);

    // Get function properties
    std::string name = cppFunc->getNameAsString();
    clang::QualType returnType = cppFunc->getReturnType();

    // Translate parameters
    std::vector<clang::ParmVarDecl*> cParams = translateParameters(cppFunc, ctx);

    // Create C function using CNodeBuilder
    clang::CNodeBuilder& builder = ctx.getBuilder();
    clang::FunctionDecl* cFunc = builder.funcDecl(
        name,
        returnType,  // For now, pass through return type
        cParams,
        nullptr      // No body yet
    );

    // Register mapping
    ctx.registerDecl(cppFunc, cFunc);

    return cFunc;
}

std::vector<clang::ParmVarDecl*> FunctionHandler::translateParameters(
    const clang::FunctionDecl* cppFunc,
    HandlerContext& ctx
) {
    std::vector<clang::ParmVarDecl*> cParams;
    clang::ASTContext& cContext = ctx.getCContext();

    // Translate each parameter
    for (const auto* cppParam : cppFunc->parameters()) {
        // Create identifier for parameter name
        clang::IdentifierInfo& II = cContext.Idents.get(cppParam->getNameAsString());

        // Create C parameter with same name and type
        clang::ParmVarDecl* cParam = clang::ParmVarDecl::Create(
            cContext,
            cContext.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II,
            cppParam->getType(),
            cContext.getTrivialTypeSourceInfo(cppParam->getType()),
            clang::SC_None,
            nullptr  // No default argument
        );

        cParams.push_back(cParam);

        // Register parameter mapping for later reference
        ctx.registerDecl(cppParam, cParam);
    }

    return cParams;
}

} // namespace cpptoc

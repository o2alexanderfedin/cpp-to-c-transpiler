/**
 * @file DestructorHandler.cpp
 * @brief Implementation of DestructorHandler
 *
 * TDD Implementation: Start minimal, add complexity as tests demand.
 */

#include "handlers/DestructorHandler.h"
#include "handlers/HandlerContext.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

bool DestructorHandler::canHandle(const clang::Decl* D) const {
    // Check if this is a CXXDestructorDecl
    return llvm::isa<clang::CXXDestructorDecl>(D);
}

clang::Decl* DestructorHandler::handleDecl(const clang::Decl* D, HandlerContext& ctx) {
    const auto* cppDestructor = llvm::cast<clang::CXXDestructorDecl>(D);

    // Get parent class
    const auto* cxxRecord = cppDestructor->getParent();
    std::string className = cxxRecord->getNameAsString();

    // Create function name: ClassName_destroy
    std::string functionName = className + "_destroy";

    // Return type is always void
    clang::ASTContext& cContext = ctx.getCContext();
    clang::QualType voidType = cContext.VoidTy;

    // Create this parameter: struct ClassName* this
    clang::QualType classType = cContext.getRecordType(cxxRecord);
    clang::ParmVarDecl* thisParam = createThisParameter(classType, ctx);

    // Create parameters vector with just this parameter
    std::vector<clang::ParmVarDecl*> params = { thisParam };

    // Create C function using CNodeBuilder
    clang::CNodeBuilder& builder = ctx.getBuilder();
    clang::FunctionDecl* cFunc = builder.funcDecl(
        functionName,
        voidType,
        params,
        nullptr  // Body will be translated separately by StatementHandler
    );

    // Register mapping
    ctx.registerDecl(cppDestructor, cFunc);

    // Register this parameter for body translation
    // When body is translated, references to 'this' will map to thisParam
    // Note: This requires HandlerContext to support implicit this parameter
    // For now, we rely on ExpressionHandler to handle CXXThisExpr

    return cFunc;
}

clang::ParmVarDecl* DestructorHandler::createThisParameter(
    clang::QualType classType,
    HandlerContext& ctx
) {
    clang::ASTContext& cContext = ctx.getCContext();

    // Create pointer type: struct ClassName*
    clang::QualType thisType = cContext.getPointerType(classType);

    // Create identifier for parameter name
    clang::IdentifierInfo& II = cContext.Idents.get("this");

    // Create parameter declaration
    clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
        cContext,
        cContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        thisType,
        cContext.getTrivialTypeSourceInfo(thisType),
        clang::SC_None,
        nullptr  // No default argument
    );

    return thisParam;
}

} // namespace cpptoc

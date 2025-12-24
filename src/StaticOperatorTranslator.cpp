/**
 * @file StaticOperatorTranslator.cpp
 * @brief Implementation of StaticOperatorTranslator
 *
 * Phase 2: Static operator() and operator[] translation for C++23 support.
 * Follows the proven translator pattern established by MultidimSubscriptTranslator
 * and TemplateExtractor.
 */

#include "../include/StaticOperatorTranslator.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include <sstream>

using namespace clang;

StaticOperatorTranslator::StaticOperatorTranslator(CNodeBuilder& Builder)
    : m_builder(Builder) {}

FunctionDecl* StaticOperatorTranslator::transformMethod(CXXMethodDecl* MD,
                                                         ASTContext& Ctx,
                                                         TranslationUnitDecl* C_TU) {
    if (!MD || !C_TU) {
        return nullptr;
    }

    // Only handle static operators
    if (!MD->isStatic()) {
        return nullptr;
    }

    // Only handle operator() and operator[]
    if (!MD->isOverloadedOperator()) {
        return nullptr;
    }

    auto Op = MD->getOverloadedOperator();
    if (Op != OO_Call && Op != OO_Subscript) {
        return nullptr;
    }

    // Get or create the C function
    return findOrCreateStaticFunction(MD, Ctx, C_TU);
}

CallExpr* StaticOperatorTranslator::transformCall(CXXOperatorCallExpr* E,
                                                   ASTContext& Ctx) {
    if (!E) {
        return nullptr;
    }

    // Get the method declaration
    const CXXMethodDecl* Method = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl());
    if (!Method) {
        return nullptr;
    }

    // Only handle static operators
    if (!Method->isStatic()) {
        return nullptr;
    }

    // Only handle operator() and operator[]
    auto Op = E->getOperator();
    if (Op != OO_Call && Op != OO_Subscript) {
        return nullptr;
    }

    // Build argument list for C function call
    // For static operators, arg[0] is the object (e.g., Calculator{}) which is unused
    // Arguments start from index 1
    llvm::SmallVector<Expr*, 4> args;
    for (unsigned i = 1; i < E->getNumArgs(); ++i) {
        args.push_back(E->getArg(i));
    }

    // Get the function name
    std::string funcName = generateStaticOperatorName(Method);

    // Create function reference
    // Note: In a full implementation, we would look up the FunctionDecl from C_TU
    // For now, we create a simplified CallExpr
    IdentifierInfo& II = Ctx.Idents.get(funcName);
    DeclarationName DN(&II);

    // Build parameter types
    llvm::SmallVector<QualType, 4> paramTypes;
    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        paramTypes.push_back(Method->getParamDecl(i)->getType());
    }

    // Create function type
    FunctionProtoType::ExtProtoInfo EPI;
    QualType funcType = Ctx.getFunctionType(Method->getReturnType(), paramTypes, EPI);

    // Create function declaration
    FunctionDecl* FD = FunctionDecl::Create(
        Ctx, Ctx.getTranslationUnitDecl(),
        SourceLocation(), SourceLocation(),
        DN, funcType, Ctx.getTrivialTypeSourceInfo(funcType), SC_None);

    // Create function reference
    DeclRefExpr* funcRef = DeclRefExpr::Create(
        Ctx, NestedNameSpecifierLoc(), SourceLocation(),
        FD, false, SourceLocation(), funcType, VK_LValue);

    // Create call expression
    CallExpr* callExpr = CallExpr::Create(
        Ctx, funcRef, args, Method->getReturnType(),
        VK_PRValue, SourceLocation(), FPOptionsOverride());

    return callExpr;
}

std::string StaticOperatorTranslator::generateStaticOperatorName(const CXXMethodDecl* MD) {
    if (!MD) {
        return "";
    }

    const CXXRecordDecl* Class = MD->getParent();
    if (!Class) {
        return "";
    }

    std::ostringstream oss;
    oss << Class->getNameAsString();

    auto Op = MD->getOverloadedOperator();
    if (Op == OO_Call) {
        oss << "__call_static";
    } else if (Op == OO_Subscript) {
        unsigned numParams = MD->getNumParams();

        if (numParams == 1) {
            // Single-dimensional subscript
            oss << "__subscript_static";
        } else {
            // Multidimensional subscript (combines with Phase 1)
            oss << "__subscript_" << numParams << "d_static";
        }
    }

    return oss.str();
}

FunctionDecl* StaticOperatorTranslator::findOrCreateStaticFunction(
    const CXXMethodDecl* MD,
    ASTContext& Ctx,
    TranslationUnitDecl* C_TU) {

    if (!MD || !C_TU) {
        return nullptr;
    }

    const CXXRecordDecl* Class = MD->getParent();
    if (!Class) {
        return nullptr;
    }

    // Generate function name
    std::string funcName = generateStaticOperatorName(MD);
    if (funcName.empty()) {
        return nullptr;
    }

    // Check if function already exists in C_TU
    for (auto* D : C_TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == funcName) {
                return FD; // Already exists
            }
        }
    }

    // Create new function declaration
    // Signature: ReturnType ClassName__op_static(Type1 arg1, Type2 arg2, ...)
    // Note: NO 'this' parameter for static operators

    IdentifierInfo& II = Ctx.Idents.get(funcName);
    DeclarationName DN(&II);

    // Build parameter list (directly from operator parameters, no 'this')
    llvm::SmallVector<ParmVarDecl*, 4> params;

    for (unsigned i = 0; i < MD->getNumParams(); ++i) {
        const ParmVarDecl* OrigParam = MD->getParamDecl(i);
        QualType paramType = OrigParam->getType();

        // Generate parameter name
        std::ostringstream paramName;
        if (OrigParam->getName().empty()) {
            paramName << "arg" << i;
        } else {
            paramName << OrigParam->getNameAsString();
        }

        ParmVarDecl* param = m_builder.param(paramType, paramName.str());
        params.push_back(param);
    }

    // Return type is same as operator return type
    QualType retType = MD->getReturnType();

    // Create function type
    llvm::SmallVector<QualType, 4> paramTypes;
    for (ParmVarDecl* P : params) {
        paramTypes.push_back(P->getType());
    }

    FunctionProtoType::ExtProtoInfo EPI;
    QualType funcType = Ctx.getFunctionType(retType, paramTypes, EPI);

    // Create function declaration
    FunctionDecl* FD = FunctionDecl::Create(
        Ctx, C_TU, SourceLocation(), SourceLocation(),
        DN, funcType, Ctx.getTrivialTypeSourceInfo(funcType), SC_None);

    FD->setParams(params);

    // Add to C translation unit
    C_TU->addDecl(FD);

    return FD;
}

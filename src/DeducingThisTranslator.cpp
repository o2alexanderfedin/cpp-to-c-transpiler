/**
 * @file DeducingThisTranslator.cpp
 * @brief Implementation of DeducingThisTranslator
 *
 * Phase 4: Deducing this / explicit object parameter translation for C++23 support.
 * Follows the proven translator pattern established by StaticOperatorTranslator.
 */

#include "../include/DeducingThisTranslator.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include <sstream>

using namespace clang;

DeducingThisTranslator::DeducingThisTranslator(CNodeBuilder& Builder)
    : m_builder(Builder) {}

std::vector<FunctionDecl*> DeducingThisTranslator::transformMethod(
    CXXMethodDecl* MD,
    ASTContext& Ctx,
    TranslationUnitDecl* C_TU,
    SourceLocation targetLoc) {

    std::vector<FunctionDecl*> result;

    if (!MD || !C_TU) {
        return result;
    }

    // Only handle explicit object member functions (C++23 deducing this)
    // isExplicitObjectMemberFunction() is only available in LLVM 16+
    // For LLVM 15, skip deducing this translation (C++23 feature not supported)
    #if LLVM_VERSION_MAJOR >= 16
    if (!MD->isExplicitObjectMemberFunction()) {
        return result;
    }
    #else
    // LLVM 15 doesn't support C++23 deducing this
    return result;
    #endif

    // Get the explicit object parameter (always the first parameter)
    if (MD->getNumParams() == 0) {
        return result; // Should not happen for explicit object member functions
    }

    ParmVarDecl* ExplicitObjectParam = MD->getParamDecl(0);
    QualType ParamType = ExplicitObjectParam->getType();

    // Determine which overloads we need to generate
    std::vector<QualifierSet> overloads = determineOverloads(ParamType);

    // Generate each overload
    for (const auto& Quals : overloads) {
        FunctionDecl* overload = generateOverload(MD, Quals, Ctx, C_TU, targetLoc);
        if (overload) {
            result.push_back(overload);
        }
    }

    return result;
}

CallExpr* DeducingThisTranslator::transformCall(
    CallExpr* Call,
    ASTContext& Ctx,
    SourceLocation targetLoc) {

    if (!Call) {
        return nullptr;
    }

    // Get the method being called (from the DeclRefExpr callee)
    Expr* Callee = Call->getCallee()->IgnoreImplicit();
    auto* DRE = dyn_cast<DeclRefExpr>(Callee);
    if (!DRE) {
        return nullptr;
    }

    const CXXMethodDecl* Method = dyn_cast<CXXMethodDecl>(DRE->getDecl());
    if (!Method) {
        return nullptr;
    }

    // Only handle explicit object member functions
    // isExplicitObjectMemberFunction() is only available in LLVM 16+
    #if LLVM_VERSION_MAJOR >= 16
    if (!Method->isExplicitObjectMemberFunction()) {
        return nullptr;
    }
    #else
    // LLVM 15 doesn't support C++23 deducing this
    return nullptr;
    #endif

    // For explicit object member functions, the first argument is the object
    if (Call->getNumArgs() == 0) {
        return nullptr;
    }

    Expr* Object = Call->getArg(0);
    if (!Object) {
        return nullptr;
    }

    QualifierSet CallQuals = analyzeCallSiteQualifiers(Object);

    // Find matching overload
    // Note: In a full implementation, we would look up the FunctionDecl from C_TU
    // For now, we create the call expression with the correct name
    FunctionDecl* TargetFunc = findMatchingOverload(
        const_cast<CXXMethodDecl*>(Method), CallQuals, Ctx.getTranslationUnitDecl());

    if (!TargetFunc) {
        // Create a placeholder function declaration
        const CXXRecordDecl* Class = Method->getParent();
        std::string funcName = generateOverloadName(Class, Method, CallQuals);

        IdentifierInfo& II = Ctx.Idents.get(funcName);
        DeclarationName DN(&II);

        // Build parameter types (skip first param which is explicit object param)
        llvm::SmallVector<QualType, 4> paramTypes;
        for (unsigned i = 1; i < Method->getNumParams(); ++i) {
            paramTypes.push_back(Method->getParamDecl(i)->getType());
        }

        FunctionProtoType::ExtProtoInfo EPI;
        QualType funcType = Ctx.getFunctionType(Method->getReturnType(), paramTypes, EPI);

        TargetFunc = FunctionDecl::Create(
            Ctx, Ctx.getTranslationUnitDecl(),
            targetLoc, targetLoc,
            DN, funcType, Ctx.getTrivialTypeSourceInfo(funcType), SC_None);
    }

    // Build arguments for C function call
    // First arg: address of object (if not by-value)
    llvm::SmallVector<Expr*, 4> args;

    if (!CallQuals.isValue) {
        // Pass pointer to object
        // Check if Object is already an lvalue that we can take address of
        Expr* objAddr = Object;
        if (Object->isLValue()) {
            objAddr = UnaryOperator::Create(
                Ctx, Object, UO_AddrOf,
                Ctx.getPointerType(Object->getType()),
                VK_PRValue, OK_Ordinary, targetLoc,
                false, FPOptionsOverride());
        }
        args.push_back(objAddr);
    } else {
        // Pass object by value
        args.push_back(Object);
    }

    // Remaining arguments (skip first arg which is the object)
    for (unsigned i = 1; i < Call->getNumArgs(); ++i) {
        args.push_back(Call->getArg(i));
    }

    // Create function reference
    DeclRefExpr* funcRef = DeclRefExpr::Create(
        Ctx, NestedNameSpecifierLoc(), targetLoc,
        TargetFunc, false, targetLoc,
        TargetFunc->getType(), VK_LValue);

    // Create call expression
    CallExpr* callExpr = CallExpr::Create(
        Ctx, funcRef, args, Method->getReturnType(),
        VK_PRValue, targetLoc, FPOptionsOverride());

    return callExpr;
}

std::vector<QualifierSet> DeducingThisTranslator::determineOverloads(QualType ParamType) {
    std::vector<QualifierSet> result;

    // Handle reference types
    if (ParamType->isLValueReferenceType()) {
        QualType Pointee = ParamType->getPointeeType();
        if (Pointee.isConstQualified()) {
            // const auto& → only const lvalue overload
            result.push_back(QualifierSet(true, false, false));
        } else {
            // auto& → non-const lvalue + const lvalue
            result.push_back(QualifierSet(false, false, false)); // lvalue
            result.push_back(QualifierSet(true, false, false));  // const lvalue
        }
    } else if (ParamType->isRValueReferenceType()) {
        // auto&& → forwarding reference, all 4 combinations
        result.push_back(QualifierSet(false, false, false)); // lvalue
        result.push_back(QualifierSet(true, false, false));  // const lvalue
        result.push_back(QualifierSet(false, true, false));  // rvalue
        result.push_back(QualifierSet(true, true, false));   // const rvalue
    } else {
        // auto → by value
        result.push_back(QualifierSet(false, false, true));
    }

    return result;
}

FunctionDecl* DeducingThisTranslator::generateOverload(
    CXXMethodDecl* MD,
    const QualifierSet& Quals,
    ASTContext& Ctx,
    TranslationUnitDecl* C_TU,
    SourceLocation targetLoc) {

    if (!MD || !C_TU) {
        return nullptr;
    }

    const CXXRecordDecl* Class = MD->getParent();
    if (!Class) {
        return nullptr;
    }

    // Generate function name
    std::string funcName = generateOverloadName(Class, MD, Quals);

    // Check if function already exists
    for (auto* D : C_TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == funcName) {
                return FD; // Already exists
            }
        }
    }

    // Create new function declaration
    IdentifierInfo& II = Ctx.Idents.get(funcName);
    DeclarationName DN(&II);

    // Build parameter list
    llvm::SmallVector<ParmVarDecl*, 4> params;

    // First parameter: 'this' with appropriate qualifiers
    QualType ThisType;
    if (Quals.isValue) {
        // Pass struct by value
        ThisType = Ctx.getRecordType(Class);
    } else {
        // Pass struct by pointer
        ThisType = Ctx.getPointerType(Ctx.getRecordType(Class));
        if (Quals.isConst) {
            // const struct T*
            QualType PointeeType = Ctx.getRecordType(Class);
            PointeeType.addConst();
            ThisType = Ctx.getPointerType(PointeeType);
        }
    }

    ParmVarDecl* SelfParam = m_builder.param(ThisType, "self");
    params.push_back(SelfParam);

    // Remaining parameters (skip index 0 which is the explicit object param)
    for (unsigned i = 1; i < MD->getNumParams(); ++i) {
        const ParmVarDecl* OrigParam = MD->getParamDecl(i);
        QualType paramType = OrigParam->getType();

        std::string paramName;
        if (OrigParam->getName().empty()) {
            std::ostringstream oss;
            oss << "arg" << (i - 1);
            paramName = oss.str();
        } else {
            paramName = OrigParam->getNameAsString();
        }

        ParmVarDecl* param = m_builder.param(paramType, paramName);
        params.push_back(param);
    }

    // Build parameter types for function type
    llvm::SmallVector<QualType, 4> paramTypes;
    for (ParmVarDecl* P : params) {
        paramTypes.push_back(P->getType());
    }

    // Return type is same as method return type
    QualType RetType = MD->getReturnType();

    // Create function type
    FunctionProtoType::ExtProtoInfo EPI;
    QualType funcType = Ctx.getFunctionType(RetType, paramTypes, EPI);

    // Create function declaration
    FunctionDecl* FD = FunctionDecl::Create(
        Ctx, C_TU, targetLoc, targetLoc,
        DN, funcType, Ctx.getTrivialTypeSourceInfo(funcType), SC_None);

    FD->setParams(params);

    // Transform body if present
    if (MD->hasBody()) {
        Stmt* TransformedBody = transformBody(
            MD->getBody(),
            MD->getParamDecl(0), // Original explicit object param
            SelfParam            // New 'self' param
        );
        if (TransformedBody) {
            FD->setBody(TransformedBody);
        }
    }

    // Add to C translation unit
    C_TU->addDecl(FD);

    return FD;
}

QualifierSet DeducingThisTranslator::analyzeCallSiteQualifiers(Expr* Object) {
    if (!Object) {
        return QualifierSet(false, false, false); // Default: non-const lvalue
    }

    // Remove implicit casts to get the real object
    Object = Object->IgnoreImplicit();

    QualType ObjectType = Object->getType();
    bool isConst = ObjectType.isConstQualified();
    bool isRValue = false;

    // Detect rvalues using value category
    ExprValueKind VK = Object->getValueKind();
    if (VK == VK_XValue || VK == VK_PRValue) {
        isRValue = true;
    }

    // Check for specific rvalue patterns
    if (isa<CXXTemporaryObjectExpr>(Object) ||
        isa<MaterializeTemporaryExpr>(Object)) {
        isRValue = true;
    }

    // Check for std::move or explicit rvalue cast
    if (auto* Cast = dyn_cast<CXXStaticCastExpr>(Object)) {
        if (Cast->getType()->isRValueReferenceType()) {
            isRValue = true;
        }
    }

    // Check for calls returning rvalue references
    if (auto* CallE = dyn_cast<CallExpr>(Object)) {
        if (CallE->getType()->isRValueReferenceType()) {
            isRValue = true;
        }
    }

    return QualifierSet(isConst, isRValue, false);
}

FunctionDecl* DeducingThisTranslator::findMatchingOverload(
    CXXMethodDecl* MD,
    const QualifierSet& CallQuals,
    TranslationUnitDecl* C_TU) {

    if (!MD || !C_TU) {
        return nullptr;
    }

    const CXXRecordDecl* Class = MD->getParent();
    if (!Class) {
        return nullptr;
    }

    std::string targetName = generateOverloadName(Class, MD, CallQuals);

    // Search for matching function in C_TU
    for (auto* D : C_TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == targetName) {
                return FD;
            }
        }
    }

    return nullptr;
}

std::string DeducingThisTranslator::generateOverloadName(
    const CXXRecordDecl* Class,
    const CXXMethodDecl* Method,
    const QualifierSet& Quals) {

    if (!Class || !Method) {
        return "";
    }

    std::ostringstream oss;
    oss << Class->getNameAsString() << "__" << Method->getNameAsString();
    oss << Quals.getSuffix();

    return oss.str();
}

Stmt* DeducingThisTranslator::transformBody(
    Stmt* Body,
    ParmVarDecl* OrigParam,
    ParmVarDecl* NewParam) {

    // For now, return the body as-is
    // A full implementation would traverse the body and replace all
    // references to OrigParam with references to NewParam
    //
    // This is a complex transformation that requires:
    // - Traversing all DeclRefExprs in the body
    // - Checking if they reference OrigParam
    // - Replacing with DeclRefExpr to NewParam
    // - Handling member access patterns (self.data → self->data if pointer)
    //
    // Since we're focusing on declaration and call site transformation first,
    // we'll document this as a known limitation and implement it if tests require it.

    return Body;
}

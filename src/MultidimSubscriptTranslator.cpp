/**
 * @file MultidimSubscriptTranslator.cpp
 * @brief Implementation of MultidimSubscriptTranslator
 *
 * Phase 1: Multidimensional subscript operator translation for C++23 support.
 * Follows the proven translator pattern established by VtableGenerator and
 * TemplateExtractor.
 */

#include "../include/MultidimSubscriptTranslator.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include <sstream>

using namespace clang;

MultidimSubscriptTranslator::MultidimSubscriptTranslator(CNodeBuilder& Builder)
    : m_builder(Builder) {}

CallExpr* MultidimSubscriptTranslator::transform(CXXOperatorCallExpr* E,
                                                  ASTContext& Ctx,
                                                  TranslationUnitDecl* C_TU) {
    if (!E || !C_TU) {
        return nullptr;
    }

    // Phase 2: Delegate static operators to StaticOperatorTranslator
    // This check ensures separation of concerns between Phase 1 and Phase 2
    const CXXMethodDecl* Method = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl());
    if (Method && Method->isStatic()) {
        return nullptr; // Let StaticOperatorTranslator handle static operators
    }

    // Validate that this is a multidimensional subscript
    // operator[](obj, idx1, idx2, ...) has obj as arg[0], indices as arg[1+]
    // Need at least 3 args total (obj + 2 indices) for multidimensional
    if (E->getNumArgs() < 3) {
        return nullptr; // Single-dimensional subscript, not our concern
    }

    // Get the function declaration for the subscript operator
    FunctionDecl* FD = getOrCreateSubscriptFunction(E, Ctx, C_TU);
    if (!FD) {
        return nullptr;
    }

    // Build argument list for C function call
    // C function signature: RetType ClassName__subscript_Nd(struct ClassName* self, Type1 idx1, ...)
    llvm::SmallVector<Expr*, 4> args;

    // First argument: address of object (&obj)
    Expr* object = E->getArg(0);
    Expr* objectAddr = m_builder.addrOf(object);
    args.push_back(objectAddr);

    // Remaining arguments: indices (idx1, idx2, ...)
    for (unsigned i = 1; i < E->getNumArgs(); ++i) {
        args.push_back(E->getArg(i));
    }

    // Create function call
    CallExpr* callExpr = m_builder.call(FD, args);

    // Determine if we need to dereference the result (lvalue context)
    // If the operator returns a reference and we're in lvalue context,
    // the C function returns a pointer that needs dereferencing
    if (const CXXMethodDecl* Method = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl())) {
        QualType RetType = Method->getReturnType();
        if (RetType->isReferenceType() && !Method->isConst()) {
            // Lvalue context: need to dereference pointer
            // m[i,j] = 5  →  *Matrix__subscript_2d(&m, i, j) = 5
            return callExpr; // For now, return the call directly
            // TODO: Wrap in dereference operator if parent context requires it
        }
    }

    return callExpr;
}

std::string MultidimSubscriptTranslator::generateFunctionName(
    const CXXRecordDecl* Class,
    unsigned NumIndices,
    bool IsConst) {

    if (!Class) {
        return "";
    }

    std::ostringstream oss;
    oss << Class->getNameAsString();
    oss << "__subscript_";
    oss << NumIndices;
    oss << "d";

    if (IsConst) {
        oss << "_const";
    }

    return oss.str();
}

FunctionDecl* MultidimSubscriptTranslator::getOrCreateSubscriptFunction(
    const CXXOperatorCallExpr* E,
    ASTContext& Ctx,
    TranslationUnitDecl* C_TU) {

    if (!E || !C_TU) {
        return nullptr;
    }

    // Get the operator method
    const CXXMethodDecl* Method = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl());
    if (!Method) {
        return nullptr;
    }

    // Get the class containing the operator
    const CXXRecordDecl* Class = Method->getParent();
    if (!Class) {
        return nullptr;
    }

    // Calculate number of indices (total args - 1 for object)
    unsigned NumIndices = E->getNumArgs() - 1;
    bool IsConst = Method->isConst();

    // Generate function name
    std::string funcName = generateFunctionName(Class, NumIndices, IsConst);

    // Check if function already exists in C_TU
    for (auto* D : C_TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == funcName) {
                return FD; // Already exists
            }
        }
    }

    // Create new function declaration
    // Signature: RetType* ClassName__subscript_Nd(struct ClassName* self, Type1 idx1, ...)
    // For const: RetType ClassName__subscript_Nd_const(const struct ClassName* self, ...)

    IdentifierInfo& II = Ctx.Idents.get(funcName);
    DeclarationName DN(&II);

    // Build parameter list
    llvm::SmallVector<ParmVarDecl*, 4> params;

    // First parameter: struct ClassName* self (or const struct ClassName* for const operators)
    QualType classType = Ctx.getRecordType(Class);
    if (IsConst) {
        classType = classType.withConst();
    }
    QualType selfPtrType = Ctx.getPointerType(classType);
    ParmVarDecl* selfParam = m_builder.param(selfPtrType, "self");
    params.push_back(selfParam);

    // Remaining parameters: indices from operator signature
    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        const ParmVarDecl* OrigParam = Method->getParamDecl(i);
        QualType paramType = OrigParam->getType();

        // Generate parameter name
        std::ostringstream paramName;
        if (OrigParam->getName().empty()) {
            paramName << "idx" << i;
        } else {
            paramName << OrigParam->getNameAsString();
        }

        ParmVarDecl* param = m_builder.param(paramType, paramName.str());
        params.push_back(param);
    }

    // Determine return type
    QualType retType = Method->getReturnType();

    // If method returns reference and is non-const, C function returns pointer
    if (retType->isReferenceType() && !IsConst) {
        // Strip reference, return pointer instead
        QualType pointeeType = retType.getNonReferenceType();
        retType = Ctx.getPointerType(pointeeType);
    } else if (retType->isReferenceType()) {
        // Const reference: strip reference, return by value
        retType = retType.getNonReferenceType();
    }

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

bool MultidimSubscriptTranslator::isLValueContext(const Expr* E) {
    // Heuristic: Check if the operator is const-qualified
    // Const operators return rvalues, non-const return lvalue references
    // TODO: Implement proper parent expression analysis

    if (!E) {
        return false;
    }

    // For now, use simple heuristic based on value category
    return E->isLValue();
}

std::string MultidimSubscriptTranslator::getTypeString(QualType Type) {
    // Strip references (C has no references)
    if (Type->isReferenceType()) {
        Type = Type.getNonReferenceType();
    }

    std::string typeStr;

    // Handle const qualification
    bool isConst = Type.isConstQualified();
    if (isConst) {
        typeStr = "const ";
        Type = Type.getUnqualifiedType();
    }

    // Handle pointer types
    if (Type->isPointerType()) {
        QualType pointee = Type->getPointeeType();
        typeStr += getTypeString(pointee) + "*";
        return typeStr;
    }

    // Handle record (class/struct) types
    if (Type->isRecordType()) {
        const RecordType* RT = Type->getAs<RecordType>();
        RecordDecl* RD = RT->getDecl();
        typeStr += "struct " + RD->getNameAsString();
        return typeStr;
    }

    // Handle built-in types
    typeStr += Type.getAsString();

    return typeStr;
}

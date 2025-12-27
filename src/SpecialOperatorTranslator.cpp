/**
 * @file SpecialOperatorTranslator.cpp
 * @brief Phase 52: Special Operator Overloading Implementation (v2.12.0)
 *
 * Implements translation of C++ special operator overloading to C function calls.
 * This file contains the core infrastructure and implementations for all 12 special operators.
 */

#include "SpecialOperatorTranslator.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Type.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

using namespace clang;

// ============================================================================
// Constructor
// ============================================================================

SpecialOperatorTranslator::SpecialOperatorTranslator(CNodeBuilder& Builder,
                                                     NameMangler& Mangler)
    : m_builder(Builder), m_mangler(Mangler) {
    llvm::outs() << "SpecialOperatorTranslator initialized (Phase 52)\n";
}

// ============================================================================
// Main Entry Points
// ============================================================================

FunctionDecl* SpecialOperatorTranslator::transformMethod(CXXMethodDecl* MD,
                                                         ASTContext& Ctx,
                                                         TranslationUnitDecl* C_TU) {
    if (!MD || !MD->isOverloadedOperator()) {
        return nullptr;
    }

    OverloadedOperatorKind Op = MD->getOverloadedOperator();
    if (!isSpecialOperator(Op)) {
        return nullptr;
    }

    // Check if already transformed
    auto it = m_methodMap.find(MD);
    if (it != m_methodMap.end()) {
        return it->second;
    }

    FunctionDecl* CFn = nullptr;

    // Route to appropriate translator based on operator type
    switch (Op) {
        case OO_Subscript:
            CFn = translateInstanceSubscript(MD, Ctx, C_TU);
            break;

        case OO_Call:
            CFn = translateInstanceCall(MD, Ctx, C_TU);
            break;

        case OO_Arrow:
            CFn = translateArrow(MD, Ctx, C_TU);
            break;

        case OO_Star:
            // Dereference operator (unary *)
            // Note: Binary * (multiplication) is handled by ArithmeticOperatorTranslator
            if (MD->getNumParams() == 0) {
                CFn = translateDereference(MD, Ctx, C_TU);
            }
            break;

        case OO_LessLess:
            // Distinguish stream output from bitwise left shift
            // For now, treat as stream output (will refine in transformCall)
            CFn = translateStreamOutput(MD, Ctx, C_TU);
            break;

        case OO_GreaterGreater:
            // Distinguish stream input from bitwise right shift
            CFn = translateStreamInput(MD, Ctx, C_TU);
            break;

        case OO_Equal:
            // Assignment operator (copy or move)
            if (MD->isCopyAssignmentOperator()) {
                CFn = translateCopyAssignment(MD, Ctx, C_TU);
            } else if (MD->isMoveAssignmentOperator()) {
                CFn = translateMoveAssignment(MD, Ctx, C_TU);
            }
            break;

        case OO_Amp:
            // Address-of operator (rare)
            CFn = translateAddressOf(MD, Ctx, C_TU);
            break;

        case OO_Comma:
            // Comma operator (very rare)
            CFn = translateComma(MD, Ctx, C_TU);
            break;

        default:
            // Not a special operator we handle
            return nullptr;
    }

    // Cache the result
    if (CFn) {
        m_methodMap[MD] = CFn;
    }

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::transformConversion(CXXConversionDecl* CD,
                                                             ASTContext& Ctx,
                                                             TranslationUnitDecl* C_TU) {
    if (!CD) {
        return nullptr;
    }

    // Check if already transformed
    auto it = m_conversionMap.find(CD);
    if (it != m_conversionMap.end()) {
        return it->second;
    }

    // Get conversion target type
    QualType ConvType = CD->getConversionType();

    FunctionDecl* CFn = nullptr;

    // Check if bool conversion (common case)
    if (ConvType->isBooleanType()) {
        CFn = translateBoolConversion(CD, Ctx, C_TU);
    } else {
        CFn = translateConversionOperator(CD, Ctx, C_TU);
    }

    // Cache the result
    if (CFn) {
        m_conversionMap[CD] = CFn;
    }

    return CFn;
}

CallExpr* SpecialOperatorTranslator::transformCall(CXXOperatorCallExpr* E,
                                                    ASTContext& Ctx) {
    if (!E) {
        return nullptr;
    }

    OverloadedOperatorKind Op = E->getOperator();
    if (!isSpecialOperator(Op)) {
        return nullptr;
    }

    // Route to appropriate call transformer
    switch (Op) {
        case OO_Subscript:
            return transformSubscriptCall(E, Ctx);

        case OO_Call:
            return transformCallOperatorCall(E, Ctx);

        case OO_Arrow:
            return transformArrowCall(E, Ctx);

        case OO_Star:
            // Dereference operator
            if (E->getNumArgs() == 1) {
                return transformDereferenceCall(E, Ctx);
            }
            break;

        case OO_LessLess:
        case OO_GreaterGreater:
            // Stream operators (distinguish from bitwise shift)
            if (isStreamOperator(E)) {
                return transformStreamCall(E, Ctx);
            }
            break;

        case OO_Equal:
            return transformAssignmentCall(E, Ctx);

        case OO_Amp:
        case OO_Comma:
            // Rare operators - treat like binary operators
            // Fall through to default handling
            break;

        default:
            break;
    }

    return nullptr;
}

// ============================================================================
// Detection Methods
// ============================================================================

bool SpecialOperatorTranslator::isSpecialOperator(OverloadedOperatorKind Op) const {
    switch (Op) {
        case OO_Subscript:        // operator[]
        case OO_Call:             // operator()
        case OO_Arrow:            // operator->
        case OO_Star:             // operator* (dereference)
        case OO_LessLess:         // operator<< (stream output)
        case OO_GreaterGreater:   // operator>> (stream input)
        case OO_Equal:            // operator= (assignment)
        case OO_Amp:              // operator& (address-of)
        case OO_Comma:            // operator, (comma)
            return true;
        default:
            return false;
    }
}

// ============================================================================
// Operator Translation Methods (using correct CNodeBuilder API)
// ============================================================================

FunctionDecl* SpecialOperatorTranslator::translateInstanceSubscript(CXXMethodDecl* MD,
                                                                     ASTContext& Ctx,
                                                                     TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating instance subscript operator: "
                 << MD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateOperatorName(MD);

    const CXXRecordDecl* ClassDecl = MD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    // Build parameter list
    SmallVector<ParmVarDecl*, 4> Params;

    // Add 'this' parameter
    QualType ThisPtrType = Ctx.getPointerType(MD->isConst() ? ClassType.withConst() : ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    // Add operator parameters
    for (const ParmVarDecl* Param : MD->parameters()) {
        IdentifierInfo* ParamII = &Ctx.Idents.get(Param->getNameAsString());
        ParmVarDecl* PVD = ParmVarDecl::Create(
            Ctx, nullptr, SourceLocation(), SourceLocation(),
            ParamII, Param->getType(), nullptr, SC_None, nullptr);
        Params.push_back(PVD);
    }

    // Return type: Convert reference to pointer
    QualType ReturnType = MD->getReturnType();
    if (ReturnType->isReferenceType()) {
        ReturnType = Ctx.getPointerType(ReturnType.getNonReferenceType());
    }

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateInstanceCall(CXXMethodDecl* MD,
                                                               ASTContext& Ctx,
                                                               TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating instance call operator: "
                 << MD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateOperatorName(MD);

    const CXXRecordDecl* ClassDecl = MD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 4> Params;

    QualType ThisPtrType = Ctx.getPointerType(MD->isConst() ? ClassType.withConst() : ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    for (const ParmVarDecl* Param : MD->parameters()) {
        IdentifierInfo* ParamII = &Ctx.Idents.get(Param->getNameAsString());
        ParmVarDecl* PVD = ParmVarDecl::Create(
            Ctx, nullptr, SourceLocation(), SourceLocation(),
            ParamII, Param->getType(), nullptr, SC_None, nullptr);
        Params.push_back(PVD);
    }

    QualType ReturnType = MD->getReturnType();

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateArrow(CXXMethodDecl* MD,
                                                        ASTContext& Ctx,
                                                        TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating arrow operator: "
                 << MD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateOperatorName(MD);

    const CXXRecordDecl* ClassDecl = MD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 1> Params;

    QualType ThisPtrType = Ctx.getPointerType(MD->isConst() ? ClassType.withConst() : ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    QualType ReturnType = MD->getReturnType();

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateDereference(CXXMethodDecl* MD,
                                                              ASTContext& Ctx,
                                                              TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating dereference operator: "
                 << MD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateOperatorName(MD);

    const CXXRecordDecl* ClassDecl = MD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 1> Params;

    QualType ThisPtrType = Ctx.getPointerType(MD->isConst() ? ClassType.withConst() : ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    QualType ReturnType = MD->getReturnType();
    if (ReturnType->isReferenceType()) {
        ReturnType = Ctx.getPointerType(ReturnType.getNonReferenceType());
    }

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateStreamOutput(CXXMethodDecl* MD,
                                                               ASTContext& Ctx,
                                                               TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating stream output operator: "
                 << MD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateOperatorName(MD);

    const CXXRecordDecl* ClassDecl = MD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 2> Params;

    QualType ThisPtrType = Ctx.getPointerType(MD->isConst() ? ClassType.withConst() : ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    for (const ParmVarDecl* Param : MD->parameters()) {
        IdentifierInfo* ParamII = &Ctx.Idents.get(Param->getNameAsString());
        ParmVarDecl* PVD = ParmVarDecl::Create(
            Ctx, nullptr, SourceLocation(), SourceLocation(),
            ParamII, Param->getType(), nullptr, SC_None, nullptr);
        Params.push_back(PVD);
    }

    QualType ReturnType = Ctx.VoidTy;

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateStreamInput(CXXMethodDecl* MD,
                                                              ASTContext& Ctx,
                                                              TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating stream input operator: "
                 << MD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateOperatorName(MD);

    const CXXRecordDecl* ClassDecl = MD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 2> Params;

    QualType ThisPtrType = Ctx.getPointerType(MD->isConst() ? ClassType.withConst() : ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    for (const ParmVarDecl* Param : MD->parameters()) {
        IdentifierInfo* ParamII = &Ctx.Idents.get(Param->getNameAsString());
        ParmVarDecl* PVD = ParmVarDecl::Create(
            Ctx, nullptr, SourceLocation(), SourceLocation(),
            ParamII, Param->getType(), nullptr, SC_None, nullptr);
        Params.push_back(PVD);
    }

    QualType ReturnType = Ctx.VoidTy;

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateBoolConversion(CXXConversionDecl* CD,
                                                                 ASTContext& Ctx,
                                                                 TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating bool conversion operator: "
                 << CD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateConversionName(CD);

    const CXXRecordDecl* ClassDecl = CD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 1> Params;

    QualType ThisPtrType = Ctx.getPointerType(CD->isConst() ? ClassType.withConst() : ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    QualType ReturnType = Ctx.BoolTy;

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateConversionOperator(CXXConversionDecl* CD,
                                                                     ASTContext& Ctx,
                                                                     TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating conversion operator: "
                 << CD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateConversionName(CD);

    const CXXRecordDecl* ClassDecl = CD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 1> Params;

    QualType ThisPtrType = Ctx.getPointerType(CD->isConst() ? ClassType.withConst() : ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    QualType ReturnType = CD->getConversionType();

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateCopyAssignment(CXXMethodDecl* MD,
                                                                 ASTContext& Ctx,
                                                                 TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating copy assignment operator: "
                 << MD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateOperatorName(MD);

    const CXXRecordDecl* ClassDecl = MD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 2> Params;

    QualType ThisPtrType = Ctx.getPointerType(ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    for (const ParmVarDecl* Param : MD->parameters()) {
        IdentifierInfo* ParamII = &Ctx.Idents.get(Param->getNameAsString());
        ParmVarDecl* PVD = ParmVarDecl::Create(
            Ctx, nullptr, SourceLocation(), SourceLocation(),
            ParamII, Param->getType(), nullptr, SC_None, nullptr);
        Params.push_back(PVD);
    }

    QualType ReturnType = Ctx.getPointerType(ClassType);

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateMoveAssignment(CXXMethodDecl* MD,
                                                                 ASTContext& Ctx,
                                                                 TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating move assignment operator: "
                 << MD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateOperatorName(MD);

    const CXXRecordDecl* ClassDecl = MD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 2> Params;

    QualType ThisPtrType = Ctx.getPointerType(ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    for (const ParmVarDecl* Param : MD->parameters()) {
        QualType ParamType = Param->getType();
        if (ParamType->isRValueReferenceType()) {
            ParamType = Ctx.getPointerType(ParamType.getNonReferenceType());
        }
        IdentifierInfo* ParamII = &Ctx.Idents.get(Param->getNameAsString());
        ParmVarDecl* PVD = ParmVarDecl::Create(
            Ctx, nullptr, SourceLocation(), SourceLocation(),
            ParamII, ParamType, nullptr, SC_None, nullptr);
        Params.push_back(PVD);
    }

    QualType ReturnType = Ctx.getPointerType(ClassType);

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateAddressOf(CXXMethodDecl* MD,
                                                            ASTContext& Ctx,
                                                            TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating address-of operator: "
                 << MD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateOperatorName(MD);

    const CXXRecordDecl* ClassDecl = MD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 1> Params;

    QualType ThisPtrType = Ctx.getPointerType(MD->isConst() ? ClassType.withConst() : ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    QualType ReturnType = MD->getReturnType();

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::translateComma(CXXMethodDecl* MD,
                                                        ASTContext& Ctx,
                                                        TranslationUnitDecl* C_TU) {
    llvm::outs() << "Translating comma operator: "
                 << MD->getQualifiedNameAsString() << "\n";

    std::string FnName = generateOperatorName(MD);

    const CXXRecordDecl* ClassDecl = MD->getParent();
    QualType ClassType = Ctx.getRecordType(ClassDecl);

    SmallVector<ParmVarDecl*, 2> Params;

    QualType ThisPtrType = Ctx.getPointerType(MD->isConst() ? ClassType.withConst() : ClassType);
    IdentifierInfo* ThisII = &Ctx.Idents.get("this");
    ParmVarDecl* ThisParam = ParmVarDecl::Create(
        Ctx, nullptr, SourceLocation(), SourceLocation(),
        ThisII, ThisPtrType, nullptr, SC_None, nullptr);
    Params.push_back(ThisParam);

    for (const ParmVarDecl* Param : MD->parameters()) {
        IdentifierInfo* ParamII = &Ctx.Idents.get(Param->getNameAsString());
        ParmVarDecl* PVD = ParmVarDecl::Create(
            Ctx, nullptr, SourceLocation(), SourceLocation(),
            ParamII, Param->getType(), nullptr, SC_None, nullptr);
        Params.push_back(PVD);
    }

    QualType ReturnType = MD->getReturnType();

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    return CFn;
}

// ============================================================================
// Call Site Transformation Methods (using correct CNodeBuilder API)
// ============================================================================

CallExpr* SpecialOperatorTranslator::transformSubscriptCall(CXXOperatorCallExpr* E,
                                                             ASTContext& Ctx) {
    CXXMethodDecl* MD = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl());
    if (!MD) {
        return nullptr;
    }

    FunctionDecl* CFn = findOrCreateFunction(MD, Ctx, Ctx.getTranslationUnitDecl());
    if (!CFn) {
        return nullptr;
    }

    SmallVector<Expr*, 2> CArgs;

    Expr* Object = E->getArg(0);
    Expr* ObjectAddr = m_builder.addrOf(Object);
    CArgs.push_back(ObjectAddr);

    for (unsigned i = 1; i < E->getNumArgs(); ++i) {
        CArgs.push_back(E->getArg(i));
    }

    return m_builder.call(CFn, CArgs);
}

CallExpr* SpecialOperatorTranslator::transformCallOperatorCall(CXXOperatorCallExpr* E,
                                                                ASTContext& Ctx) {
    CXXMethodDecl* MD = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl());
    if (!MD) {
        return nullptr;
    }

    FunctionDecl* CFn = findOrCreateFunction(MD, Ctx, Ctx.getTranslationUnitDecl());
    if (!CFn) {
        return nullptr;
    }

    SmallVector<Expr*, 4> CArgs;

    Expr* Object = E->getArg(0);
    Expr* ObjectAddr = m_builder.addrOf(Object);
    CArgs.push_back(ObjectAddr);

    for (unsigned i = 1; i < E->getNumArgs(); ++i) {
        CArgs.push_back(E->getArg(i));
    }

    return m_builder.call(CFn, CArgs);
}

CallExpr* SpecialOperatorTranslator::transformArrowCall(CXXOperatorCallExpr* E,
                                                         ASTContext& Ctx) {
    CXXMethodDecl* MD = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl());
    if (!MD) {
        return nullptr;
    }

    FunctionDecl* CFn = findOrCreateFunction(MD, Ctx, Ctx.getTranslationUnitDecl());
    if (!CFn) {
        return nullptr;
    }

    SmallVector<Expr*, 1> CArgs;

    Expr* Object = E->getArg(0);
    Expr* ObjectAddr = m_builder.addrOf(Object);
    CArgs.push_back(ObjectAddr);

    return m_builder.call(CFn, CArgs);
}

CallExpr* SpecialOperatorTranslator::transformDereferenceCall(CXXOperatorCallExpr* E,
                                                               ASTContext& Ctx) {
    CXXMethodDecl* MD = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl());
    if (!MD) {
        return nullptr;
    }

    FunctionDecl* CFn = findOrCreateFunction(MD, Ctx, Ctx.getTranslationUnitDecl());
    if (!CFn) {
        return nullptr;
    }

    SmallVector<Expr*, 1> CArgs;

    Expr* Object = E->getArg(0);
    Expr* ObjectAddr = m_builder.addrOf(Object);
    CArgs.push_back(ObjectAddr);

    return m_builder.call(CFn, CArgs);
}

CallExpr* SpecialOperatorTranslator::transformStreamCall(CXXOperatorCallExpr* E,
                                                          ASTContext& Ctx) {
    CXXMethodDecl* MD = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl());
    if (!MD) {
        return nullptr;
    }

    FunctionDecl* CFn = findOrCreateFunction(MD, Ctx, Ctx.getTranslationUnitDecl());
    if (!CFn) {
        return nullptr;
    }

    SmallVector<Expr*, 2> CArgs;

    for (unsigned i = 0; i < E->getNumArgs(); ++i) {
        Expr* Arg = E->getArg(i);
        if (Arg->getType()->isRecordType()) {
            Arg = m_builder.addrOf(Arg);
        }
        CArgs.push_back(Arg);
    }

    return m_builder.call(CFn, CArgs);
}

CallExpr* SpecialOperatorTranslator::transformAssignmentCall(CXXOperatorCallExpr* E,
                                                              ASTContext& Ctx) {
    CXXMethodDecl* MD = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl());
    if (!MD) {
        return nullptr;
    }

    FunctionDecl* CFn = findOrCreateFunction(MD, Ctx, Ctx.getTranslationUnitDecl());
    if (!CFn) {
        return nullptr;
    }

    SmallVector<Expr*, 2> CArgs;

    Expr* LHS = E->getArg(0);
    Expr* LHSAddr = m_builder.addrOf(LHS);
    CArgs.push_back(LHSAddr);

    Expr* RHS = E->getArg(1);
    if (RHS->getType()->isRecordType()) {
        RHS = m_builder.addrOf(RHS);
    }
    CArgs.push_back(RHS);

    return m_builder.call(CFn, CArgs);
}

// ============================================================================
// Utility Methods
// ============================================================================

std::string SpecialOperatorTranslator::generateOperatorName(const CXXMethodDecl* MD) {
    if (!MD) {
        return "";
    }

    // Use NameMangler's standard mangling
    return m_mangler.mangleMethodName(const_cast<CXXMethodDecl*>(MD));
}

std::string SpecialOperatorTranslator::generateConversionName(const CXXConversionDecl* CD) {
    if (!CD) {
        return "";
    }

    const CXXRecordDecl* ClassDecl = CD->getParent();
    std::string ClassName = ClassDecl->getNameAsString();

    QualType ConvType = CD->getConversionType();
    std::string TargetType = ConvType.getAsString();

    // Sanitize target type name for C identifier
    std::string OpName = "operator_to_";
    for (char c : TargetType) {
        if (isalnum(c)) {
            OpName += c;
        } else if (c == ' ' || c == '*' || c == '&') {
            OpName += '_';
        }
    }

    if (CD->isConst()) {
        OpName += "_const";
    }

    return ClassName + "_" + OpName;
}

bool SpecialOperatorTranslator::isStreamOperator(CXXOperatorCallExpr* E) const {
    if (!E || E->getNumArgs() < 2) {
        return false;
    }

    QualType FirstParamType = E->getArg(0)->getType();
    if (FirstParamType->isReferenceType()) {
        QualType Pointee = FirstParamType->getPointeeType();
        std::string TypeStr = Pointee.getAsString();
        if (TypeStr.find("ostream") != std::string::npos ||
            TypeStr.find("istream") != std::string::npos) {
            return true;
        }
    }

    return false;
}

bool SpecialOperatorTranslator::isBitwiseShiftOperator(CXXOperatorCallExpr* E) const {
    return !isStreamOperator(E);
}

FunctionDecl* SpecialOperatorTranslator::findOrCreateFunction(const CXXMethodDecl* MD,
                                                               ASTContext& Ctx,
                                                               TranslationUnitDecl* C_TU) {
    auto it = m_methodMap.find(MD);
    if (it != m_methodMap.end()) {
        return it->second;
    }

    FunctionDecl* CFn = const_cast<SpecialOperatorTranslator*>(this)->transformMethod(
        const_cast<CXXMethodDecl*>(MD), Ctx, C_TU);

    return CFn;
}

FunctionDecl* SpecialOperatorTranslator::findOrCreateConversionFunction(const CXXConversionDecl* CD,
                                                                        ASTContext& Ctx,
                                                                        TranslationUnitDecl* C_TU) {
    auto it = m_conversionMap.find(CD);
    if (it != m_conversionMap.end()) {
        return it->second;
    }

    FunctionDecl* CFn = const_cast<SpecialOperatorTranslator*>(this)->transformConversion(
        const_cast<CXXConversionDecl*>(CD), Ctx, C_TU);

    return CFn;
}

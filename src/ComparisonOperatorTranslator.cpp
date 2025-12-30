/**
 * @file ComparisonOperatorTranslator.cpp
 * @brief Phase 51: Comparison & Logical Operator Overloading Implementation (v2.11.0)
 *
 * Implements translation of C++ comparison and logical operator overloading to C function calls.
 * This file contains the core infrastructure and implementations for all 9 operators.
 * All operators return bool (via <stdbool.h>).
 */

#include "ComparisonOperatorTranslator.h"
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

ComparisonOperatorTranslator::ComparisonOperatorTranslator(CNodeBuilder& Builder)
    : m_builder(Builder) {
    llvm::outs() << "ComparisonOperatorTranslator initialized (Phase 51)\n";
}

// ============================================================================
// Main Entry Points
// ============================================================================

FunctionDecl* ComparisonOperatorTranslator::transformMethod(CXXMethodDecl* MD,
                                                             ASTContext& Ctx,
                                                             TranslationUnitDecl* C_TU) {
    if (!MD || !MD->isOverloadedOperator()) {
        return nullptr;
    }

    OverloadedOperatorKind Op = MD->getOverloadedOperator();
    if (!isComparisonOperator(Op)) {
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
        // Relational operators
        case OO_Less:
            CFn = translateLessThan(MD, Ctx, C_TU);
            break;

        case OO_Greater:
            CFn = translateGreaterThan(MD, Ctx, C_TU);
            break;

        case OO_LessEqual:
            CFn = translateLessThanOrEqual(MD, Ctx, C_TU);
            break;

        case OO_GreaterEqual:
            CFn = translateGreaterThanOrEqual(MD, Ctx, C_TU);
            break;

        // Equality operators
        case OO_EqualEqual:
            CFn = translateEqual(MD, Ctx, C_TU);
            break;

        case OO_ExclaimEqual:
            CFn = translateNotEqual(MD, Ctx, C_TU);
            break;

        // Logical operators
        case OO_Exclaim:
            CFn = translateLogicalNot(MD, Ctx, C_TU);
            break;

        case OO_AmpAmp:
            CFn = translateLogicalAnd(MD, Ctx, C_TU);
            break;

        case OO_PipePipe:
            CFn = translateLogicalOr(MD, Ctx, C_TU);
            break;

        default:
            return nullptr;
    }

    if (CFn) {
        m_methodMap[MD] = CFn;
        llvm::outs() << "Transformed comparison/logical operator: "
                     << MD->getNameAsString() << " -> "
                     << CFn->getNameAsString() << "\n";
    }

    return CFn;
}

CallExpr* ComparisonOperatorTranslator::transformCall(CXXOperatorCallExpr* E,
                                                       ASTContext& Ctx) {
    if (!E) {
        return nullptr;
    }

    OverloadedOperatorKind Op = E->getOperator();
    if (!isComparisonOperator(Op)) {
        return nullptr;
    }

    // Route to appropriate call transformer
    switch (Op) {
        // Binary comparison operators (relational + equality)
        case OO_Less:
        case OO_Greater:
        case OO_LessEqual:
        case OO_GreaterEqual:
        case OO_EqualEqual:
        case OO_ExclaimEqual:
        case OO_AmpAmp:
        case OO_PipePipe:
            return transformBinaryComparisonCall(E, Ctx);

        // Unary logical operator
        case OO_Exclaim:
            return transformUnaryLogicalCall(E, Ctx);

        default:
            return nullptr;
    }
}

bool ComparisonOperatorTranslator::isComparisonOperator(OverloadedOperatorKind Op) const {
    switch (Op) {
        // Relational operators
        case OO_Less:          // <
        case OO_Greater:       // >
        case OO_LessEqual:     // <=
        case OO_GreaterEqual:  // >=
        // Equality operators
        case OO_EqualEqual:    // ==
        case OO_ExclaimEqual:  // !=
        // Logical operators
        case OO_Exclaim:       // !
        case OO_AmpAmp:        // &&
        case OO_PipePipe:      // ||
            return true;
        default:
            return false;
    }
}

// ============================================================================
// Relational Operator Translators (4 operators)
// ============================================================================

FunctionDecl* ComparisonOperatorTranslator::translateLessThan(CXXMethodDecl* MD,
                                                               ASTContext& Ctx,
                                                               TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ComparisonOperatorTranslator::translateGreaterThan(CXXMethodDecl* MD,
                                                                  ASTContext& Ctx,
                                                                  TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ComparisonOperatorTranslator::translateLessThanOrEqual(CXXMethodDecl* MD,
                                                                      ASTContext& Ctx,
                                                                      TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ComparisonOperatorTranslator::translateGreaterThanOrEqual(CXXMethodDecl* MD,
                                                                         ASTContext& Ctx,
                                                                         TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

// ============================================================================
// Equality Operator Translators (2 operators)
// ============================================================================

FunctionDecl* ComparisonOperatorTranslator::translateEqual(CXXMethodDecl* MD,
                                                            ASTContext& Ctx,
                                                            TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ComparisonOperatorTranslator::translateNotEqual(CXXMethodDecl* MD,
                                                               ASTContext& Ctx,
                                                               TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

// ============================================================================
// Logical Operator Translators (3 operators)
// ============================================================================

FunctionDecl* ComparisonOperatorTranslator::translateLogicalNot(CXXMethodDecl* MD,
                                                                 ASTContext& Ctx,
                                                                 TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ComparisonOperatorTranslator::translateLogicalAnd(CXXMethodDecl* MD,
                                                                 ASTContext& Ctx,
                                                                 TranslationUnitDecl* C_TU) {
    llvm::outs() << "WARNING: operator&& loses short-circuit evaluation\n";
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ComparisonOperatorTranslator::translateLogicalOr(CXXMethodDecl* MD,
                                                                ASTContext& Ctx,
                                                                TranslationUnitDecl* C_TU) {
    llvm::outs() << "WARNING: operator|| loses short-circuit evaluation\n";
    return findOrCreateFunction(MD, Ctx, C_TU);
}

// ============================================================================
// Call Site Transformation Helpers
// ============================================================================

CallExpr* ComparisonOperatorTranslator::transformBinaryComparisonCall(CXXOperatorCallExpr* E,
                                                                       ASTContext& Ctx) {
    // Get the callee (the operator method)
    auto* Callee = E->getCalleeDecl();
    if (!Callee) {
        return nullptr;
    }

    auto* MD = dyn_cast<CXXMethodDecl>(Callee);
    if (!MD) {
        return nullptr;
    }

    // Find the corresponding C function
    auto it = m_methodMap.find(MD);
    if (it == m_methodMap.end()) {
        llvm::errs() << "Warning: C function not found for comparison operator call\n";
        return nullptr;
    }

    FunctionDecl* CFn = it->second;

    // Binary operator: args = [object, operand]
    // Transform to: C_function(&object, &operand)
    SmallVector<Expr*, 2> Args;

    // Arg 0: object (this)
    Expr* Object = E->getArg(0);
    Expr* ObjectAddr = m_builder.addrOf(Object);
    Args.push_back(ObjectAddr);

    // Arg 1: operand
    Expr* Operand = E->getArg(1);
    Expr* OperandAddr = m_builder.addrOf(Operand);
    Args.push_back(OperandAddr);

    // Create the call expression
    return m_builder.call(CFn, Args);
}

CallExpr* ComparisonOperatorTranslator::transformUnaryLogicalCall(CXXOperatorCallExpr* E,
                                                                   ASTContext& Ctx) {
    // Get the callee (the operator method)
    auto* Callee = E->getCalleeDecl();
    if (!Callee) {
        return nullptr;
    }

    auto* MD = dyn_cast<CXXMethodDecl>(Callee);
    if (!MD) {
        return nullptr;
    }

    // Find the corresponding C function
    auto it = m_methodMap.find(MD);
    if (it == m_methodMap.end()) {
        llvm::errs() << "Warning: C function not found for unary logical operator call\n";
        return nullptr;
    }

    FunctionDecl* CFn = it->second;

    // Unary operator: args = [object]
    // Transform to: C_function(&object)
    SmallVector<Expr*, 1> Args;

    Expr* Object = E->getArg(0);
    Expr* ObjectAddr = m_builder.addrOf(Object);
    Args.push_back(ObjectAddr);

    return m_builder.call(CFn, Args);
}

// ============================================================================
// Utility Functions
// ============================================================================

std::string ComparisonOperatorTranslator::generateOperatorName(const CXXMethodDecl* MD) {
    // Delegate to cpptoc::mangle_method for consistent naming
    return cpptoc::mangle_method(MD);
}

FunctionDecl* ComparisonOperatorTranslator::findOrCreateFunction(const CXXMethodDecl* MD,
                                                                  ASTContext& Ctx,
                                                                  TranslationUnitDecl* C_TU) {
    if (!MD || !C_TU) {
        return nullptr;
    }

    // Generate function name
    std::string FnName = generateOperatorName(MD);

    // Check if function already exists in C_TU
    for (auto* Decl : C_TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(Decl)) {
            if (FD->getNameAsString() == FnName) {
                return FD;
            }
        }
    }

    // Create new function declaration
    // Signature: bool FnName(Class* this, params...)
    //            ^^^^ ALL comparison/logical operators return bool

    // Build parameter types: this + original params
    SmallVector<QualType, 4> ParamTypes;
    SmallVector<std::string, 4> ParamNames;

    // Add 'this' parameter
    QualType ClassType = Ctx.getRecordType(MD->getParent());
    QualType ThisType = MD->isConst() ?
        Ctx.getPointerType(Ctx.getConstType(ClassType)) :
        Ctx.getPointerType(ClassType);
    ParamTypes.push_back(ThisType);
    ParamNames.push_back("this");

    // Add original parameters
    for (unsigned i = 0; i < MD->getNumParams(); ++i) {
        const ParmVarDecl* Param = MD->getParamDecl(i);
        QualType ParamType = Param->getType();

        // Convert reference types to pointers
        if (ParamType->isReferenceType()) {
            QualType PointeeType = ParamType->getPointeeType();
            ParamType = Ctx.getPointerType(PointeeType);
        }

        ParamTypes.push_back(ParamType);

        std::string ParamName = Param->getNameAsString();
        if (ParamName.empty()) {
            ParamName = "arg" + std::to_string(i);
        }
        ParamNames.push_back(ParamName);
    }

    // Get return type - ALL comparison/logical operators return bool
    QualType ReturnType = createBoolReturnType(Ctx);

    // Create function declaration using CNodeBuilder
    // Build ParmVarDecl array
    SmallVector<ParmVarDecl*, 4> Params;
    for (size_t i = 0; i < ParamTypes.size(); ++i) {
        IdentifierInfo* ParamII = &Ctx.Idents.get(ParamNames[i]);
        ParmVarDecl* PVD = ParmVarDecl::Create(
            Ctx, nullptr, SourceLocation(), SourceLocation(),
            ParamII, ParamTypes[i], nullptr, SC_None, nullptr);
        Params.push_back(PVD);
    }

    FunctionDecl* CFn = m_builder.funcDecl(FnName, ReturnType, Params, nullptr);

    if (CFn) {
        llvm::outs() << "Created C function for comparison/logical operator: " << FnName
                     << " (returns bool)\n";
    }

    return CFn;
}

QualType ComparisonOperatorTranslator::createBoolReturnType(ASTContext& Ctx) const {
    // Return bool type (C99's _Bool via <stdbool.h>)
    return Ctx.BoolTy;
}

bool ComparisonOperatorTranslator::isUnaryOperator(const CXXMethodDecl* MD) const {
    if (!MD) {
        return false;
    }

    // Unary operators have 0 parameters (excluding 'this')
    // Binary operators have 1 parameter
    return MD->getNumParams() == 0;
}

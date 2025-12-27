/**
 * @file ArithmeticOperatorTranslator.cpp
 * @brief Phase 50: Arithmetic Operator Overloading Implementation (v2.10.0)
 *
 * Implements translation of C++ arithmetic operator overloading to C function calls.
 * This file contains the core infrastructure and implementations for all 10 operators.
 */

#include "ArithmeticOperatorTranslator.h"
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

ArithmeticOperatorTranslator::ArithmeticOperatorTranslator(CNodeBuilder& Builder,
                                                           NameMangler& Mangler)
    : m_builder(Builder), m_mangler(Mangler) {
    llvm::outs() << "ArithmeticOperatorTranslator initialized (Phase 50)\n";
}

// ============================================================================
// Main Entry Points
// ============================================================================

FunctionDecl* ArithmeticOperatorTranslator::transformMethod(CXXMethodDecl* MD,
                                                             ASTContext& Ctx,
                                                             TranslationUnitDecl* C_TU) {
    if (!MD || !MD->isOverloadedOperator()) {
        return nullptr;
    }

    OverloadedOperatorKind Op = MD->getOverloadedOperator();
    if (!isArithmeticOperator(Op)) {
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
        // Binary operators
        case OO_Plus:
            if (isBinaryOperator(MD)) {
                CFn = translateBinaryPlus(MD, Ctx, C_TU);
            } else {
                CFn = translateUnaryPlus(MD, Ctx, C_TU);
            }
            break;

        case OO_Minus:
            if (isBinaryOperator(MD)) {
                CFn = translateBinaryMinus(MD, Ctx, C_TU);
            } else {
                CFn = translateUnaryMinus(MD, Ctx, C_TU);
            }
            break;

        case OO_Star:
            if (isBinaryOperator(MD)) {
                CFn = translateBinaryMultiply(MD, Ctx, C_TU);
            }
            // Note: Unary * (dereference) is handled separately (not arithmetic)
            break;

        case OO_Slash:
            CFn = translateBinaryDivide(MD, Ctx, C_TU);
            break;

        case OO_Percent:
            CFn = translateBinaryModulo(MD, Ctx, C_TU);
            break;

        // Increment/Decrement
        case OO_PlusPlus:
            if (isPrefixOperator(MD)) {
                CFn = translatePrefixIncrement(MD, Ctx, C_TU);
            } else {
                CFn = translatePostfixIncrement(MD, Ctx, C_TU);
            }
            break;

        case OO_MinusMinus:
            if (isPrefixOperator(MD)) {
                CFn = translatePrefixDecrement(MD, Ctx, C_TU);
            } else {
                CFn = translatePostfixDecrement(MD, Ctx, C_TU);
            }
            break;

        // Compound assignment
        case OO_PlusEqual:
        case OO_MinusEqual:
        case OO_StarEqual:
        case OO_SlashEqual:
            CFn = translateCompoundAssignment(MD, Ctx, C_TU);
            break;

        default:
            return nullptr;
    }

    if (CFn) {
        m_methodMap[MD] = CFn;
        llvm::outs() << "Transformed arithmetic operator: "
                     << MD->getNameAsString() << " -> "
                     << CFn->getNameAsString() << "\n";
    }

    return CFn;
}

CallExpr* ArithmeticOperatorTranslator::transformCall(CXXOperatorCallExpr* E,
                                                       ASTContext& Ctx) {
    if (!E) {
        return nullptr;
    }

    OverloadedOperatorKind Op = E->getOperator();
    if (!isArithmeticOperator(Op)) {
        return nullptr;
    }

    // Route to appropriate call transformer
    switch (Op) {
        case OO_Plus:
        case OO_Minus:
        case OO_Star:
        case OO_Slash:
        case OO_Percent:
            if (E->getNumArgs() == 2) {
                return transformBinaryOpCall(E, Ctx);
            } else {
                return transformUnaryOpCall(E, Ctx);
            }

        case OO_PlusPlus:
        case OO_MinusMinus:
            return transformIncrementDecrementCall(E, Ctx);

        case OO_PlusEqual:
        case OO_MinusEqual:
        case OO_StarEqual:
        case OO_SlashEqual:
            return transformCompoundAssignmentCall(E, Ctx);

        default:
            return nullptr;
    }
}

bool ArithmeticOperatorTranslator::isArithmeticOperator(OverloadedOperatorKind Op) const {
    switch (Op) {
        case OO_Plus:         // + (binary and unary)
        case OO_Minus:        // - (binary and unary)
        case OO_Star:         // * (binary only, unary * is dereference)
        case OO_Slash:        // /
        case OO_Percent:      // %
        case OO_PlusPlus:     // ++ (prefix and postfix)
        case OO_MinusMinus:   // -- (prefix and postfix)
        case OO_PlusEqual:    // +=
        case OO_MinusEqual:   // -=
        case OO_StarEqual:    // *=
        case OO_SlashEqual:   // /=
            return true;
        default:
            return false;
    }
}

// ============================================================================
// Binary Operator Translators
// ============================================================================

FunctionDecl* ArithmeticOperatorTranslator::translateBinaryPlus(CXXMethodDecl* MD,
                                                                 ASTContext& Ctx,
                                                                 TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ArithmeticOperatorTranslator::translateBinaryMinus(CXXMethodDecl* MD,
                                                                  ASTContext& Ctx,
                                                                  TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ArithmeticOperatorTranslator::translateBinaryMultiply(CXXMethodDecl* MD,
                                                                     ASTContext& Ctx,
                                                                     TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ArithmeticOperatorTranslator::translateBinaryDivide(CXXMethodDecl* MD,
                                                                   ASTContext& Ctx,
                                                                   TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ArithmeticOperatorTranslator::translateBinaryModulo(CXXMethodDecl* MD,
                                                                   ASTContext& Ctx,
                                                                   TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

// ============================================================================
// Unary Operator Translators
// ============================================================================

FunctionDecl* ArithmeticOperatorTranslator::translateUnaryMinus(CXXMethodDecl* MD,
                                                                 ASTContext& Ctx,
                                                                 TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ArithmeticOperatorTranslator::translateUnaryPlus(CXXMethodDecl* MD,
                                                                ASTContext& Ctx,
                                                                TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

// ============================================================================
// Increment/Decrement Operator Translators
// ============================================================================

FunctionDecl* ArithmeticOperatorTranslator::translatePrefixIncrement(CXXMethodDecl* MD,
                                                                      ASTContext& Ctx,
                                                                      TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ArithmeticOperatorTranslator::translatePostfixIncrement(CXXMethodDecl* MD,
                                                                       ASTContext& Ctx,
                                                                       TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ArithmeticOperatorTranslator::translatePrefixDecrement(CXXMethodDecl* MD,
                                                                      ASTContext& Ctx,
                                                                      TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

FunctionDecl* ArithmeticOperatorTranslator::translatePostfixDecrement(CXXMethodDecl* MD,
                                                                       ASTContext& Ctx,
                                                                       TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

// ============================================================================
// Compound Assignment Operator Translators
// ============================================================================

FunctionDecl* ArithmeticOperatorTranslator::translateCompoundAssignment(CXXMethodDecl* MD,
                                                                         ASTContext& Ctx,
                                                                         TranslationUnitDecl* C_TU) {
    return findOrCreateFunction(MD, Ctx, C_TU);
}

// ============================================================================
// Call Site Transformation Helpers
// ============================================================================

CallExpr* ArithmeticOperatorTranslator::transformBinaryOpCall(CXXOperatorCallExpr* E,
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
        llvm::errs() << "Warning: C function not found for operator call\n";
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

CallExpr* ArithmeticOperatorTranslator::transformUnaryOpCall(CXXOperatorCallExpr* E,
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
        llvm::errs() << "Warning: C function not found for unary operator call\n";
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

CallExpr* ArithmeticOperatorTranslator::transformIncrementDecrementCall(CXXOperatorCallExpr* E,
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
        llvm::errs() << "Warning: C function not found for increment/decrement operator call\n";
        return nullptr;
    }

    FunctionDecl* CFn = it->second;

    // Prefix: args = [object]
    // Postfix: args = [object, dummy_int]
    SmallVector<Expr*, 2> Args;

    Expr* Object = E->getArg(0);
    Expr* ObjectAddr = m_builder.addrOf(Object);
    Args.push_back(ObjectAddr);

    // Postfix has dummy int parameter
    if (E->getNumArgs() > 1) {
        Args.push_back(E->getArg(1));
    }

    return m_builder.call(CFn, Args);
}

CallExpr* ArithmeticOperatorTranslator::transformCompoundAssignmentCall(CXXOperatorCallExpr* E,
                                                                         ASTContext& Ctx) {
    // Same as binary operator transformation
    return transformBinaryOpCall(E, Ctx);
}

// ============================================================================
// Utility Functions
// ============================================================================

std::string ArithmeticOperatorTranslator::generateOperatorName(const CXXMethodDecl* MD) {
    // Delegate to NameMangler for consistent naming
    return m_mangler.mangleMethodName(const_cast<CXXMethodDecl*>(MD));
}

FunctionDecl* ArithmeticOperatorTranslator::findOrCreateFunction(const CXXMethodDecl* MD,
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
    // Signature: RetType FnName(Class* this, params...)

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

    // Get return type
    QualType ReturnType = MD->getReturnType();

    // Convert reference return to pointer
    if (ReturnType->isReferenceType()) {
        ReturnType = Ctx.getPointerType(ReturnType->getPointeeType());
    }

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
        llvm::outs() << "Created C function for operator: " << FnName << "\n";
    }

    return CFn;
}

bool ArithmeticOperatorTranslator::isBinaryOperator(const CXXMethodDecl* MD) const {
    if (!MD) {
        return false;
    }

    // Binary operators have exactly 1 parameter (excluding 'this')
    // Unary operators have 0 parameters
    return MD->getNumParams() == 1;
}

bool ArithmeticOperatorTranslator::isPrefixOperator(const CXXMethodDecl* MD) const {
    if (!MD) {
        return false;
    }

    OverloadedOperatorKind Op = MD->getOverloadedOperator();
    if (Op != OO_PlusPlus && Op != OO_MinusMinus) {
        return false;
    }

    // Prefix: 0 parameters
    // Postfix: 1 parameter (dummy int)
    return MD->getNumParams() == 0;
}

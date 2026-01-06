/**
 * @file ConstexprEnhancementHandler.cpp
 * @brief Implementation of partial constexpr enhancement support (C++23)
 */

#include "ConstexprEnhancementHandler.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;

ConstexprEnhancementHandler::ConstexprEnhancementHandler(CNodeBuilder& Builder)
    : m_builder(Builder) {}

bool ConstexprEnhancementHandler::handleConstexprFunction(FunctionDecl* FD,
                                                          ASTContext& Ctx) {
    if (!FD || !FD->isConstexpr()) {
        return false;
    }

    // Determine strategy
    ConstexprStrategy Strategy = determineStrategy(FD, Ctx);

    switch (Strategy) {
    case ConstexprStrategy::CompileTime:
        // Function can be evaluated at compile-time
        // Calls will be replaced with literals
        // No need to emit function definition
        return true;

    case ConstexprStrategy::Runtime:
        // Function too complex, emit as runtime function
        // This is handled by normal function translation
        emitFallbackWarning(FD, "Complex constexpr requires runtime evaluation");
        return true;

    case ConstexprStrategy::NotConstexpr:
        // Not constexpr
        return false;
    }

    return false;
}

ConstexprStrategy ConstexprEnhancementHandler::determineStrategy(
    FunctionDecl* FD, ASTContext& Ctx) {

    if (!FD || !FD->isConstexpr()) {
        return ConstexprStrategy::NotConstexpr;
    }

    // Check if function is simple enough for compile-time evaluation
    if (isSimpleReturnLiteral(FD)) {
        return ConstexprStrategy::CompileTime;
    }

    // Check if function has C++23-specific features
    if (detectC23ConstexprFeatures(FD)) {
        // C++23 features detected, likely needs runtime
        return ConstexprStrategy::Runtime;
    }

    // Try to evaluate the function
    Expr::EvalResult Result;
    if (FD->hasBody() && FD->getBody()) {
        // For functions with parameters, we can't evaluate without arguments
        if (FD->getNumParams() > 0) {
            return ConstexprStrategy::Runtime;
        }

        // Try compile-time evaluation
        if (attemptCompileTimeEval(FD, Result, Ctx)) {
            return ConstexprStrategy::CompileTime;
        }
    }

    // Default to runtime
    return ConstexprStrategy::Runtime;
}

bool ConstexprEnhancementHandler::tryEvaluateCall(CallExpr* Call,
                                                  ASTContext& Ctx) {
    if (!Call) {
        return false;
    }

    // Get callee function
    FunctionDecl* Callee = Call->getDirectCallee();
    if (!Callee || !Callee->isConstexpr()) {
        return false;
    }

    // Check if all arguments are literals
    for (unsigned i = 0; i < Call->getNumArgs(); i++) {
        Expr* Arg = Call->getArg(i);
        if (!Arg->isConstantInitializer(Ctx, false)) {
            return false;
        }
    }

    // Try to evaluate the call
    Expr::EvalResult Result;
    if (Call->EvaluateAsRValue(Result, Ctx)) {
        // Success - could replace call with literal
        // For now, just return true to indicate it's evaluable
        return true;
    }

    return false;
}

bool ConstexprEnhancementHandler::detectC23ConstexprFeatures(FunctionDecl* FD) {
    if (!FD) {
        return false;
    }

    // Check return type
    QualType ReturnType = FD->getReturnType();

    // C++23 allows non-literal types in constexpr
    // For simplicity, check if return type is a class type
    if (ReturnType->isClassType() || ReturnType->isStructureType()) {
        // Might be using C++23 non-literal types
        return true;
    }

    // Check for static variables with non-literal types
    if (FD->hasBody()) {
        // Would need to traverse body to find static variables
        // For now, assume no C++23 features if we get here
    }

    return false;
}

bool ConstexprEnhancementHandler::attemptCompileTimeEval(
    FunctionDecl* FD, Expr::EvalResult& Result, ASTContext& Ctx) {

    if (!FD || !FD->hasBody()) {
        return false;
    }

    Stmt* Body = FD->getBody();
    if (!Body) {
        return false;
    }

    // For simple functions, extract the return expression
    if (auto* CS = dyn_cast<CompoundStmt>(Body)) {
        if (CS->size() == 1) {
            if (auto* RS = dyn_cast<ReturnStmt>(*CS->body_begin())) {
                if (Expr* RetVal = RS->getRetValue()) {
                    // Try to evaluate the return expression
                    return RetVal->EvaluateAsRValue(Result, Ctx);
                }
            }
        }
    } else if (auto* RS = dyn_cast<ReturnStmt>(Body)) {
        // Direct return statement
        if (Expr* RetVal = RS->getRetValue()) {
            return RetVal->EvaluateAsRValue(Result, Ctx);
        }
    }

    return false;
}

bool ConstexprEnhancementHandler::isSimpleReturnLiteral(FunctionDecl* FD) {
    if (!FD || !FD->hasBody()) {
        return false;
    }

    Stmt* Body = FD->getBody();
    if (!Body) {
        return false;
    }

    // Check if body is a single return statement
    CompoundStmt* CS = dyn_cast<CompoundStmt>(Body);
    if (CS && CS->size() == 1) {
        if (auto* RS = dyn_cast<ReturnStmt>(*CS->body_begin())) {
            if (Expr* RetVal = RS->getRetValue()) {
                return isLiteralOnly(RetVal);
            }
        }
    } else if (auto* RS = dyn_cast<ReturnStmt>(Body)) {
        if (Expr* RetVal = RS->getRetValue()) {
            return isLiteralOnly(RetVal);
        }
    }

    return false;
}

bool ConstexprEnhancementHandler::isLiteralOnly(Stmt* S) {
    if (!S) {
        return false;
    }

    // Check for literal types
    if (isa<IntegerLiteral>(S) ||
        isa<FloatingLiteral>(S) ||
        isa<StringLiteral>(S) ||
        isa<CharacterLiteral>(S) ||
        isa<CXXBoolLiteralExpr>(S) ||
        isa<CXXNullPtrLiteralExpr>(S)) {
        return true;
    }

    // UnaryOperator with literal (e.g., -42)
    if (auto* UO = dyn_cast<UnaryOperator>(S)) {
        return isLiteralOnly(UO->getSubExpr());
    }

    // BinaryOperator with literals (e.g., 1 + 2)
    if (auto* BO = dyn_cast<BinaryOperator>(S)) {
        return isLiteralOnly(BO->getLHS()) && isLiteralOnly(BO->getRHS());
    }

    // Parenthesized expression
    if (auto* PE = dyn_cast<ParenExpr>(S)) {
        return isLiteralOnly(PE->getSubExpr());
    }

    // ImplicitCastExpr (type conversions)
    if (auto* ICE = dyn_cast<ImplicitCastExpr>(S)) {
        return isLiteralOnly(ICE->getSubExpr());
    }

    // MaterializeTemporaryExpr
    if (auto* MTE = dyn_cast<MaterializeTemporaryExpr>(S)) {
        return isLiteralOnly(MTE->getSubExpr());
    }

    // Not a literal expression
    return false;
}

void ConstexprEnhancementHandler::emitFallbackWarning(FunctionDecl* FD,
                                                      const std::string& Reason) {
    // Emit warning to stderr (or logging system)
    llvm::errs() << "Warning: constexpr function '"
                 << FD->getNameAsString()
                 << "' will be evaluated at runtime: "
                 << Reason << "\n";
}

Expr* ConstexprEnhancementHandler::createLiteralFromAPValue(
    CallExpr* Call, const APValue& Result, ASTContext& Ctx) {

    if (!Call) {
        return nullptr;
    }

    QualType ResultType = Call->getType();

    // Handle integer values
    if (Result.isInt()) {
        return IntegerLiteral::Create(
            Ctx, Result.getInt(), ResultType, SourceLocation());
    }

    // Handle floating point values
    if (Result.isFloat()) {
        return FloatingLiteral::Create(
            Ctx, Result.getFloat(), false, ResultType, SourceLocation());
    }

    // Handle null pointer
    if (Result.isNullPointer()) {
        return IntegerLiteral::Create(
            Ctx, llvm::APInt(32, 0), Ctx.IntTy, SourceLocation());
    }

    // Other types not supported yet
    return nullptr;
}

/**
 * @file StdMoveTranslator.cpp
 * @brief Implementation of std::move() Translation (Story #132)
 */

#include "../include/StdMoveTranslator.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include "clang/AST/ParentMapContext.h"
#include <sstream>

using namespace clang;

StdMoveTranslator::StdMoveTranslator(ASTContext& Context)
    : Context(Context) {}

bool StdMoveTranslator::isStdMoveCall(const CallExpr* Call) const {
    if (!Call) {
        return false;
    }

    const FunctionDecl* Callee = Call->getDirectCallee();
    if (!Callee) {
        return false;
    }

    // Check if function name is "move" in std namespace
    std::string name = Callee->getQualifiedNameAsString();
    return name == "std::move";
}

StdMoveTranslator::MoveContext StdMoveTranslator::analyzeMoveContext(const CallExpr* MoveCall) {
    if (!MoveCall) {
        return MoveContext::Construction;
    }

    // Get parent nodes to determine context
    auto& ParentMap = Context.getParentMapContext();
    auto Parents = ParentMap.getParents(*MoveCall);

    if (Parents.empty()) {
        return MoveContext::Construction;
    }

    // Traverse up the AST to find the usage context
    const Stmt* ParentStmt = Parents[0].get<Stmt>();
    if (!ParentStmt) {
        // Check if parent is a VarDecl (initialization context)
        const Decl* ParentDecl = Parents[0].get<Decl>();
        if (ParentDecl && isa<VarDecl>(ParentDecl)) {
            return MoveContext::Construction;
        }
        return MoveContext::Construction;
    }

    // Check if parent is a variable declaration (construction context)
    // Pattern: Buffer b2 = std::move(b1);
    auto DeclParents = ParentMap.getParents(*ParentStmt);
    if (!DeclParents.empty()) {
        const Decl* GrandParentDecl = DeclParents[0].get<Decl>();
        if (GrandParentDecl && isa<VarDecl>(GrandParentDecl)) {
            return MoveContext::Construction;
        }
    }

    // Check if parent is a binary operator (assignment context)
    // Pattern: b3 = std::move(b2);
    if (const BinaryOperator* BinOp = dyn_cast<BinaryOperator>(ParentStmt)) {
        if (BinOp->getOpcode() == BO_Assign) {
            return MoveContext::Assignment;
        }
    }

    // Check if parent is a CXXOperatorCallExpr for operator=
    if (const CXXOperatorCallExpr* OpCall = dyn_cast<CXXOperatorCallExpr>(ParentStmt)) {
        if (OpCall->getOperator() == OO_Equal) {
            return MoveContext::Assignment;
        }
    }

    // Check if parent is a return statement
    // Pattern: return std::move(local);
    if (isa<ReturnStmt>(ParentStmt)) {
        return MoveContext::Return;
    }

    // Check if we need to look further up for return statement
    if (!DeclParents.empty()) {
        const Stmt* GrandParent = DeclParents[0].get<Stmt>();
        if (GrandParent && isa<ReturnStmt>(GrandParent)) {
            return MoveContext::Return;
        }
    }

    // Check if parent is a CallExpr (function argument context)
    // Pattern: func(std::move(obj));
    // The parent would be MaterializeTemporaryExpr or ImplicitCastExpr
    // We need to look for CallExpr ancestor
    const Stmt* Current = ParentStmt;
    for (int depth = 0; depth < 5; ++depth) {
        auto CurrentParents = ParentMap.getParents(*Current);
        if (CurrentParents.empty()) break;

        const Stmt* NextParent = CurrentParents[0].get<Stmt>();
        if (!NextParent) break;

        if (const CallExpr* ParentCall = dyn_cast<CallExpr>(NextParent)) {
            // Check if MoveCall is one of the arguments
            for (unsigned i = 0; i < ParentCall->getNumArgs(); ++i) {
                // Traverse down through implicit nodes to find our MoveCall
                const Expr* Arg = ParentCall->getArg(i)->IgnoreImplicit();
                if (Arg == MoveCall ||
                    (isa<CXXConstructExpr>(Arg) &&
                     dyn_cast<CXXConstructExpr>(Arg)->getArg(0)->IgnoreImplicit() == MoveCall)) {
                    return MoveContext::Argument;
                }
            }
        }

        Current = NextParent;
    }

    // Default to construction if we can't determine
    return MoveContext::Construction;
}

std::string StdMoveTranslator::translateStdMove(const CallExpr* MoveCall, MoveContext Context) {
    if (!MoveCall || !isStdMoveCall(MoveCall)) {
        return "";
    }

    // Dispatch to appropriate generation method based on context
    switch (Context) {
        case MoveContext::Construction:
            return generateConstructionCode(MoveCall);
        case MoveContext::Assignment:
            return generateAssignmentCode(MoveCall);
        case MoveContext::Argument:
            return generateArgumentCode(MoveCall);
        case MoveContext::Return:
            return generateReturnCode(MoveCall);
        default:
            return generateConstructionCode(MoveCall);
    }
}

const Expr* StdMoveTranslator::getMovedArgument(const CallExpr* MoveCall) const {
    if (!MoveCall || MoveCall->getNumArgs() == 0) {
        return nullptr;
    }

    // std::move() takes one argument
    return MoveCall->getArg(0);
}

std::string StdMoveTranslator::getTypeName(const Expr* E) const {
    if (!E) {
        return "";
    }

    // Get the type of the expression
    QualType Type = E->getType();

    // Remove reference
    if (Type->isReferenceType()) {
        Type = Type.getNonReferenceType();
    }

    // Remove const/volatile qualifiers
    Type = Type.getUnqualifiedType();

    // Get the type as string
    std::string TypeStr = Type.getAsString();

    // Extract class name if it's a class type
    if (const RecordType* RT = Type->getAs<RecordType>()) {
        if (const RecordDecl* RD = RT->getDecl()) {
            return RD->getNameAsString();
        }
    }

    // For simple types, return the type string
    // Remove "class " or "struct " prefix if present
    if (TypeStr.find("class ") == 0) {
        return TypeStr.substr(6);
    }
    if (TypeStr.find("struct ") == 0) {
        return TypeStr.substr(7);
    }

    return TypeStr;
}

std::string StdMoveTranslator::getVariableName(const Expr* E) const {
    if (!E) {
        return "";
    }

    // Remove implicit casts and parentheses
    E = E->IgnoreImpCasts();
    E = E->IgnoreParens();

    // Check if it's a DeclRefExpr (variable reference)
    if (const DeclRefExpr* DRE = dyn_cast<DeclRefExpr>(E)) {
        if (const NamedDecl* ND = DRE->getDecl()) {
            return ND->getNameAsString();
        }
    }

    // Check if it's a member expression
    if (const MemberExpr* ME = dyn_cast<MemberExpr>(E)) {
        return ME->getMemberDecl()->getNameAsString();
    }

    return "";
}

std::string StdMoveTranslator::generateConstructionCode(const CallExpr* MoveCall) {
    const Expr* Arg = getMovedArgument(MoveCall);
    if (!Arg) {
        return "";
    }

    std::string typeName = getTypeName(Arg);
    std::string varName = getVariableName(Arg);

    std::ostringstream code;
    code << typeName << "_move_construct";

    return code.str();
}

std::string StdMoveTranslator::generateAssignmentCode(const CallExpr* MoveCall) {
    const Expr* Arg = getMovedArgument(MoveCall);
    if (!Arg) {
        return "";
    }

    std::string typeName = getTypeName(Arg);
    std::string varName = getVariableName(Arg);

    std::ostringstream code;
    code << typeName << "_move_assign";

    return code.str();
}

std::string StdMoveTranslator::generateArgumentCode(const CallExpr* MoveCall) {
    const Expr* Arg = getMovedArgument(MoveCall);
    if (!Arg) {
        return "";
    }

    std::string typeName = getTypeName(Arg);
    std::string varName = getVariableName(Arg);

    std::ostringstream code;

    // Generate temporary variable and move construction
    code << typeName << " __arg_temp__;\n";
    code << "    " << typeName << "_move_construct(&__arg_temp__, &" << varName << ")";

    return code.str();
}

std::string StdMoveTranslator::generateReturnCode(const CallExpr* MoveCall) {
    const Expr* Arg = getMovedArgument(MoveCall);
    if (!Arg) {
        return "";
    }

    std::string typeName = getTypeName(Arg);
    std::string varName = getVariableName(Arg);

    std::ostringstream code;

    // Generate temporary variable and move construction
    code << typeName << " __return_temp__;\n";
    code << "    " << typeName << "_move_construct(&__return_temp__, &" << varName << ");\n";
    code << "    return __return_temp__";

    return code.str();
}

const Stmt* StdMoveTranslator::findParentStmt(const Expr* E) const {
    if (!E) {
        return nullptr;
    }

    auto& ParentMap = Context.getParentMapContext();
    auto Parents = ParentMap.getParents(*E);

    if (Parents.empty()) {
        return nullptr;
    }

    return Parents[0].get<Stmt>();
}

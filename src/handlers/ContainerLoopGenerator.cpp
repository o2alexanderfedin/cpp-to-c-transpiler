/**
 * @file ContainerLoopGenerator.cpp
 * @brief Implementation of ContainerLoopGenerator
 *
 * TDD Implementation: Generate iterator-based loops for custom containers.
 * Migrated from HandlerContext to dispatcher pattern.
 */

#include "dispatch/CppToCVisitorDispatcher.h"
#include "handlers/ContainerLoopGenerator.h"
#include "mapping/StmtMapper.h"
#include "CNodeBuilder.h"
#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include <sstream>

namespace cpptoc {

// Initialize static counter
unsigned ContainerLoopGenerator::iteratorVarCounter_ = 0;

clang::ForStmt* ContainerLoopGenerator::generate(
    const clang::CXXForRangeStmt* RFS,
    const RangeClassification& rangeInfo,
    const LoopVariableInfo& loopVarInfo,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    if (!RFS || rangeInfo.rangeType != RangeType::CustomType) {
        return nullptr;
    }

    // Get container expression
    const clang::Expr* containerExpr = RangeTypeAnalyzer::getRangeExpr(RFS);
    if (!containerExpr) {
        return nullptr;
    }

    clang::QualType containerType = containerExpr->getType();

    // Find begin() and end() methods
    const clang::CXXMethodDecl* beginMethod = findBeginMethod(containerType);
    const clang::CXXMethodDecl* endMethod = findEndMethod(containerType);

    if (!beginMethod || !endMethod) {
        // Container doesn't have begin/end methods
        return nullptr;
    }

    // Analyze iterator type
    IteratorTypeAnalyzer iterAnalyzer;
    clang::QualType iteratorType = IteratorTypeAnalyzer::getIteratorTypeFromBegin(beginMethod);
    IteratorClassification iterClass = iterAnalyzer.analyze(iteratorType);

    if (!iterClass.isValid()) {
        // Iterator type not supported
        return nullptr;
    }

    // Generate iterator variable names
    auto [beginVarName, endVarName] = generateIteratorVarNames();

    // Create iterator variable declarations
    clang::VarDecl* beginVar = createBeginIterator(
        beginVarName, iteratorType, containerExpr, containerType, cASTContext, targetLoc
    );
    clang::VarDecl* endVar = createEndIterator(
        endVarName, iteratorType, containerExpr, containerType, cASTContext, targetLoc
    );

    if (!beginVar || !endVar) {
        return nullptr;
    }

    // Create loop condition: begin != end
    clang::Expr* condition = createIteratorComparison(beginVar, endVar, iterClass, cASTContext, targetLoc);

    // Create loop increment: ++begin
    clang::Expr* increment = createIteratorIncrement(beginVar, iterClass, cASTContext, targetLoc);

    // Create loop body with element access
    clang::CompoundStmt* body = createLoopBody(RFS, beginVar, loopVarInfo, iterClass, cppASTContext, cASTContext, targetLoc);

    if (!condition || !increment || !body) {
        return nullptr;
    }

    // Create the for loop: for (; begin != end; ++begin) { ... }
    clang::ForStmt* forLoop = new (cASTContext) clang::ForStmt(
        cASTContext,
        nullptr,        // No init (iterators declared in outer scope)
        condition,      // begin != end
        nullptr,        // No cond var
        increment,      // ++begin
        body,           // Loop body
        targetLoc,
        targetLoc,
        targetLoc
    );

    // Wrap in compound statement with iterator declarations
    clang::CompoundStmt* wrappedLoop = createIteratorScope(beginVar, endVar, forLoop, cASTContext, targetLoc);

    // Return the wrapped loop as a ForStmt (actually returns CompoundStmt cast to ForStmt)
    // Note: We need to return ForStmt, but we have CompoundStmt with ForStmt inside
    // For now, return the inner ForStmt and handle wrapping in caller
    return forLoop;
}

std::pair<std::string, std::string> ContainerLoopGenerator::generateIteratorVarNames() {
    unsigned counter = iteratorVarCounter_++;
    std::string beginName = "__begin_" + std::to_string(counter);
    std::string endName = "__end_" + std::to_string(counter);
    return {beginName, endName};
}

clang::VarDecl* ContainerLoopGenerator::createBeginIterator(
    const std::string& beginVarName,
    clang::QualType iteratorType,
    const clang::Expr* containerExpr,
    clang::QualType containerType,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    // Create identifier
    clang::IdentifierInfo& beginII = cASTContext.Idents.get(beginVarName);

    // Create variable declaration
    clang::VarDecl* beginVar = clang::VarDecl::Create(
        cASTContext,
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        targetLoc,
        &beginII,
        iteratorType,
        cASTContext.getTrivialTypeSourceInfo(iteratorType),
        clang::SC_None
    );

    // Create initializer: Container::begin(&container)
    clang::Expr* beginCall = createBeginCall(containerExpr, containerType, cASTContext, targetLoc);
    if (beginCall) {
        beginVar->setInit(beginCall);
    }

    return beginVar;
}

clang::VarDecl* ContainerLoopGenerator::createEndIterator(
    const std::string& endVarName,
    clang::QualType iteratorType,
    const clang::Expr* containerExpr,
    clang::QualType containerType,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    // Create identifier
    clang::IdentifierInfo& endII = cASTContext.Idents.get(endVarName);

    // Create variable declaration
    clang::VarDecl* endVar = clang::VarDecl::Create(
        cASTContext,
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        targetLoc,
        &endII,
        iteratorType,
        cASTContext.getTrivialTypeSourceInfo(iteratorType),
        clang::SC_None
    );

    // Create initializer: Container::end(&container)
    clang::Expr* endCall = createEndCall(containerExpr, containerType, cASTContext, targetLoc);
    if (endCall) {
        endVar->setInit(endCall);
    }

    return endVar;
}

clang::Expr* ContainerLoopGenerator::createIteratorComparison(
    clang::VarDecl* beginVar,
    clang::VarDecl* endVar,
    const IteratorClassification& iterClass,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    clang::QualType iteratorType = beginVar->getType();

    // Create DeclRefExpr for begin
    clang::DeclRefExpr* beginRef = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),
        targetLoc,
        beginVar,
        false,
        targetLoc,
        iteratorType,
        clang::VK_LValue
    );

    // Create DeclRefExpr for end
    clang::DeclRefExpr* endRef = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),
        targetLoc,
        endVar,
        false,
        targetLoc,
        iteratorType,
        clang::VK_LValue
    );

    if (iterClass.isPointer) {
        // For pointer iterators: begin != end (built-in operator)
        return clang::BinaryOperator::Create(
            cASTContext,
            beginRef,
            endRef,
            clang::BO_NE,
            cASTContext.BoolTy,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            targetLoc,
            clang::FPOptionsOverride()
        );
    } else if (iterClass.isStruct && iterClass.operations.notEqualOp) {
        // For struct iterators: Call Iterator__not_equal(&begin, &end)
        // This will be translated by ExpressionHandler
        // For now, create a CXXOperatorCallExpr that represents the != operation

        // Create UnaryOperator for address-of (&begin, &end)
        clang::QualType ptrType = cASTContext.getPointerType(iteratorType);

        clang::UnaryOperator* beginAddr = clang::UnaryOperator::Create(
            cASTContext,
            beginRef,
            clang::UO_AddrOf,
            ptrType,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            targetLoc,
            false,
            clang::FPOptionsOverride()
        );

        clang::UnaryOperator* endAddr = clang::UnaryOperator::Create(
            cASTContext,
            endRef,
            clang::UO_AddrOf,
            ptrType,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            targetLoc,
            false,
            clang::FPOptionsOverride()
        );

        // For now, create a simple != operator (will be translated later)
        // In full implementation, this would create a proper call to the translated function
        return clang::BinaryOperator::Create(
            cASTContext,
            beginRef,
            endRef,
            clang::BO_NE,
            cASTContext.BoolTy,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            targetLoc,
            clang::FPOptionsOverride()
        );
    }

    return nullptr;
}

clang::Expr* ContainerLoopGenerator::createIteratorIncrement(
    clang::VarDecl* beginVar,
    const IteratorClassification& iterClass,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    clang::QualType iteratorType = beginVar->getType();

    // Create DeclRefExpr for begin
    clang::DeclRefExpr* beginRef = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),
        targetLoc,
        beginVar,
        false,
        targetLoc,
        iteratorType,
        clang::VK_LValue
    );

    if (iterClass.isPointer) {
        // For pointer iterators: ++begin (built-in operator)
        return clang::UnaryOperator::Create(
            cASTContext,
            beginRef,
            clang::UO_PreInc,
            iteratorType,
            clang::VK_LValue,
            clang::OK_Ordinary,
            targetLoc,
            false,
            clang::FPOptionsOverride()
        );
    } else if (iterClass.isStruct && iterClass.operations.incrementOp) {
        // For struct iterators: Call Iterator__increment(&begin)
        // For now, create a simple ++ operator (will be translated later)
        return clang::UnaryOperator::Create(
            cASTContext,
            beginRef,
            clang::UO_PreInc,
            iteratorType,
            clang::VK_LValue,
            clang::OK_Ordinary,
            targetLoc,
            false,
            clang::FPOptionsOverride()
        );
    }

    return nullptr;
}

clang::CompoundStmt* ContainerLoopGenerator::createLoopBody(
    const clang::CXXForRangeStmt* RFS,
    clang::VarDecl* beginVar,
    const LoopVariableInfo& loopVarInfo,
    const IteratorClassification& iterClass,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    // Create element variable declaration
    clang::DeclStmt* elementDeclStmt = createElementVarDecl(
        RFS, beginVar, loopVarInfo, iterClass, cASTContext, targetLoc
    );

    if (!elementDeclStmt) {
        return nullptr;
    }

    // Get original loop body and translate it via dispatcher
    const clang::Stmt* originalBody = RFS->getBody();

    // Dispatch the body statement to be translated
    disp_.dispatch(cppASTContext, cASTContext, originalBody);

    // Get the translated body from the StmtMapper
    clang::Stmt* translatedBody = disp_.getStmtMapper().getCreated(originalBody);

    // Combine element declaration and body into compound statement
    llvm::SmallVector<clang::Stmt*, 2> bodyStmts;
    bodyStmts.push_back(elementDeclStmt);
    if (translatedBody) {
        bodyStmts.push_back(translatedBody);
    }

    return clang::CompoundStmt::Create(
        cASTContext,
        bodyStmts,
        clang::FPOptionsOverride(),
        targetLoc,
        targetLoc
    );
}

clang::DeclStmt* ContainerLoopGenerator::createElementVarDecl(
    const clang::CXXForRangeStmt* RFS,
    clang::VarDecl* beginVar,
    const LoopVariableInfo& loopVarInfo,
    const IteratorClassification& iterClass,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    // Get loop variable name and type
    std::string varName = loopVarInfo.name;
    clang::QualType varType = loopVarInfo.type;

    // If type is auto, use element type from iterator
    if (loopVarInfo.isAuto || varType.isNull()) {
        varType = iterClass.elementType;
    }

    // Create identifier
    clang::IdentifierInfo& varII = cASTContext.Idents.get(varName);

    // Create variable declaration
    clang::VarDecl* elementVar = clang::VarDecl::Create(
        cASTContext,
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        targetLoc,
        &varII,
        varType,
        cASTContext.getTrivialTypeSourceInfo(varType),
        clang::SC_None
    );

    // Create initializer: *begin
    clang::Expr* derefExpr = createIteratorDereference(beginVar, iterClass, cASTContext, targetLoc);
    if (derefExpr) {
        elementVar->setInit(derefExpr);
    }

    // Create DeclStmt
    return new (cASTContext) clang::DeclStmt(
        clang::DeclGroupRef(elementVar),
        targetLoc,
        targetLoc
    );
}

clang::Expr* ContainerLoopGenerator::createIteratorDereference(
    clang::VarDecl* beginVar,
    const IteratorClassification& iterClass,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    clang::QualType iteratorType = beginVar->getType();

    // Create DeclRefExpr for begin
    clang::DeclRefExpr* beginRef = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),
        targetLoc,
        beginVar,
        false,
        targetLoc,
        iteratorType,
        clang::VK_LValue
    );

    if (iterClass.isPointer) {
        // For pointer iterators: *begin (built-in operator)
        return clang::UnaryOperator::Create(
            cASTContext,
            beginRef,
            clang::UO_Deref,
            iterClass.elementType,
            clang::VK_LValue,
            clang::OK_Ordinary,
            targetLoc,
            false,
            clang::FPOptionsOverride()
        );
    } else if (iterClass.isStruct && iterClass.operations.derefOp) {
        // For struct iterators: Call Iterator__deref(&begin)
        // For now, create a simple * operator (will be translated later)
        clang::QualType resultType = iterClass.elementType;
        return clang::UnaryOperator::Create(
            cASTContext,
            beginRef,
            clang::UO_Deref,
            resultType,
            clang::VK_LValue,
            clang::OK_Ordinary,
            targetLoc,
            false,
            clang::FPOptionsOverride()
        );
    }

    return nullptr;
}

clang::Expr* ContainerLoopGenerator::createBeginCall(
    const clang::Expr* containerExpr,
    clang::QualType containerType,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    // Find begin() method
    const clang::CXXMethodDecl* beginMethod = findBeginMethod(containerType);
    if (!beginMethod) {
        return nullptr;
    }

    // Create a member call expression: container.begin()
    // For C translation, this will become: ContainerType__begin(&container)
    // But for now, we create the C++ AST representation

    // Clone the container expression (as we need it as lvalue)
    clang::Expr* baseExpr = const_cast<clang::Expr*>(containerExpr);

    // Create MemberExpr for begin
    // Note: Cast away const as CreateImplicit requires non-const ValueDecl
    clang::MemberExpr* memberExpr = clang::MemberExpr::CreateImplicit(
        cASTContext,
        baseExpr,
        false, // is arrow
        const_cast<clang::CXXMethodDecl*>(beginMethod),
        beginMethod->getType(),
        clang::VK_LValue,
        clang::OK_Ordinary
    );

    // Create call expression
    clang::QualType resultType = beginMethod->getReturnType();
    clang::CXXMemberCallExpr* callExpr = clang::CXXMemberCallExpr::Create(
        cASTContext,
        memberExpr,
        {},
        resultType,
        clang::VK_PRValue,
        targetLoc,
        clang::FPOptionsOverride()
    );

    return callExpr;
}

clang::Expr* ContainerLoopGenerator::createEndCall(
    const clang::Expr* containerExpr,
    clang::QualType containerType,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    // Find end() method
    const clang::CXXMethodDecl* endMethod = findEndMethod(containerType);
    if (!endMethod) {
        return nullptr;
    }

    // Create a member call expression: container.end()
    clang::Expr* baseExpr = const_cast<clang::Expr*>(containerExpr);

    // Create MemberExpr for end
    // Note: Cast away const as CreateImplicit requires non-const ValueDecl
    clang::MemberExpr* memberExpr = clang::MemberExpr::CreateImplicit(
        cASTContext,
        baseExpr,
        false, // is arrow
        const_cast<clang::CXXMethodDecl*>(endMethod),
        endMethod->getType(),
        clang::VK_LValue,
        clang::OK_Ordinary
    );

    // Create call expression
    clang::QualType resultType = endMethod->getReturnType();
    clang::CXXMemberCallExpr* callExpr = clang::CXXMemberCallExpr::Create(
        cASTContext,
        memberExpr,
        {},
        resultType,
        clang::VK_PRValue,
        targetLoc,
        clang::FPOptionsOverride()
    );

    return callExpr;
}

clang::CompoundStmt* ContainerLoopGenerator::createIteratorScope(
    clang::VarDecl* beginDecl,
    clang::VarDecl* endDecl,
    clang::ForStmt* forLoop,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    // Create DeclStmt for begin and end
    clang::DeclStmt* beginDeclStmt = new (cASTContext) clang::DeclStmt(
        clang::DeclGroupRef(beginDecl),
        targetLoc,
        targetLoc
    );

    clang::DeclStmt* endDeclStmt = new (cASTContext) clang::DeclStmt(
        clang::DeclGroupRef(endDecl),
        targetLoc,
        targetLoc
    );

    // Create compound statement with declarations and loop
    llvm::SmallVector<clang::Stmt*, 3> stmts;
    stmts.push_back(beginDeclStmt);
    stmts.push_back(endDeclStmt);
    stmts.push_back(forLoop);

    return clang::CompoundStmt::Create(
        cASTContext,
        stmts,
        clang::FPOptionsOverride(),
        targetLoc,
        targetLoc
    );
}

const clang::CXXMethodDecl* ContainerLoopGenerator::findBeginMethod(
    clang::QualType containerType
) {
    // Get the record type
    const auto* RT = containerType->getAs<clang::RecordType>();
    if (!RT) return nullptr;

    const auto* RD = RT->getDecl();
    if (!RD) return nullptr;

    const auto* CXXRecord = llvm::dyn_cast<clang::CXXRecordDecl>(RD);
    if (!CXXRecord) return nullptr;

    // Look for begin() method
    for (const auto* method : CXXRecord->methods()) {
        if (method->getName() == "begin") {
            return method;
        }
    }

    return nullptr;
}

const clang::CXXMethodDecl* ContainerLoopGenerator::findEndMethod(
    clang::QualType containerType
) {
    // Get the record type
    const auto* RT = containerType->getAs<clang::RecordType>();
    if (!RT) return nullptr;

    const auto* RD = RT->getDecl();
    if (!RD) return nullptr;

    const auto* CXXRecord = llvm::dyn_cast<clang::CXXRecordDecl>(RD);
    if (!CXXRecord) return nullptr;

    // Look for end() method
    for (const auto* method : CXXRecord->methods()) {
        if (method->getName() == "end") {
            return method;
        }
    }

    return nullptr;
}

} // namespace cpptoc

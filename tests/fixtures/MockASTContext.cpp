/**
 * @file MockASTContext.cpp
 * @brief Implementation of MockASTContext test fixture
 *
 * Simplified implementation that leverages CNodeBuilder.
 * We don't need a fully functional ASTContext for testing - we just need
 * to be able to create AST nodes. CNodeBuilder already does this.
 */

#include "MockASTContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/Tooling/Tooling.h"
#include <sstream>

namespace cpptoc {
namespace test {

MockASTContext::MockASTContext() {
    // Create a minimal AST using clang::tooling helpers
    // This gives us a fully functional ASTContext
    std::string code = "int dummy;"; // Minimal valid C++ code
    std::unique_ptr<clang::ASTUnit> ast = clang::tooling::buildASTFromCode(code);

    if (!ast) {
        // Fallback: If buildASTFromCode fails, we're in trouble
        throw std::runtime_error("Failed to create ASTContext");
    }

    // Extract the ASTContext (we own it now through unique_ptr semantics)
    context_ = std::unique_ptr<clang::ASTContext>(&ast->getASTContext());

    // Release the ASTUnit without destroying the ASTContext
    // (This is a bit hacky but necessary for our test infrastructure)
    ast.release();
}

MockASTContext::~MockASTContext() {
    // Clean up owned nodes (AST context will clean up allocated nodes)
    ownedDecls_.clear();
    ownedStmts_.clear();
}

clang::QualType MockASTContext::parseType(const std::string& typeStr) {
    // Simple type parsing for common types
    if (typeStr == "void") {
        return context_->VoidTy;
    } else if (typeStr == "int") {
        return context_->IntTy;
    } else if (typeStr == "float") {
        return context_->FloatTy;
    } else if (typeStr == "double") {
        return context_->DoubleTy;
    } else if (typeStr == "char") {
        return context_->CharTy;
    } else if (typeStr == "bool") {
        return context_->BoolTy;
    }

    // Handle pointer types
    if (typeStr.back() == '*') {
        std::string baseType = typeStr.substr(0, typeStr.length() - 1);
        // Trim whitespace
        while (!baseType.empty() && baseType.back() == ' ') {
            baseType.pop_back();
        }
        return context_->getPointerType(parseType(baseType));
    }

    // Default to int for unknown types
    return context_->IntTy;
}

clang::ParmVarDecl* MockASTContext::createParameter(const std::string& paramStr) {
    // Parse "type name" format
    std::istringstream iss(paramStr);
    std::string typePart;
    std::string namePart;

    // Read type (may be multiple words like "const int")
    std::vector<std::string> parts;
    std::string word;
    while (iss >> word) {
        parts.push_back(word);
    }

    if (parts.empty()) {
        return nullptr;
    }

    // Last part is name, rest is type
    namePart = parts.back();
    parts.pop_back();

    // Reconstruct type string
    for (size_t i = 0; i < parts.size(); ++i) {
        if (i > 0) typePart += " ";
        typePart += parts[i];
    }

    if (typePart.empty()) {
        typePart = "int"; // Default type
    }

    clang::QualType paramType = parseType(typePart);
    clang::IdentifierInfo& II = context_->Idents.get(namePart);

    return clang::ParmVarDecl::Create(
        *context_,
        context_->getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        paramType,
        context_->getTrivialTypeSourceInfo(paramType),
        clang::SC_None,
        nullptr
    );
}

clang::FunctionDecl* MockASTContext::createFunction(
    const std::string& returnType,
    const std::string& name,
    const std::vector<std::string>& params,
    clang::Stmt* body
) {
    // Parse return type
    clang::QualType retType = parseType(returnType);

    // Create function declaration
    clang::IdentifierInfo& II = context_->Idents.get(name);
    clang::DeclarationName declName(&II);

    // Create parameter types for function type
    llvm::SmallVector<clang::QualType, 4> paramTypes;
    std::vector<clang::ParmVarDecl*> paramDecls;

    for (const auto& paramStr : params) {
        clang::ParmVarDecl* paramDecl = createParameter(paramStr);
        if (paramDecl) {
            paramTypes.push_back(paramDecl->getType());
            paramDecls.push_back(paramDecl);
        }
    }

    // Create function type
    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = context_->getFunctionType(retType, paramTypes, EPI);

    // Create function declaration
    clang::FunctionDecl* func = clang::FunctionDecl::Create(
        *context_,
        context_->getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        declName,
        funcType,
        context_->getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    // Set parameters
    func->setParams(paramDecls);

    // Set body if provided
    if (body) {
        func->setBody(body);
    }

    return func;
}

clang::VarDecl* MockASTContext::createVariable(
    const std::string& type,
    const std::string& name,
    clang::Expr* init
) {
    clang::QualType varType = parseType(type);
    clang::IdentifierInfo& II = context_->Idents.get(name);

    clang::VarDecl* var = clang::VarDecl::Create(
        *context_,
        context_->getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        varType,
        context_->getTrivialTypeSourceInfo(varType),
        clang::SC_None
    );

    if (init) {
        var->setInit(init);
    }

    return var;
}

clang::IntegerLiteral* MockASTContext::createIntLiteral(int value) {
    return clang::IntegerLiteral::Create(
        *context_,
        llvm::APInt(32, value),
        context_->IntTy,
        clang::SourceLocation()
    );
}

clang::FloatingLiteral* MockASTContext::createFloatLiteral(double value) {
    llvm::APFloat apValue(value);
    return clang::FloatingLiteral::Create(
        *context_,
        apValue,
        false, // isExact
        context_->DoubleTy,
        clang::SourceLocation()
    );
}

clang::BinaryOperator* MockASTContext::createBinaryOp(
    clang::BinaryOperatorKind op,
    clang::Expr* lhs,
    clang::Expr* rhs
) {
    clang::QualType resultType = lhs->getType();

    return clang::BinaryOperator::Create(
        *context_,
        lhs,
        rhs,
        op,
        resultType,
        clang::VK_PRValue,
        clang::OK_Ordinary,
        clang::SourceLocation(),
        clang::FPOptionsOverride()
    );
}

clang::DeclRefExpr* MockASTContext::createVarRef(clang::VarDecl* var) {
    return clang::DeclRefExpr::Create(
        *context_,
        clang::NestedNameSpecifierLoc(),
        clang::SourceLocation(),
        var,
        false, // refersToEnclosingVariableOrCapture
        clang::SourceLocation(),
        var->getType(),
        clang::VK_LValue
    );
}

clang::ReturnStmt* MockASTContext::createReturnStmt(clang::Expr* expr) {
    return clang::ReturnStmt::Create(
        *context_,
        clang::SourceLocation(),
        expr,
        nullptr // no NRVO candidate
    );
}

clang::CompoundStmt* MockASTContext::createCompoundStmt(
    const std::vector<clang::Stmt*>& stmts
) {
    return clang::CompoundStmt::Create(
        *context_,
        stmts,
        clang::FPOptionsOverride(),
        clang::SourceLocation(),
        clang::SourceLocation()
    );
}

} // namespace test
} // namespace cpptoc

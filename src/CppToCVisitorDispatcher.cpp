#include "CppToCVisitorDispatcher.h"
#include "PathMapper.h"

// ============================================================================
// Helper Methods
// ============================================================================

std::string CppToCVisitorDispatcher::getTargetPath(const clang::ASTContext& cppASTContext, const clang::Decl* D) const {
    // Delegate to PathMapper utility method
    return pathMapper.getTargetPathFromDeclLocation(cppASTContext, D);
}

// ============================================================================
// Core AST Node Handlers
// ============================================================================

// Declaration handlers
void CppToCVisitorDispatcher::addHandler(DeclPredicate predicate, DeclVisitor handler) {
    declHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::Decl* cppDecl) const {
    for (const auto& [predicate, handler] : declHandlers) {
        if (predicate(cppDecl)) {
            handler(*this, cppASTContext, cASTContext, cppDecl);
            return true;
        }
    }
    return false;
}

// Statement handlers
void CppToCVisitorDispatcher::addHandler(StmtPredicate predicate, StmtVisitor handler) {
    stmtHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::Stmt* cppStmt) const {
    for (const auto& [predicate, handler] : stmtHandlers) {
        if (predicate(cppStmt)) {
            handler(*this, cppASTContext, cASTContext, cppStmt);
            return true;
        }
    }
    return false;
}

// Expression handlers
void CppToCVisitorDispatcher::addHandler(ExprPredicate predicate, ExprVisitor handler) {
    exprHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::Expr* cppExpr) const {
    for (const auto& [predicate, handler] : exprHandlers) {
        if (predicate(cppExpr)) {
            handler(*this, cppASTContext, cASTContext, cppExpr);
            return true;
        }
    }
    return false;
}

// Type handlers
void CppToCVisitorDispatcher::addHandler(TypePredicate predicate, TypeVisitor handler) {
    typeHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::Type* cppType) const {
    for (const auto& [predicate, handler] : typeHandlers) {
        if (predicate(cppType)) {
            handler(*this, cppASTContext, cASTContext, cppType);
            return true;
        }
    }
    return false;
}

// ============================================================================
// Additional AST Node Handlers
// ============================================================================

// Attribute handlers
void CppToCVisitorDispatcher::addHandler(AttrPredicate predicate, AttrVisitor handler) {
    attrHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::Attr* attr) const {
    for (const auto& [predicate, handler] : attrHandlers) {
        if (predicate(attr)) {
            handler(*this, cppASTContext, cASTContext, attr);
            return true;
        }
    }
    return false;
}

// NestedNameSpecifier handlers
void CppToCVisitorDispatcher::addHandler(NestedNameSpecifierPredicate predicate, NestedNameSpecifierVisitor handler) {
    nestedNameSpecifierHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::NestedNameSpecifier* nns) const {
    for (const auto& [predicate, handler] : nestedNameSpecifierHandlers) {
        if (predicate(nns)) {
            handler(*this, cppASTContext, cASTContext, nns);
            return true;
        }
    }
    return false;
}

// TemplateArgument handlers
void CppToCVisitorDispatcher::addHandler(TemplateArgumentPredicate predicate, TemplateArgumentVisitor handler) {
    templateArgumentHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::TemplateArgument* arg) const {
    for (const auto& [predicate, handler] : templateArgumentHandlers) {
        if (predicate(arg)) {
            handler(*this, cppASTContext, cASTContext, arg);
            return true;
        }
    }
    return false;
}

// CXXCtorInitializer handlers
void CppToCVisitorDispatcher::addHandler(CXXCtorInitializerPredicate predicate, CXXCtorInitializerVisitor handler) {
    ctorInitializerHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::CXXCtorInitializer* init) const {
    for (const auto& [predicate, handler] : ctorInitializerHandlers) {
        if (predicate(init)) {
            handler(*this, cppASTContext, cASTContext, init);
            return true;
        }
    }
    return false;
}

// CXXBaseSpecifier handlers
void CppToCVisitorDispatcher::addHandler(CXXBaseSpecifierPredicate predicate, CXXBaseSpecifierVisitor handler) {
    baseSpecifierHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::CXXBaseSpecifier* base) const {
    for (const auto& [predicate, handler] : baseSpecifierHandlers) {
        if (predicate(base)) {
            handler(*this, cppASTContext, cASTContext, base);
            return true;
        }
    }
    return false;
}

// TypeLoc handlers
void CppToCVisitorDispatcher::addHandler(TypeLocPredicate predicate, TypeLocVisitor handler) {
    typeLocHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::TypeLoc* typeLoc) const {
    for (const auto& [predicate, handler] : typeLocHandlers) {
        if (predicate(typeLoc)) {
            handler(*this, cppASTContext, cASTContext, typeLoc);
            return true;
        }
    }
    return false;
}

// TemplateName handlers
void CppToCVisitorDispatcher::addHandler(TemplateNamePredicate predicate, TemplateNameVisitor handler) {
    templateNameHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::TemplateName* name) const {
    for (const auto& [predicate, handler] : templateNameHandlers) {
        if (predicate(name)) {
            handler(*this, cppASTContext, cASTContext, name);
            return true;
        }
    }
    return false;
}

// Comment handlers
void CppToCVisitorDispatcher::addHandler(CommentPredicate predicate, CommentVisitor handler) {
    commentHandlers.emplace_back(predicate, handler);
}

bool CppToCVisitorDispatcher::dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, clang::comments::Comment* comment) const {
    for (const auto& [predicate, handler] : commentHandlers) {
        if (predicate(comment)) {
            handler(*this, cppASTContext, cASTContext, comment);
            return true;
        }
    }
    return false;
}

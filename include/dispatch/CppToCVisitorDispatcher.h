/**
 * @file CppToCVisitorDispatcher.h
 * @brief Chain of Responsibility dispatcher for AST node handling
 *
 * Implements dispatcher pattern for routing Clang AST nodes to appropriate handlers
 * based on predicates. Part of refactoring CppToCVisitor into specialized handlers.
 *
 * Design Principles:
 * - SOLID: Single Responsibility (dispatch only, no translation logic)
 * - Chain of Responsibility: Sequential handler evaluation
 * - Open/Closed: Add handlers without modifying dispatcher
 */

#pragma once

#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Type.h"
#include "clang/AST/Attr.h"
#include "clang/AST/NestedNameSpecifier.h"
#include "clang/AST/TemplateBase.h"
#include "clang/AST/TypeLoc.h"
#include "clang/AST/TemplateName.h"
#include "clang/AST/Comment.h"
#include <functional>
#include <tuple>
#include <vector>

// Forward declarations
class TargetContext;

namespace cpptoc {
    class PathMapper;
    class DeclLocationMapper;
}

// Include mapper type aliases (now based on NodeMapper template)
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"

/**
 * @class CppToCVisitorDispatcher
 * @brief Dispatches Clang AST nodes to registered handlers
 *
 * This class implements the Chain of Responsibility pattern for AST node handling.
 * Handlers are evaluated in registration order until one matches.
 *
 * Example usage with recursive dispatch:
 * @code
 * CppToCVisitorDispatcher dispatcher;
 *
 * // Register a class handler that recursively dispatches methods
 * dispatcher.addHandler(
 *     // Predicate: Match CXXRecordDecl
 *     [](clang::Decl* d) { return llvm::isa<clang::CXXRecordDecl>(d); },
 *
 *     // Visitor: Translate class and recursively dispatch child nodes
 *     [](const CppToCVisitorDispatcher& disp, clang::ASTContext& cpp, clang::ASTContext& c, clang::Decl* d) {
 *         auto* classDecl = llvm::cast<clang::CXXRecordDecl>(d);
 *
 *         // Translate class to C struct
 *         // ...
 *
 *         // Recursively dispatch child methods
 *         for (auto* method : classDecl->methods()) {
 *             disp.dispatch(cpp, c, method);  // ← Recursive dispatch
 *         }
 *     }
 * );
 *
 * // Usage
 * dispatcher.dispatch(cppContext, cContext, someDecl);
 * @endcode
 */
class CppToCVisitorDispatcher
{
public:
    typedef std::function<bool(const clang::Decl*)> DeclPredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::Decl*)> DeclVisitor;

    typedef std::function<bool(const clang::Stmt*)> StmtPredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::Stmt*)> StmtVisitor;

    typedef std::function<bool(const clang::Expr*)> ExprPredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::Expr*)> ExprVisitor;

    typedef std::function<bool(const clang::Type*)> TypePredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::Type*)> TypeVisitor;

    typedef std::function<bool(const clang::Attr*)> AttrPredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::Attr*)> AttrVisitor;

    typedef std::function<bool(const clang::NestedNameSpecifier*)> NestedNameSpecifierPredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::NestedNameSpecifier*)> NestedNameSpecifierVisitor;

    typedef std::function<bool(const clang::TemplateArgument*)> TemplateArgumentPredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::TemplateArgument*)> TemplateArgumentVisitor;

    typedef std::function<bool(const clang::CXXCtorInitializer*)> CXXCtorInitializerPredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::CXXCtorInitializer*)> CXXCtorInitializerVisitor;

    typedef std::function<bool(const clang::CXXBaseSpecifier*)> CXXBaseSpecifierPredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::CXXBaseSpecifier*)> CXXBaseSpecifierVisitor;

    typedef std::function<bool(const clang::TypeLoc*)> TypeLocPredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::TypeLoc*)> TypeLocVisitor;

    typedef std::function<bool(const clang::TemplateName*)> TemplateNamePredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::TemplateName*)> TemplateNameVisitor;

    typedef std::function<bool(const clang::comments::Comment*)> CommentPredicate;
    typedef std::function<void(const CppToCVisitorDispatcher&, const clang::ASTContext&, clang::ASTContext&, const clang::comments::Comment*)> CommentVisitor;

private:
    // Core AST handler vectors
    std::vector<std::tuple<DeclPredicate, DeclVisitor>> declHandlers;
    std::vector<std::tuple<StmtPredicate, StmtVisitor>> stmtHandlers;
    std::vector<std::tuple<ExprPredicate, ExprVisitor>> exprHandlers;
    std::vector<std::tuple<TypePredicate, TypeVisitor>> typeHandlers;

    // Additional AST handler vectors
    std::vector<std::tuple<AttrPredicate, AttrVisitor>> attrHandlers;
    std::vector<std::tuple<NestedNameSpecifierPredicate, NestedNameSpecifierVisitor>> nestedNameSpecifierHandlers;
    std::vector<std::tuple<TemplateArgumentPredicate, TemplateArgumentVisitor>> templateArgumentHandlers;
    std::vector<std::tuple<CXXCtorInitializerPredicate, CXXCtorInitializerVisitor>> ctorInitializerHandlers;
    std::vector<std::tuple<CXXBaseSpecifierPredicate, CXXBaseSpecifierVisitor>> baseSpecifierHandlers;
    std::vector<std::tuple<TypeLocPredicate, TypeLocVisitor>> typeLocHandlers;
    std::vector<std::tuple<TemplateNamePredicate, TemplateNameVisitor>> templateNameHandlers;
    std::vector<std::tuple<CommentPredicate, CommentVisitor>> commentHandlers;

    // Path mapper for C++ source file → C target file mapping
    cpptoc::PathMapper& pathMapper;

    // Location mapper for extracting target paths from AST nodes
    cpptoc::DeclLocationMapper& declLocationMapper;

    // Declaration mapper for C++ → C declaration mappings
    cpptoc::DeclMapper& declMapper;

    // Type mapper for C++ → C type mappings
    cpptoc::TypeMapper& typeMapper;

    // Expression mapper for C++ → C expression mappings
    cpptoc::ExprMapper& exprMapper;

    // Statement mapper for C++ → C statement mappings
    cpptoc::StmtMapper& stmtMapper;

    // Target context for C AST creation (provides LocationMapper)
    TargetContext& targetContext;

    // Current target path context (which source file is currently being transpiled)
    // Mutable because handlers need to update context even when dispatcher is const
    mutable std::string currentTargetPath_;

public:
    /**
     * @brief Construct dispatcher with required dependencies
     * @param mapper PathMapper for source-to-target file mapping (required)
     * @param locMapper DeclLocationMapper for extracting paths from AST nodes (required)
     * @param dMapper DeclMapper for C++ → C declaration mappings (required)
     * @param tMapper TypeMapper for C++ → C type mappings (required)
     * @param eMapper ExprMapper for C++ → C expression mappings (required)
     * @param sMapper StmtMapper for C++ → C statement mappings (required)
     * @param tgtContext TargetContext for C AST creation (provides LocationMapper)
     */
    explicit CppToCVisitorDispatcher(
        cpptoc::PathMapper& mapper,
        cpptoc::DeclLocationMapper& locMapper,
        cpptoc::DeclMapper& dMapper,
        cpptoc::TypeMapper& tMapper,
        cpptoc::ExprMapper& eMapper,
        cpptoc::StmtMapper& sMapper,
        TargetContext& tgtContext
    ) : pathMapper(mapper), declLocationMapper(locMapper), declMapper(dMapper), typeMapper(tMapper), exprMapper(eMapper), stmtMapper(sMapper), targetContext(tgtContext) {}

    /**
     * @brief Get the path mapper
     * @return Reference to PathMapper
     */
    cpptoc::PathMapper& getPathMapper() const { return pathMapper; }

    /**
     * @brief Get the declaration mapper
     * @return Reference to DeclMapper
     */
    cpptoc::DeclMapper& getDeclMapper() const { return declMapper; }

    /**
     * @brief Get the type mapper
     * @return Reference to TypeMapper
     */
    cpptoc::TypeMapper& getTypeMapper() const { return typeMapper; }

    /**
     * @brief Get the expression mapper
     * @return Reference to ExprMapper
     */
    cpptoc::ExprMapper& getExprMapper() const { return exprMapper; }

    /**
     * @brief Get the statement mapper
     * @return Reference to StmtMapper
     */
    cpptoc::StmtMapper& getStmtMapper() const { return stmtMapper; }

    /**
     * @brief Get the target context
     * @return Reference to TargetContext
     */
    TargetContext& getTargetContext() const { return targetContext; }

    /**
     * @brief Helper: Get C target path for AST node's source file
     * @param cppASTContext C++ ASTContext containing SourceManager
     * @param D AST node to get file location from
     * @return C target file path (e.g., "/output/file.c")
     *
     * Common pattern for all handlers:
     * 1. Extract source file path from AST node's SourceLocation
     * 2. Map source path to target path via PathMapper
     * 3. Return target path
     *
     * This encapsulates the boilerplate that all handlers need.
     * More accurate than getMainFileID() - uses actual node location.
     */
    std::string getTargetPath(const clang::ASTContext& cppASTContext, const clang::Decl* D) const;

    /**
     * @brief Set the current target path (which source file is being transpiled)
     * @param targetPath Target file path for current source file
     *
     * Should be called at the start of processing each source file, so all declarations
     * encountered during that source file's processing get added to the correct C_TU.
     * Const-qualified because it modifies mutable context state (not logical constness).
     */
    void setCurrentTargetPath(const std::string& targetPath) const;

    /**
     * @brief Get the current target path (which source file is being transpiled)
     * @return Current target file path
     *
     * Returns the path set by setCurrentTargetPath(). All declarations encountered
     * during transpilation of the current source file should go to this C_TU.
     */
    std::string getCurrentTargetPath() const;

    /**
     * @brief Helper: Get target SourceLocation for AST node
     * @param cppASTContext C++ ASTContext containing SourceManager
     * @param D AST node to extract file location from (used as fallback if current path is empty)
     * @return clang::SourceLocation pointing to start of target file
     *
     * Encapsulates the common pattern used in all handlers:
     * 1. Get current target path or extract from AST node's location
     * 2. Lookup target file's starting location via LocationMapper
     * 3. Return the SourceLocation
     *
     * Usage:
     * @code
     * clang::SourceLocation targetLoc = disp.getTargetSourceLocation(cppASTContext, someNode);
     * clang::WhileStmt* cWhile = clang::WhileStmt::Create(
     *     cASTContext,
     *     nullptr,
     *     cCond,
     *     cBody,
     *     targetLoc,  // WhileLoc
     *     targetLoc,  // LParenLoc
     *     targetLoc   // RParenLoc
     * );
     * @endcode
     */
    clang::SourceLocation getTargetSourceLocation(const clang::ASTContext& cppASTContext, const clang::Decl* D) const;

    // Core AST node handlers
    void addHandler(DeclPredicate predicate, DeclVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::Decl* cppDecl) const;

    void addHandler(StmtPredicate predicate, StmtVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::Stmt* cppStmt) const;

    void addHandler(ExprPredicate predicate, ExprVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::Expr* cppExpr) const;

    void addHandler(TypePredicate predicate, TypeVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::Type* cppType) const;

    // Additional AST node handlers
    void addHandler(AttrPredicate predicate, AttrVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::Attr* attr) const;

    void addHandler(NestedNameSpecifierPredicate predicate, NestedNameSpecifierVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::NestedNameSpecifier* nns) const;

    void addHandler(TemplateArgumentPredicate predicate, TemplateArgumentVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::TemplateArgument* arg) const;

    void addHandler(CXXCtorInitializerPredicate predicate, CXXCtorInitializerVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::CXXCtorInitializer* init) const;

    void addHandler(CXXBaseSpecifierPredicate predicate, CXXBaseSpecifierVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::CXXBaseSpecifier* base) const;

    void addHandler(TypeLocPredicate predicate, TypeLocVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::TypeLoc* typeLoc) const;

    void addHandler(TemplateNamePredicate predicate, TemplateNameVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::TemplateName* name) const;

    void addHandler(CommentPredicate predicate, CommentVisitor handler);
    bool dispatch(const clang::ASTContext& cppASTContext, clang::ASTContext& cASTContext, const clang::comments::Comment* comment) const;
};

#ifndef HEADER_SEPARATOR_H
#define HEADER_SEPARATOR_H

#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <vector>

/// @brief Separates declarations into header and implementation lists
///
/// SOLID: Single Responsibility - only separates headers from implementation.
/// This class analyzes Clang AST declarations and routes them to either
/// the header file list (.h) or implementation file list (.c).
///
/// Routing Rules:
/// - RecordDecl (complete definitions) → header
/// - FunctionDecl declarations (no body) → header
/// - FunctionDecl definitions (with body) → impl + declaration in header
class HeaderSeparator : public clang::RecursiveASTVisitor<HeaderSeparator> {
public:
    /// @brief Analyze entire translation unit and populate declaration lists
    /// @param TU Translation unit to analyze
    void analyzeTranslationUnit(clang::TranslationUnitDecl *TU);

    /// @brief Get declarations that should go to header file (.h)
    /// @return Vector of declarations for header
    const std::vector<clang::Decl*>& getHeaderDecls() const { return headerDecls; }

    /// @brief Get declarations that should go to implementation file (.c)
    /// @return Vector of declarations for implementation
    const std::vector<clang::Decl*>& getImplDecls() const { return implDecls; }

    /// @brief Visitor method for struct/class declarations
    /// @param D RecordDecl to analyze
    /// @return true to continue traversal
    bool VisitRecordDecl(clang::RecordDecl *D);

    /// @brief Visitor method for function declarations
    /// @param D FunctionDecl to analyze
    /// @return true to continue traversal
    bool VisitFunctionDecl(clang::FunctionDecl *D);

private:
    std::vector<clang::Decl*> headerDecls;  ///< Declarations for .h file
    std::vector<clang::Decl*> implDecls;    ///< Declarations for .c file
};

#endif // HEADER_SEPARATOR_H

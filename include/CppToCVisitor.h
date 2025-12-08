#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ASTContext.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include <map>
#include <string>

// RecursiveASTVisitor that traverses C++ AST nodes
// Single Responsibility: Visit and identify AST nodes for translation
class CppToCVisitor : public clang::RecursiveASTVisitor<CppToCVisitor> {
  clang::ASTContext &Context;
  clang::CNodeBuilder &Builder;
  NameMangler Mangler;

  // Mapping: C++ class -> C struct (Story #15)
  std::map<clang::CXXRecordDecl*, clang::RecordDecl*> cppToCMap;

  // Mapping: C++ method -> C function (Story #16)
  std::map<clang::CXXMethodDecl*, clang::FunctionDecl*> methodToCFunc;

  // Mapping: C++ constructor -> C function (Story #17)
  std::map<clang::CXXConstructorDecl*, clang::FunctionDecl*> ctorMap;

  // Current translation context (Story #19)
  clang::ParmVarDecl *currentThisParam = nullptr;
  clang::CXXMethodDecl *currentMethod = nullptr;

public:
  explicit CppToCVisitor(clang::ASTContext &Context, clang::CNodeBuilder &Builder)
    : Context(Context), Builder(Builder), Mangler(Context) {}

  // Visit C++ class/struct declarations
  bool VisitCXXRecordDecl(clang::CXXRecordDecl *D);

  // Visit C++ member function declarations
  bool VisitCXXMethodDecl(clang::CXXMethodDecl *MD);

  // Visit C++ constructor declarations (Story #17)
  bool VisitCXXConstructorDecl(clang::CXXConstructorDecl *CD);

  // Visit variable declarations (including member variables)
  bool VisitVarDecl(clang::VarDecl *VD);

  // Expression translation (Story #19)
  clang::Expr* translateExpr(clang::Expr *E);
  clang::Expr* translateDeclRefExpr(clang::DeclRefExpr *DRE);
  clang::Expr* translateMemberExpr(clang::MemberExpr *ME);
  clang::Expr* translateCallExpr(clang::CallExpr *CE);
  clang::Expr* translateBinaryOperator(clang::BinaryOperator *BO);

  // Statement translation (Story #19)
  clang::Stmt* translateStmt(clang::Stmt *S);
  clang::Stmt* translateReturnStmt(clang::ReturnStmt *RS);
  clang::Stmt* translateCompoundStmt(clang::CompoundStmt *CS);

  // Retrieve generated C struct by class name (for testing)
  clang::RecordDecl* getCStruct(llvm::StringRef className) const;

  // Retrieve generated C function by name (for testing)
  clang::FunctionDecl* getCFunc(llvm::StringRef funcName) const;
};

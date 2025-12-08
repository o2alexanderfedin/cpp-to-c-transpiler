#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ASTContext.h"

// RecursiveASTVisitor that traverses C++ AST nodes
// Single Responsibility: Visit and identify AST nodes for translation
class CppToCVisitor : public clang::RecursiveASTVisitor<CppToCVisitor> {
  clang::ASTContext &Context;

public:
  explicit CppToCVisitor(clang::ASTContext &Context) : Context(Context) {}

  // Visit C++ class/struct declarations
  bool VisitCXXRecordDecl(clang::CXXRecordDecl *D);

  // Visit C++ member function declarations
  bool VisitCXXMethodDecl(clang::CXXMethodDecl *MD);

  // Visit variable declarations (including member variables)
  bool VisitVarDecl(clang::VarDecl *VD);
};

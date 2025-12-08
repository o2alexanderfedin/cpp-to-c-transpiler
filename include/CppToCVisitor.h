#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ASTContext.h"
#include "CNodeBuilder.h"
#include <map>
#include <string>

// RecursiveASTVisitor that traverses C++ AST nodes
// Single Responsibility: Visit and identify AST nodes for translation
class CppToCVisitor : public clang::RecursiveASTVisitor<CppToCVisitor> {
  clang::ASTContext &Context;
  clang::CNodeBuilder &Builder;

  // Mapping: C++ class -> C struct (Story #15)
  std::map<clang::CXXRecordDecl*, clang::RecordDecl*> cppToCMap;

public:
  explicit CppToCVisitor(clang::ASTContext &Context, clang::CNodeBuilder &Builder)
    : Context(Context), Builder(Builder) {}

  // Visit C++ class/struct declarations
  bool VisitCXXRecordDecl(clang::CXXRecordDecl *D);

  // Visit C++ member function declarations
  bool VisitCXXMethodDecl(clang::CXXMethodDecl *MD);

  // Visit variable declarations (including member variables)
  bool VisitVarDecl(clang::VarDecl *VD);

  // Retrieve generated C struct by class name (for testing)
  clang::RecordDecl* getCStruct(llvm::StringRef className) const;
};

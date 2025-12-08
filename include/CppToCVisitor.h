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

public:
  explicit CppToCVisitor(clang::ASTContext &Context, clang::CNodeBuilder &Builder)
    : Context(Context), Builder(Builder), Mangler(Context) {}

  // Visit C++ class/struct declarations
  bool VisitCXXRecordDecl(clang::CXXRecordDecl *D);

  // Visit C++ member function declarations
  bool VisitCXXMethodDecl(clang::CXXMethodDecl *MD);

  // Visit variable declarations (including member variables)
  bool VisitVarDecl(clang::VarDecl *VD);

  // Retrieve generated C struct by class name (for testing)
  clang::RecordDecl* getCStruct(llvm::StringRef className) const;

  // Retrieve generated C function by name (for testing)
  clang::FunctionDecl* getCFunc(llvm::StringRef funcName) const;
};

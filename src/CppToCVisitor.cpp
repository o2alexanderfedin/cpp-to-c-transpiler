#include "CppToCVisitor.h"
#include "llvm/Support/raw_ostream.h"
#include <vector>

using namespace clang;

// Story #15: Class-to-Struct Conversion
bool CppToCVisitor::VisitCXXRecordDecl(CXXRecordDecl *D) {
  // Edge case 1: Forward declarations - skip
  if (!D->isCompleteDefinition())
    return true;

  // Edge case 2: Compiler-generated classes - skip
  if (D->isImplicit())
    return true;

  // Edge case 3: Already translated - avoid duplicates
  if (cppToCMap.find(D) != cppToCMap.end())
    return true;

  llvm::outs() << "Translating class: " << D->getNameAsString() << "\n";

  // Build field list for C struct
  std::vector<FieldDecl*> fields;
  for (FieldDecl *Field : D->fields()) {
    // Create C field with same type and name
    FieldDecl *CField = Builder.fieldDecl(
      Field->getType(),
      Field->getName()
    );
    fields.push_back(CField);
  }

  // Create C struct using CNodeBuilder
  RecordDecl *CStruct = Builder.structDecl(D->getName(), fields);

  // Store mapping for method translation
  cppToCMap[D] = CStruct;

  llvm::outs() << "  -> struct " << CStruct->getName() << " with "
               << fields.size() << " fields\n";

  return true;
}

// Story #16: Method-to-Function Conversion
bool CppToCVisitor::VisitCXXMethodDecl(CXXMethodDecl *MD) {
  // Edge case 1: Skip virtual methods (Phase 1 POC scope)
  if (MD->isVirtual()) {
    llvm::outs() << "Skipping virtual method: " << MD->getQualifiedNameAsString() << "\n";
    return true;
  }

  // Edge case 2: Skip implicit methods (compiler-generated)
  if (MD->isImplicit()) {
    return true;
  }

  // Edge case 3: Skip constructors/destructors (handled separately)
  if (isa<CXXConstructorDecl>(MD) || isa<CXXDestructorDecl>(MD)) {
    return true;
  }

  llvm::outs() << "Translating method: " << MD->getQualifiedNameAsString() << "\n";

  CXXRecordDecl *Parent = MD->getParent();
  RecordDecl *CStruct = nullptr;

  // Find C struct for parent class
  if (cppToCMap.find(Parent) != cppToCMap.end()) {
    CStruct = cppToCMap[Parent];
  } else {
    llvm::outs() << "  Warning: Parent struct not found, skipping\n";
    return true;
  }

  // Build parameter list: this + original params
  std::vector<ParmVarDecl*> params;

  // Add this parameter
  QualType thisType = Builder.ptrType(Builder.structType(Parent->getName()));
  ParmVarDecl *thisParam = Builder.param(thisType, "this");
  params.push_back(thisParam);

  // Add original parameters
  for (ParmVarDecl *Param : MD->parameters()) {
    ParmVarDecl *CParam = Builder.param(Param->getType(), Param->getName());
    params.push_back(CParam);
  }

  // Generate function name using name mangling
  std::string funcName = Mangler.mangleName(MD);

  // Create C function
  FunctionDecl *CFunc = Builder.funcDecl(
    funcName,
    MD->getReturnType(),
    params,
    nullptr  // Body translation deferred to Story #19
  );

  // Store mapping
  methodToCFunc[MD] = CFunc;

  llvm::outs() << "  -> " << funcName << " with "
               << params.size() << " parameters\n";

  return true;
}

bool CppToCVisitor::VisitVarDecl(VarDecl *VD) {
  llvm::outs() << "Found variable: " << VD->getNameAsString() << "\n";
  return true;
}

// Retrieve generated C struct by class name (for testing)
RecordDecl* CppToCVisitor::getCStruct(llvm::StringRef className) const {
  // Search through mapping to find struct by name
  for (const auto &entry : cppToCMap) {
    if (entry.second && entry.second->getName() == className) {
      return entry.second;
    }
  }
  return nullptr;
}

// Retrieve generated C function by name (for testing)
FunctionDecl* CppToCVisitor::getCFunc(llvm::StringRef funcName) const {
  // Search through mapping to find function by name
  for (const auto &entry : methodToCFunc) {
    if (entry.second && entry.second->getName() == funcName) {
      return entry.second;
    }
  }
  return nullptr;
}

#include "CppToCVisitor.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
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

  // Create C function (body will be added below)
  FunctionDecl *CFunc = Builder.funcDecl(
    funcName,
    MD->getReturnType(),
    params,
    nullptr
  );

  // Set translation context for body translation (Story #19)
  currentThisParam = thisParam;
  currentMethod = MD;

  // Translate method body if it exists
  if (MD->hasBody()) {
    Stmt *Body = MD->getBody();
    Stmt *TranslatedBody = translateStmt(Body);
    CFunc->setBody(TranslatedBody);
    llvm::outs() << "  -> " << funcName << " with body translated\n";
  } else {
    llvm::outs() << "  -> " << funcName << " (no body)\n";
  }

  // Clear translation context
  currentThisParam = nullptr;
  currentMethod = nullptr;

  // Store mapping
  methodToCFunc[MD] = CFunc;

  llvm::outs() << "  -> " << funcName << " with "
               << params.size() << " parameters\n";

  return true;
}

// Story #17: Constructor Translation (stub for now)
bool CppToCVisitor::VisitCXXConstructorDecl(CXXConstructorDecl *CD) {
  // Edge case: Skip implicit constructors
  if (CD->isImplicit()) {
    return true;
  }

  llvm::outs() << "Found constructor: " << CD->getParent()->getName()
               << "::" << CD->getName() << "\n";

  // TODO: Implement constructor translation in Story #17
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

// ============================================================================
// Story #19: Member Access Transformation - Expression Translation
// ============================================================================

// Main expression translation dispatcher
Expr* CppToCVisitor::translateExpr(Expr *E) {
  if (!E) return nullptr;

  // Dispatch to specific translators based on expression type
  if (MemberExpr *ME = dyn_cast<MemberExpr>(E)) {
    return translateMemberExpr(ME);
  }

  if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(E)) {
    return translateDeclRefExpr(DRE);
  }

  if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
    return translateCallExpr(CE);
  }

  if (BinaryOperator *BO = dyn_cast<BinaryOperator>(E)) {
    return translateBinaryOperator(BO);
  }

  // Default: return expression as-is (literals, etc.)
  return E;
}

// Translate DeclRefExpr - handles implicit 'this'
Expr* CppToCVisitor::translateDeclRefExpr(DeclRefExpr *DRE) {
  ValueDecl *D = DRE->getDecl();

  // Check if this is an implicit member access (field without explicit this)
  if (FieldDecl *FD = dyn_cast<FieldDecl>(D)) {
    // We're inside a method body, convert 'x' to 'this->x'
    if (currentThisParam) {
      llvm::outs() << "  Translating implicit member access: " << FD->getName()
                   << " -> this->" << FD->getName() << "\n";

      return Builder.arrowMember(
        Builder.ref(currentThisParam),
        FD->getName()
      );
    }
  }

  // Regular variable reference - return as-is
  return DRE;
}

// Translate MemberExpr - handles explicit member access
Expr* CppToCVisitor::translateMemberExpr(MemberExpr *ME) {
  Expr *Base = ME->getBase();
  ValueDecl *Member = ME->getMemberDecl();

  llvm::outs() << "  Translating member access: " << Member->getName() << "\n";

  // Translate base recursively
  Expr *TranslatedBase = translateExpr(Base);

  // Determine if we need -> or . based on base type
  if (Base->getType()->isPointerType()) {
    return Builder.arrowMember(TranslatedBase, Member->getName());
  } else {
    return Builder.member(TranslatedBase, Member->getName());
  }
}

// Translate CallExpr - handles function calls
Expr* CppToCVisitor::translateCallExpr(CallExpr *CE) {
  // Translate callee and arguments
  Expr *Callee = translateExpr(CE->getCallee());

  std::vector<Expr*> args;
  for (Expr *Arg : CE->arguments()) {
    args.push_back(translateExpr(Arg));
  }

  // Reconstruct call expression with translated parts
  return CallExpr::Create(
    Context,
    Callee,
    args,
    CE->getType(),
    CE->getValueKind(),
    SourceLocation(),
    FPOptionsOverride()
  );
}

// Translate BinaryOperator - handles assignments, arithmetic, etc.
Expr* CppToCVisitor::translateBinaryOperator(BinaryOperator *BO) {
  Expr *LHS = translateExpr(BO->getLHS());
  Expr *RHS = translateExpr(BO->getRHS());

  return BinaryOperator::Create(
    Context,
    LHS,
    RHS,
    BO->getOpcode(),
    BO->getType(),
    BO->getValueKind(),
    BO->getObjectKind(),
    SourceLocation(),
    FPOptionsOverride()
  );
}

// ============================================================================
// Story #19: Statement Translation
// ============================================================================

// Main statement translation dispatcher
Stmt* CppToCVisitor::translateStmt(Stmt *S) {
  if (!S) return nullptr;

  // Dispatch to specific translators
  if (ReturnStmt *RS = dyn_cast<ReturnStmt>(S)) {
    return translateReturnStmt(RS);
  }

  if (CompoundStmt *CS = dyn_cast<CompoundStmt>(S)) {
    return translateCompoundStmt(CS);
  }

  // If it's an expression, translate it
  if (Expr *E = dyn_cast<Expr>(S)) {
    return translateExpr(E);
  }

  // Default: return as-is
  return S;
}

// Translate return statements
Stmt* CppToCVisitor::translateReturnStmt(ReturnStmt *RS) {
  Expr *RetValue = RS->getRetValue();
  if (RetValue) {
    Expr *TranslatedValue = translateExpr(RetValue);
    return Builder.returnStmt(TranslatedValue);
  }
  return Builder.returnStmt();
}

// Translate compound statements (blocks)
Stmt* CppToCVisitor::translateCompoundStmt(CompoundStmt *CS) {
  std::vector<Stmt*> translatedStmts;

  for (Stmt *S : CS->body()) {
    Stmt *TranslatedStmt = translateStmt(S);
    if (TranslatedStmt) {
      translatedStmts.push_back(TranslatedStmt);
    }
  }

  return Builder.block(translatedStmts);
}

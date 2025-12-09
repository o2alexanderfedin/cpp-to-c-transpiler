#include "CppToCVisitor.h"
#include "CFGAnalyzer.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include <vector>
#include <algorithm>

using namespace clang;

// Story #15 + Story #50: Class-to-Struct Conversion with Base Class Embedding
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

  // Story #50: Embed base class fields at offset 0 (SRP: delegate to helper)
  collectBaseClassFields(D, fields);

  // Add derived class's own fields after base class fields
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

// Story #17: Constructor Translation
bool CppToCVisitor::VisitCXXConstructorDecl(CXXConstructorDecl *CD) {
  // Edge case: Skip implicit constructors (compiler-generated)
  if (CD->isImplicit()) {
    return true;
  }

  llvm::outs() << "Translating constructor: " << CD->getParent()->getName()
               << "::" << CD->getParent()->getName() << "\n";

  CXXRecordDecl *Parent = CD->getParent();
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

  // Add 'this' parameter - use the existing C struct type
  QualType thisType = Builder.ptrType(Context.getRecordType(CStruct));
  ParmVarDecl *thisParam = Builder.param(thisType, "this");
  params.push_back(thisParam);

  // Add original parameters
  for (ParmVarDecl *Param : CD->parameters()) {
    ParmVarDecl *CParam = Builder.param(Param->getType(), Param->getName());
    params.push_back(CParam);
  }

  // Generate constructor name using name mangling
  std::string funcName = Mangler.mangleConstructor(CD);

  // Create C init function (body will be added below)
  FunctionDecl *CFunc = Builder.funcDecl(
    funcName,
    Builder.voidType(),
    params,
    nullptr
  );

  // Build function body
  std::vector<Stmt*> stmts;

  // Set translation context for expression translation
  currentThisParam = thisParam;
  currentMethod = CD;

  // Translate member initializers: this->x = x;
  for (CXXCtorInitializer *Init : CD->inits()) {
    if (Init->isAnyMemberInitializer()) {
      FieldDecl *Field = Init->getAnyMember();
      Expr *InitExpr = Init->getInit();

      if (!Field || !InitExpr) {
        llvm::outs() << "  Warning: Null field or init expr, skipping\n";
        continue;
      }

      llvm::outs() << "  Translating member initializer: " << Field->getName() << "\n";

      // Translate the init expression first
      Expr *TranslatedExpr = translateExpr(InitExpr);
      if (!TranslatedExpr) {
        llvm::outs() << "  Warning: Failed to translate init expr\n";
        continue;
      }

      // Create the arrow member expression for this->field
      MemberExpr *ThisMember = Builder.arrowMember(
        Builder.ref(thisParam),
        Field->getName()
      );

      if (!ThisMember) {
        llvm::outs() << "  Warning: Failed to create arrow member\n";
        continue;
      }

      // Create assignment: this->field = initExpr;
      BinaryOperator *Assignment = Builder.assign(ThisMember, TranslatedExpr);
      if (!Assignment) {
        llvm::outs() << "  Warning: Failed to create assignment\n";
        continue;
      }

      stmts.push_back(Assignment);
    }
  }

  // Translate constructor body statements
  if (CD->hasBody()) {
    CompoundStmt *Body = dyn_cast<CompoundStmt>(CD->getBody());
    if (Body) {
      for (Stmt *S : Body->body()) {
        Stmt *TranslatedStmt = translateStmt(S);
        if (TranslatedStmt) {
          stmts.push_back(TranslatedStmt);
        }
      }
    }
  }

  // Clear translation context
  currentThisParam = nullptr;
  currentMethod = nullptr;

  // Set function body
  CFunc->setBody(Builder.block(stmts));

  // Store mapping
  ctorMap[CD] = CFunc;

  llvm::outs() << "  -> " << funcName << " with "
               << params.size() << " parameters, "
               << stmts.size() << " statements\n";

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

// Retrieve generated C constructor function by name (for testing)
FunctionDecl* CppToCVisitor::getCtor(llvm::StringRef funcName) const {
  // Search through mapping to find constructor by name
  for (const auto &entry : ctorMap) {
    if (entry.second && entry.second->getName() == funcName) {
      return entry.second;
    }
  }
  return nullptr;
}

// Retrieve generated C destructor function by name (for testing - Story #152)
FunctionDecl* CppToCVisitor::getDtor(llvm::StringRef funcName) const {
  // Search through mapping to find destructor by name
  for (const auto &entry : dtorMap) {
    if (entry.second && entry.second->getName() == funcName) {
      return entry.second;
    }
  }
  return nullptr;
}

// ============================================================================
// Epic #5: RAII + Automatic Destructor Injection
// Story #152: Destructor Injection at Function Exit
// ============================================================================

// Visit C++ destructor declarations
bool CppToCVisitor::VisitCXXDestructorDecl(CXXDestructorDecl *DD) {
  // Edge case: Skip implicit destructors (compiler-generated)
  if (DD->isImplicit() || DD->isTrivial()) {
    return true;
  }

  llvm::outs() << "Translating destructor: ~" << DD->getParent()->getName() << "\n";

  CXXRecordDecl *Parent = DD->getParent();
  RecordDecl *CStruct = nullptr;

  // Find C struct for parent class
  if (cppToCMap.find(Parent) != cppToCMap.end()) {
    CStruct = cppToCMap[Parent];
  } else {
    llvm::outs() << "  Warning: Parent struct not found, skipping\n";
    return true;
  }

  // Build parameter list: this pointer only
  std::vector<ParmVarDecl*> params;
  QualType thisType = Builder.ptrType(Context.getRecordType(CStruct));
  ParmVarDecl *thisParam = Builder.param(thisType, "this");
  params.push_back(thisParam);

  // Generate destructor name using name mangling
  std::string funcName = Mangler.mangleDestructor(DD);

  // Create C cleanup function
  FunctionDecl *CFunc = Builder.funcDecl(
    funcName,
    Builder.voidType(),
    params,
    nullptr
  );

  // Set translation context for body translation
  currentThisParam = thisParam;
  currentMethod = DD;

  // Translate destructor body if it exists
  if (DD->hasBody()) {
    Stmt *Body = DD->getBody();
    Stmt *TranslatedBody = translateStmt(Body);
    CFunc->setBody(TranslatedBody);
    llvm::outs() << "  -> " << funcName << " with body translated\n";
  } else {
    // Create empty body for destructor
    CFunc->setBody(Builder.block({}));
    llvm::outs() << "  -> " << funcName << " (empty body)\n";
  }

  // Clear translation context
  currentThisParam = nullptr;
  currentMethod = nullptr;

  // Store mapping
  dtorMap[DD] = CFunc;

  llvm::outs() << "  -> " << funcName << " created\n";

  return true;
}

// Visit function declarations for destructor injection
bool CppToCVisitor::VisitFunctionDecl(FunctionDecl *FD) {
  // Skip if this is a C++ method (handled by VisitCXXMethodDecl)
  if (isa<CXXMethodDecl>(FD)) {
    return true;
  }

  // Skip if no body
  if (!FD->hasBody()) {
    return true;
  }

  // Story #152: Analyze function for RAII objects and inject destructors
  llvm::outs() << "Analyzing function for RAII: " << FD->getNameAsString() << "\n";

  // Use CFGAnalyzer to find local variables
  CFGAnalyzer analyzer;
  analyzer.analyzeCFG(FD);

  std::vector<VarDecl*> localVars = analyzer.getLocalVars();
  llvm::outs() << "  Found " << localVars.size() << " local variables\n";

  // Filter to only objects with destructors
  std::vector<VarDecl*> objectsToDestroy;
  for (VarDecl *VD : localVars) {
    if (hasNonTrivialDestructor(VD->getType())) {
      objectsToDestroy.push_back(VD);
      llvm::outs() << "  Variable '" << VD->getNameAsString()
                   << "' has destructor\n";
    }
  }

  if (!objectsToDestroy.empty()) {
    llvm::outs() << "  Will inject destructors for "
                 << objectsToDestroy.size() << " objects\n";
    // Note: Actual injection happens during translation
    // This visitor just identifies what needs to be done
  }

  return true;
}

// ============================================================================
// Epic #6: Single Inheritance Helper Methods
// ============================================================================

/**
 * Story #50: Collect all base class fields in inheritance order
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only collects base fields, doesn't modify anything
 * - Open/Closed: Can be extended for multiple inheritance without modification
 * - Dependency Inversion: Depends on FieldDecl abstraction, not concrete types
 *
 * Algorithm:
 * 1. Iterate through each base class
 * 2. Lookup the already-translated C struct for that base
 * 3. Copy all fields from base C struct (which already includes its bases)
 * 4. This naturally handles multi-level inheritance (A -> B -> C)
 */
void CppToCVisitor::collectBaseClassFields(CXXRecordDecl *D,
                                            std::vector<FieldDecl*> &fields) {
  // For each direct base class
  for (const CXXBaseSpecifier &Base : D->bases()) {
    CXXRecordDecl *BaseClass = Base.getType()->getAsCXXRecordDecl();

    // Edge case: Invalid or incomplete base class definition
    if (!BaseClass || !BaseClass->isCompleteDefinition()) {
      continue;
    }

    // Lookup the C struct for this base class
    // Note: Base classes are visited before derived classes by AST traversal
    auto it = cppToCMap.find(BaseClass);
    if (it == cppToCMap.end()) {
      // Base class not yet translated - should not happen with proper traversal
      llvm::errs() << "Warning: Base class " << BaseClass->getNameAsString()
                   << " not yet translated\n";
      continue;
    }

    RecordDecl *BaseCStruct = it->second;

    // Copy all fields from base C struct (DRY: reuse existing field decls)
    // The base C struct already contains its own base fields (multi-level)
    for (FieldDecl *BaseField : BaseCStruct->fields()) {
      // Create new field with same type and name for derived struct
      FieldDecl *CField = Builder.fieldDecl(
        BaseField->getType(),
        BaseField->getName()
      );
      fields.push_back(CField);
    }
  }
}

// ============================================================================
// Epic #5: RAII Helper Methods
// ============================================================================

// Helper: Check if type has non-trivial destructor
bool CppToCVisitor::hasNonTrivialDestructor(QualType type) const {
  // Remove qualifiers and get canonical type
  type = type.getCanonicalType();
  type.removeLocalConst();

  // Check if it's a record type (class/struct)
  const RecordType *RT = type->getAs<RecordType>();
  if (!RT) {
    return false;
  }

  RecordDecl *RD = RT->getDecl();
  CXXRecordDecl *CXXRD = dyn_cast<CXXRecordDecl>(RD);

  if (!CXXRD) {
    return false;  // C struct, no destructor
  }

  // Check if destructor exists and is non-trivial
  if (!CXXRD->hasDefinition()) {
    return false;
  }

  return CXXRD->hasNonTrivialDestructor();
}

// Helper: Create destructor call for a variable
CallExpr* CppToCVisitor::createDestructorCall(VarDecl *VD) {
  QualType type = VD->getType();
  const RecordType *RT = type->getAs<RecordType>();
  if (!RT) {
    return nullptr;
  }

  CXXRecordDecl *CXXRD = dyn_cast<CXXRecordDecl>(RT->getDecl());
  if (!CXXRD || !CXXRD->hasDefinition()) {
    return nullptr;
  }

  CXXDestructorDecl *Dtor = CXXRD->getDestructor();
  if (!Dtor) {
    return nullptr;
  }

  // Find the C destructor function
  FunctionDecl *CDtor = nullptr;
  if (dtorMap.find(Dtor) != dtorMap.end()) {
    CDtor = dtorMap[Dtor];
  }

  if (!CDtor) {
    // Destructor not yet translated, this might happen in multi-pass scenarios
    llvm::outs() << "  Warning: Destructor for " << CXXRD->getName()
                 << " not found in mapping\n";
    return nullptr;
  }

  // Create call: ClassName__dtor(&var)
  Expr *VarRef = Builder.ref(VD);
  Expr *AddrOf = Builder.addrOf(VarRef);

  return Builder.call(CDtor, {AddrOf});
}

// Helper: Inject destructors at scope exit
void CppToCVisitor::injectDestructorsAtScopeExit(CompoundStmt *CS,
                                                  const std::vector<VarDecl*> &vars) {
  if (vars.empty()) {
    return;
  }

  // Get existing statements
  std::vector<Stmt*> stmts;
  for (Stmt *S : CS->body()) {
    stmts.push_back(S);
  }

  // Inject destructors in reverse construction order (LIFO)
  for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
    CallExpr *DtorCall = createDestructorCall(*it);
    if (DtorCall) {
      stmts.push_back(DtorCall);
      llvm::outs() << "  Injected destructor call for: "
                   << (*it)->getNameAsString() << "\n";
    }
  }

  // Note: In a real implementation, we'd need to replace the CompoundStmt
  // For now, this demonstrates the logic
  // Actual replacement would require TreeTransform or similar
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

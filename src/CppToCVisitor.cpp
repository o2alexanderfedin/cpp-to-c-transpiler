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

  // Story #62: Generate implicit constructors if needed
  generateImplicitConstructors(D);

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

  // Story #51: Emit base constructor calls FIRST (before member initializers)
  emitBaseConstructorCalls(CD, thisParam, stmts);

  // Story #61: Translate member initializers: this->x = x;
  // IMPORTANT: Clang's AST API returns CXXCtorInitializer nodes in DECLARATION order,
  // not source order. This matches C++ semantics where members are initialized in
  // the order they are declared, regardless of initializer list order.
  //
  // Example: class Point { int x, y, z; public: Point() : z(0), x(0), y(0) {} };
  // Clang returns initializers as: [x, y, z] (declaration order)
  // NOT as: [z, x, y] (source order)
  //
  // This ensures correct C++ initialization semantics automatically.
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

  // Build destructor body with base destructor chaining
  std::vector<Stmt*> stmts;

  // Translate derived destructor body FIRST
  if (DD->hasBody()) {
    CompoundStmt *Body = dyn_cast<CompoundStmt>(DD->getBody());
    if (Body) {
      for (Stmt *S : Body->body()) {
        Stmt *TranslatedStmt = translateStmt(S);
        if (TranslatedStmt) {
          stmts.push_back(TranslatedStmt);
        }
      }
    }
  }

  // Story #52: Emit base destructor calls AFTER derived destructor body
  emitBaseDestructorCalls(DD, thisParam, stmts);

  // Set complete body
  CFunc->setBody(Builder.block(stmts));
  llvm::outs() << "  -> " << funcName << " with " << stmts.size() << " statements\n";

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

/**
 * Story #51: Base Constructor Chaining (Epic #6)
 *
 * Single Responsibility: Extract base constructor call logic from VisitCXXConstructorDecl
 * Open/Closed: Open for extension (virtual inheritance), closed for modification
 *
 * Implementation Strategy:
 * 1. Iterate through constructor's member initializer list
 * 2. For each base class initializer:
 *    a. Extract the base class type
 *    b. Get the C constructor function from ctorMap
 *    c. Build argument list (this + initializer args)
 *    d. Create call expression to base constructor
 * 3. Add base constructor calls to statement list in order
 *
 * C++ Semantics:
 * - Base constructors are called BEFORE derived constructor body
 * - Base constructors are called in the order they appear in member init list
 * - For multi-level inheritance, each level calls its immediate parent only
 */
void CppToCVisitor::emitBaseConstructorCalls(CXXConstructorDecl *CD,
                                              ParmVarDecl *thisParam,
                                              std::vector<Stmt*> &stmts) {
  // Process base class initializers in order
  for (CXXCtorInitializer *Init : CD->inits()) {
    // Skip non-base initializers (member, delegating, etc.)
    if (!Init->isBaseInitializer()) {
      continue;
    }

    // Get the base class type from initializer
    QualType BaseType = Init->getBaseClass()->getCanonicalTypeInternal();
    CXXRecordDecl *BaseClass = BaseType->getAsCXXRecordDecl();

    // Edge case: Invalid base class
    if (!BaseClass) {
      llvm::outs() << "  Warning: Could not get base class, skipping\n";
      continue;
    }

    llvm::outs() << "  Translating base class initializer: " << BaseClass->getName() << "\n";

    // Get the init expression (should be CXXConstructExpr)
    Expr *BaseInit = Init->getInit();
    CXXConstructExpr *CtorExpr = dyn_cast_or_null<CXXConstructExpr>(BaseInit);

    // Edge case: Not a constructor expression
    if (!CtorExpr) {
      llvm::outs() << "  Warning: Base initializer is not a CXXConstructExpr\n";
      continue;
    }

    // Get the base class constructor declaration
    CXXConstructorDecl *BaseCtorDecl = CtorExpr->getConstructor();

    // Lookup the C function for this base constructor
    auto it = ctorMap.find(BaseCtorDecl);
    if (it == ctorMap.end()) {
      llvm::outs() << "  Warning: Base constructor function not found\n";
      continue;
    }

    FunctionDecl *BaseCFunc = it->second;

    // Build argument list for base constructor call
    std::vector<Expr*> baseArgs;

    // First argument: this pointer
    // No explicit cast needed - base class fields are at offset 0 (Story #50)
    baseArgs.push_back(Builder.ref(thisParam));

    // Remaining arguments: from base initializer expression
    for (unsigned i = 0; i < CtorExpr->getNumArgs(); i++) {
      Expr *Arg = CtorExpr->getArg(i);
      Expr *TranslatedArg = translateExpr(Arg);
      if (TranslatedArg) {
        baseArgs.push_back(TranslatedArg);
      }
    }

    // Create the base constructor call expression
    CallExpr *BaseCall = Builder.call(BaseCFunc, baseArgs);
    if (BaseCall) {
      stmts.push_back(BaseCall);
      llvm::outs() << "  -> Added base constructor call to "
                   << BaseCFunc->getNameAsString() << "\n";
    }
  }
}

/**
 * Story #52: Base Destructor Chaining (Epic #6)
 *
 * Single Responsibility: Extract base destructor call logic from VisitCXXDestructorDecl
 * Open/Closed: Open for extension (virtual inheritance), closed for modification
 *
 * Implementation Strategy:
 * 1. Get the derived class's base classes
 * 2. For each base class:
 *    a. Find the base destructor in dtorMap
 *    b. Create call to base destructor with 'this' pointer
 *    c. Append to statement list
 * 3. Base destructors called in order (for single inheritance, only one base)
 *
 * C++ Semantics:
 * - Base destructors are called AFTER derived destructor body
 * - Destruction order is REVERSE of construction order
 * - For multi-level inheritance, each level calls its immediate parent only
 */
void CppToCVisitor::emitBaseDestructorCalls(CXXDestructorDecl *DD,
                                             ParmVarDecl *thisParam,
                                             std::vector<Stmt*> &stmts) {
  CXXRecordDecl *DerivedClass = DD->getParent();

  // Process each direct base class
  for (const CXXBaseSpecifier &Base : DerivedClass->bases()) {
    CXXRecordDecl *BaseClass = Base.getType()->getAsCXXRecordDecl();

    // Edge case: Invalid base class
    if (!BaseClass || !BaseClass->isCompleteDefinition()) {
      continue;
    }

    llvm::outs() << "  Emitting base destructor call for: " << BaseClass->getName() << "\n";

    // Get the base class destructor
    CXXDestructorDecl *BaseDtor = BaseClass->getDestructor();
    if (!BaseDtor) {
      llvm::outs() << "  Warning: Base class has no destructor\n";
      continue;
    }

    // Lookup the C function for this base destructor
    auto it = dtorMap.find(BaseDtor);
    if (it == dtorMap.end()) {
      llvm::outs() << "  Warning: Base destructor function not found\n";
      continue;
    }

    FunctionDecl *BaseDFunc = it->second;

    // Build argument list: just 'this' pointer
    std::vector<Expr*> baseArgs;
    baseArgs.push_back(Builder.ref(thisParam));

    // Create the base destructor call expression
    CallExpr *BaseCall = Builder.call(BaseDFunc, baseArgs);
    if (BaseCall) {
      stmts.push_back(BaseCall);
      llvm::outs() << "  -> Added base destructor call to "
                   << BaseDFunc->getNameAsString() << "\n";
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

// ============================================================================
// Epic #7: Implicit Constructor Generation (Story #62)
// ============================================================================

/**
 * Story #62: Check if class needs implicit default constructor
 *
 * Returns true if:
 * - No user-declared constructors exist (hasUserDeclaredConstructor() returns false)
 */
bool CppToCVisitor::needsImplicitDefaultConstructor(CXXRecordDecl *D) const {
  // If user declared ANY constructor, no implicit default constructor
  return !D->hasUserDeclaredConstructor();
}

/**
 * Story #62: Check if class needs implicit copy constructor
 *
 * Returns true if:
 * - No user-declared copy constructor exists
 * - Class has at least one constructor (to enable copy construction)
 */
bool CppToCVisitor::needsImplicitCopyConstructor(CXXRecordDecl *D) const {
  // Check if user declared a copy constructor (not compiler-generated)
  for (CXXConstructorDecl *Ctor : D->ctors()) {
    if (Ctor->isCopyConstructor() && !Ctor->isImplicit()) {
      return false;  // User declared copy constructor exists
    }
  }

  // Generate copy constructor if class has any constructor
  // (either explicit or we're about to generate default)
  return D->hasUserDeclaredConstructor() || needsImplicitDefaultConstructor(D);
}

/**
 * Story #62: Generate implicit constructors for a class
 *
 * Orchestrates generation of default and copy constructors when needed.
 */
void CppToCVisitor::generateImplicitConstructors(CXXRecordDecl *D) {
  // Generate default constructor if needed
  if (needsImplicitDefaultConstructor(D)) {
    llvm::outs() << "  Generating implicit default constructor\n";
    FunctionDecl *DefaultCtor = generateDefaultConstructor(D);
    if (DefaultCtor) {
      // Store in constructor map for retrieval by tests
      // Use the FunctionDecl pointer cast as key (implicit ctors don't have CXXConstructorDecl)
      ctorMap[reinterpret_cast<CXXConstructorDecl*>(DefaultCtor)] = DefaultCtor;
    }
  }

  // Generate copy constructor if needed
  if (needsImplicitCopyConstructor(D)) {
    llvm::outs() << "  Generating implicit copy constructor\n";
    FunctionDecl *CopyCtor = generateCopyConstructor(D);
    if (CopyCtor) {
      // Store in constructor map for retrieval by tests
      // Use the FunctionDecl pointer cast as key (implicit ctors don't have CXXConstructorDecl)
      ctorMap[reinterpret_cast<CXXConstructorDecl*>(CopyCtor)] = CopyCtor;
    }
  }
}

/**
 * Story #62: Generate default constructor
 *
 * Generates: Class__ctor_default(struct Class *this)
 * - Zero-initializes primitive members
 * - Calls default constructors for class-type members
 * - Calls base class default constructor if derived
 */
FunctionDecl* CppToCVisitor::generateDefaultConstructor(CXXRecordDecl *D) {
  // Get the C struct for this class
  RecordDecl *CStruct = cppToCMap[D];
  if (!CStruct) {
    llvm::outs() << "  Warning: C struct not found for default ctor generation\n";
    return nullptr;
  }

  // Build parameter list: only 'this' parameter
  std::vector<ParmVarDecl*> params;
  QualType thisType = Builder.ptrType(Context.getRecordType(CStruct));
  ParmVarDecl *thisParam = Builder.param(thisType, "this");
  params.push_back(thisParam);

  // Generate constructor name: Class__ctor_default
  std::string funcName = D->getName().str() + "__ctor_default";

  // Create C init function
  FunctionDecl *CFunc = Builder.funcDecl(
    funcName,
    Builder.voidType(),
    params,
    nullptr
  );

  // Build function body
  std::vector<Stmt*> stmts;

  // Set translation context
  currentThisParam = thisParam;
  currentMethod = nullptr;

  // 1. Call base class default constructor if derived
  if (D->getNumBases() > 0) {
    for (const CXXBaseSpecifier &Base : D->bases()) {
      CXXRecordDecl *BaseClass = Base.getType()->getAsCXXRecordDecl();
      if (!BaseClass) continue;

      std::string baseCtorName = BaseClass->getName().str() + "__ctor_default";
      llvm::outs() << "    TODO: Call base default constructor: " << baseCtorName << "\n";
      // TODO: Look up base constructor and create call expression
      // For now, this is left for Story #63 (Complete Constructor Chaining)
    }
  }

  // 2. Initialize members in declaration order
  for (FieldDecl *Field : D->fields()) {
    QualType fieldType = Field->getType();

    // Create this->field member expression
    MemberExpr *ThisMember = Builder.arrowMember(
      Builder.ref(thisParam),
      Field->getName()
    );

    if (fieldType->isRecordType()) {
      // Class-type member: call default constructor
      CXXRecordDecl *FieldClass = fieldType->getAsCXXRecordDecl();
      if (FieldClass) {
        std::string fieldCtorName = FieldClass->getName().str() + "__ctor_default";

        // Look up the member's default constructor
        // Try implicit name first (_default suffix)
        FunctionDecl *MemberCtor = getCtor(fieldCtorName);

        // If not found, try explicit default constructor name (no suffix)
        if (!MemberCtor) {
          std::string explicitCtorName = FieldClass->getName().str() + "__ctor";
          MemberCtor = getCtor(explicitCtorName);
        }

        // If still not found, try to translate it on-demand
        if (!MemberCtor) {
          // Find the member class's default constructor
          for (CXXConstructorDecl *Ctor : FieldClass->ctors()) {
            if (Ctor->isDefaultConstructor() && !Ctor->isImplicit()) {
              // Translate this explicit default constructor now
              std::string explicitCtorName = FieldClass->getName().str() + "__ctor";
              llvm::outs() << "    On-demand translation of " << explicitCtorName << "\n";
              VisitCXXConstructorDecl(Ctor);
              MemberCtor = getCtor(explicitCtorName);
              break;
            }
          }
        }

        if (MemberCtor) {
          // Create call: MemberClass__ctor_default(&this->member);
          std::vector<Expr*> args;

          // Address of this->member
          Expr *memberAddr = Builder.addrOf(ThisMember);
          args.push_back(memberAddr);

          // Create call expression
          CallExpr *memberCtorCall = Builder.call(MemberCtor, args);
          if (memberCtorCall) {
            stmts.push_back(memberCtorCall);
            llvm::outs() << "    Calling member default constructor: " << fieldCtorName << " for field " << Field->getName() << "\n";
          }
        } else {
          llvm::outs() << "    Warning: Member default constructor not found: " << fieldCtorName << "\n";
        }
      }
    } else if (fieldType->isPointerType()) {
      // Pointer member: initialize to NULL
      Expr *nullExpr = Builder.nullPtr();
      BinaryOperator *Assignment = Builder.assign(ThisMember, nullExpr);
      stmts.push_back(Assignment);
    } else {
      // Primitive member: zero-initialize
      Expr *zeroExpr = Builder.intLit(0);
      BinaryOperator *Assignment = Builder.assign(ThisMember, zeroExpr);
      stmts.push_back(Assignment);
    }
  }

  // Create function body
  CompoundStmt *body = Builder.block(stmts);

  // Set function body
  CFunc->setBody(body);

  llvm::outs() << "  Generated default constructor: " << funcName << "\n";
  return CFunc;
}

/**
 * Story #62: Generate copy constructor
 *
 * Generates: Class__ctor_copy(struct Class *this, const struct Class *other)
 * - Performs memberwise copy for primitive members
 * - Calls copy constructors for class-type members
 * - Performs shallow copy for pointer members
 * - Calls base class copy constructor if derived
 */
FunctionDecl* CppToCVisitor::generateCopyConstructor(CXXRecordDecl *D) {
  // Get the C struct for this class
  RecordDecl *CStruct = cppToCMap[D];
  if (!CStruct) {
    llvm::outs() << "  Warning: C struct not found for copy ctor generation\n";
    return nullptr;
  }

  // Build parameter list: this + other
  std::vector<ParmVarDecl*> params;

  QualType thisType = Builder.ptrType(Context.getRecordType(CStruct));
  ParmVarDecl *thisParam = Builder.param(thisType, "this");
  params.push_back(thisParam);

  // const struct Class *other
  QualType otherType = Builder.ptrType(
    Context.getConstType(Context.getRecordType(CStruct))
  );
  ParmVarDecl *otherParam = Builder.param(otherType, "other");
  params.push_back(otherParam);

  // Generate constructor name: Class__ctor_copy
  std::string funcName = D->getName().str() + "__ctor_copy";

  // Create C init function
  FunctionDecl *CFunc = Builder.funcDecl(
    funcName,
    Builder.voidType(),
    params,
    nullptr
  );

  // Build function body
  std::vector<Stmt*> stmts;

  // Set translation context
  currentThisParam = thisParam;
  currentMethod = nullptr;

  // 1. Call base class copy constructor if derived
  if (D->getNumBases() > 0) {
    for (const CXXBaseSpecifier &Base : D->bases()) {
      CXXRecordDecl *BaseClass = Base.getType()->getAsCXXRecordDecl();
      if (!BaseClass) continue;

      std::string baseCopyCtorName = BaseClass->getName().str() + "__ctor_copy";
      llvm::outs() << "    TODO: Call base copy constructor: " << baseCopyCtorName << "\n";
    }
  }

  // 2. Copy members in declaration order
  for (FieldDecl *Field : D->fields()) {
    QualType fieldType = Field->getType();

    // Create this->field and other->field member expressions
    MemberExpr *ThisMember = Builder.arrowMember(
      Builder.ref(thisParam),
      Field->getName()
    );

    MemberExpr *OtherMember = Builder.arrowMember(
      Builder.ref(otherParam),
      Field->getName()
    );

    if (fieldType->isRecordType()) {
      // Class-type member: call copy constructor
      CXXRecordDecl *FieldClass = fieldType->getAsCXXRecordDecl();
      if (FieldClass) {
        std::string fieldCopyCtorName = FieldClass->getName().str() + "__ctor_copy";

        // Look up the member's copy constructor
        // Try implicit name first (_copy suffix)
        FunctionDecl *MemberCopyCtor = getCtor(fieldCopyCtorName);

        // If not found, try to translate explicit copy constructor on-demand
        if (!MemberCopyCtor) {
          // Find the member class's copy constructor
          for (CXXConstructorDecl *Ctor : FieldClass->ctors()) {
            if (Ctor->isCopyConstructor() && !Ctor->isImplicit()) {
              // Translate this explicit copy constructor now
              llvm::outs() << "    On-demand translation of explicit copy constructor\n";
              VisitCXXConstructorDecl(Ctor);
              // After translation, look it up directly using the key
              auto it = ctorMap.find(Ctor);
              if (it != ctorMap.end()) {
                MemberCopyCtor = it->second;
                llvm::outs() << "    Found copy constructor: " << MemberCopyCtor->getNameAsString() << "\n";
              } else {
                llvm::outs() << "    Warning: Translated copy constructor not found in map\n";
              }
              break;
            }
          }
        }

        if (MemberCopyCtor) {
          // Create call: MemberClass__ctor_copy(&this->member, &other->member);
          std::vector<Expr*> args;

          // First arg: address of this->member
          Expr *thisMemberAddr = Builder.addrOf(ThisMember);
          args.push_back(thisMemberAddr);

          // Second arg: address of other->member
          Expr *otherMemberAddr = Builder.addrOf(OtherMember);
          args.push_back(otherMemberAddr);

          // Create call expression
          CallExpr *memberCopyCall = Builder.call(MemberCopyCtor, args);
          if (memberCopyCall) {
            stmts.push_back(memberCopyCall);
            llvm::outs() << "    Calling member copy constructor: " << MemberCopyCtor->getNameAsString() << " for field " << Field->getName() << "\n";
          }
        } else {
          llvm::outs() << "    Warning: Member copy constructor not found: " << fieldCopyCtorName << "\n";
        }
      }
    } else {
      // Primitive or pointer member: memberwise (shallow) copy
      BinaryOperator *Assignment = Builder.assign(ThisMember, OtherMember);
      stmts.push_back(Assignment);
    }
  }

  // Create function body
  CompoundStmt *body = Builder.block(stmts);

  // Set function body
  CFunc->setBody(body);

  llvm::outs() << "  Generated copy constructor: " << funcName << "\n";
  return CFunc;
}

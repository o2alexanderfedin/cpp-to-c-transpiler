#include "CppToCVisitor.h"
#include "CFGAnalyzer.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/Basic/SourceManager.h"
#include <vector>
#include <algorithm>

using namespace clang;

// Forward declarations of CLI accessor functions from main.cpp
extern bool shouldGenerateACSL();
extern ACSLLevel getACSLLevel();
extern ACSLOutputMode getACSLOutputMode();
extern bool shouldGenerateMemoryPredicates(); // Phase 6 (v1.23.0)

// Epic #193: ACSL Integration - Constructor Implementation
CppToCVisitor::CppToCVisitor(ASTContext &Context, CNodeBuilder &Builder)
    : Context(Context), Builder(Builder), Mangler(Context),
      VirtualAnalyzer(Context), VptrInjectorInstance(Context, VirtualAnalyzer),
      MoveCtorTranslator(Context), MoveAssignTranslator(Context),
      RvalueRefParamTrans(Context) {

  // Initialize ACSL annotators if --generate-acsl flag is enabled
  if (shouldGenerateACSL()) {
    ACSLLevel level = getACSLLevel();
    ACSLOutputMode mode = getACSLOutputMode();

    llvm::outs() << "Initializing ACSL annotators (level: "
                 << (level == ACSLLevel::Basic ? "basic" : "full")
                 << ", mode: " << (mode == ACSLOutputMode::Inline ? "inline" : "separate")
                 << ")\n";

    // Initialize all 8 ACSL annotator classes
    m_functionAnnotator = std::make_unique<ACSLFunctionAnnotator>(level, mode);
    m_loopAnnotator = std::make_unique<ACSLLoopAnnotator>(level, mode);
    m_classAnnotator = std::make_unique<ACSLClassAnnotator>(level, mode);
    m_statementAnnotator = std::make_unique<ACSLStatementAnnotator>(level, mode);
    m_typeInvariantGen = std::make_unique<ACSLTypeInvariantGenerator>(level, mode);
    m_axiomaticBuilder = std::make_unique<ACSLAxiomaticBuilder>(level, mode);
    m_ghostInjector = std::make_unique<ACSLGhostCodeInjector>(level, mode);
    // Note: ACSLBehaviorAnnotator only accepts level parameter (no mode parameter)
    m_behaviorAnnotator = std::make_unique<ACSLBehaviorAnnotator>(level);

    // Phase 6 (v1.23.0): Configure memory predicates if enabled
    if (shouldGenerateMemoryPredicates()) {
      m_functionAnnotator->setMemoryPredicatesEnabled(true);
      llvm::outs() << "Memory predicates enabled (allocable, freeable, block_length, base_addr)\n";
    }
  }
}

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

  // Story #169: Inject vptr field if this is a polymorphic class without bases
  // If class has bases, base class would have already injected vptr
  if (D->getNumBases() == 0) {
    VptrInjectorInstance.injectVptrField(D, fields);
  }

  // Add derived class's own fields after base class fields and vptr
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

  // Epic #193: Generate ACSL class invariants if enabled
  if (m_classAnnotator && m_typeInvariantGen) {
    llvm::outs() << "Generating ACSL invariants for class: "
                 << D->getNameAsString() << "\n";

    // Generate class invariants
    std::string classInvariant = m_classAnnotator->generateClassInvariantPredicate(D);

    // Generate type invariants if full level
    std::string typeInvariants;
    if (getACSLLevel() == ACSLLevel::Full && m_typeInvariantGen) {
      typeInvariants = m_typeInvariantGen->generateTypeInvariant(D);
    }

    // Combine annotations
    std::string fullAnnotation = classInvariant;
    if (!typeInvariants.empty()) {
      fullAnnotation += "\n" + typeInvariants;
    }

    // Emit ACSL annotation
    if (!fullAnnotation.empty()) {
      emitACSL(fullAnnotation, getACSLOutputMode());
    }
  }

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

  // Story #131: Handle move assignment operators
  if (MoveAssignTranslator.isMoveAssignmentOperator(MD)) {
    llvm::outs() << "Translating move assignment operator: " << MD->getQualifiedNameAsString() << "\n";
    std::string cCode = MoveAssignTranslator.generateMoveAssignment(MD);
    if (!cCode.empty()) {
      llvm::outs() << "Generated move assignment C code:\n" << cCode << "\n";
      // TODO: Store generated function for later output
    }
    return true;
  }

  // Story #134: Handle copy assignment operators (skip for now, similar to move)
  if (MD->isCopyAssignmentOperator()) {
    llvm::outs() << "Translating copy assignment operator: " << MD->getQualifiedNameAsString() << "\n";
    // Copy assignment operators are handled similar to move assignments
    // TODO: Generate C code for copy assignment
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

  // Story #130: Handle move constructors specially
  if (MoveCtorTranslator.isMoveConstructor(CD)) {
    llvm::outs() << "Detected move constructor: " << CD->getParent()->getName()
                 << "::" << CD->getParent()->getName() << "(&&)\n";

    std::string moveCtorCode = MoveCtorTranslator.generateMoveConstructor(CD);
    if (!moveCtorCode.empty()) {
      llvm::outs() << "Generated move constructor C code:\n" << moveCtorCode << "\n";
    }

    // Note: For now, we just generate the code for testing/validation
    // Full integration would store this in a function declaration
    // Continue with normal processing to store in ctorMap for now
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

  // Story #184: Handle delegating constructors
  if (CD->isDelegatingConstructor()) {
    llvm::outs() << "  Delegating constructor detected\n";

    // Find the delegating initializer
    CXXCtorInitializer *DelegatingInit = nullptr;
    for (CXXCtorInitializer *Init : CD->inits()) {
      if (Init->isDelegatingInitializer()) {
        DelegatingInit = Init;
        break;
      }
    }

    if (DelegatingInit) {
      // Get the target constructor from the delegating initializer
      Expr *InitExpr = DelegatingInit->getInit();
      CXXConstructExpr *CtorExpr = dyn_cast_or_null<CXXConstructExpr>(InitExpr);

      if (CtorExpr) {
        CXXConstructorDecl *TargetCtor = CtorExpr->getConstructor();

        // Lookup the C function for the target constructor
        auto it = ctorMap.find(TargetCtor);
        if (it != ctorMap.end()) {
          FunctionDecl *TargetCFunc = it->second;

          // Build argument list: this + arguments from delegating call
          std::vector<Expr*> targetArgs;
          targetArgs.push_back(Builder.ref(thisParam));

          for (unsigned i = 0; i < CtorExpr->getNumArgs(); i++) {
            Expr *Arg = CtorExpr->getArg(i);
            Expr *TranslatedArg = translateExpr(Arg);
            if (TranslatedArg) {
              targetArgs.push_back(TranslatedArg);
            }
          }

          // Create call to target constructor
          CallExpr *DelegateCall = Builder.call(TargetCFunc, targetArgs);
          if (DelegateCall) {
            stmts.push_back(DelegateCall);
            llvm::outs() << "  -> Delegating to " << TargetCFunc->getNameAsString() << "\n";
          }
        } else {
          llvm::outs() << "  Warning: Target constructor function not found\n";
        }
      }
    }
    // Note: For delegating constructors, we skip base/member initialization
    // because the target constructor handles all initialization
  } else {
    // Non-delegating constructor: normal initialization
    // Story #51: Emit base constructor calls FIRST (before member initializers)
    emitBaseConstructorCalls(CD, thisParam, stmts);

    // Story #63: Emit member constructor calls in DECLARATION order
    // Handles both class-type members (constructor calls) and primitives (assignment)
    emitMemberConstructorCalls(CD, thisParam, stmts);
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

  // Story #63: Emit member destructor calls in REVERSE declaration order
  // Called AFTER derived body, BEFORE base destructors
  CXXRecordDecl *ClassDecl = DD->getParent();
  emitMemberDestructorCalls(ClassDecl, thisParam, stmts);

  // Story #52: Emit base destructor calls AFTER member destructors
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

    // Story #44: Store objects for destruction at function scope
    // These will be used during statement translation to inject destructor calls
    currentFunctionObjectsToDestroy = objectsToDestroy;

    // Story #45: Clear previous return tracking for this function
    currentFunctionReturns.clear();

    // Story #47: Clear previous goto/label tracking for this function
    currentFunctionGotos.clear();
    currentFunctionLabels.clear();

    // Story #48: Clear previous break/continue tracking for this function
    currentFunctionBreaksContinues.clear();

    // Story #45: Analyze return statements in the function
    // The VisitReturnStmt will be called automatically during traversal
    // and will populate currentFunctionReturns

    // Story #47: Analyze goto statements after traversal
    // The VisitGotoStmt and VisitLabelStmt will be called during traversal
    // and will populate currentFunctionGotos and currentFunctionLabels
    // After traversal, we match them and determine destructor injection points
    analyzeGotoStatements(FD);

    // Story #48: Analyze break/continue statements after traversal
    // The VisitBreakStmt and VisitContinueStmt will be called during traversal
    // and will populate currentFunctionBreaksContinues
    // After traversal, we identify objects needing destruction
    analyzeBreakContinueStatements(FD);

  } else {
    currentFunctionObjectsToDestroy.clear();
    currentFunctionReturns.clear();
    currentFunctionGotos.clear();
    currentFunctionLabels.clear();
    currentFunctionBreaksContinues.clear();
  }

  // Epic #193: Generate ACSL function contracts if enabled
  if (m_functionAnnotator && m_behaviorAnnotator) {
    llvm::outs() << "Generating ACSL contract for function: "
                 << FD->getNameAsString() << "\n";

    // Generate function contract (requires, ensures, assigns)
    std::string functionContract = m_functionAnnotator->generateFunctionContract(FD);

    // Generate behavior annotations if full level
    std::string behaviorAnnotations;
    if (getACSLLevel() == ACSLLevel::Full && m_behaviorAnnotator) {
      behaviorAnnotations = m_behaviorAnnotator->generateBehaviors(FD);
    }

    // Combine annotations
    std::string fullAnnotation = functionContract;
    if (!behaviorAnnotations.empty()) {
      fullAnnotation += "\n" + behaviorAnnotations;
    }

    // Emit ACSL annotation
    if (!fullAnnotation.empty()) {
      emitACSL(fullAnnotation, getACSLOutputMode());
    }
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
// Story #63: Complete Constructor/Destructor Chaining Helper Methods
// ============================================================================

// Helper: Find initializer for a specific field in constructor init list
CXXCtorInitializer* CppToCVisitor::findInitializerForField(
    CXXConstructorDecl *CD,
    FieldDecl *Field) {
  for (CXXCtorInitializer *Init : CD->inits()) {
    if (Init->isAnyMemberInitializer() && Init->getAnyMember() == Field) {
      return Init;
    }
  }
  return nullptr;
}

// Emit member constructor calls in declaration order
void CppToCVisitor::emitMemberConstructorCalls(CXXConstructorDecl *CD,
                                                ParmVarDecl *thisParam,
                                                std::vector<Stmt*> &stmts) {
  CXXRecordDecl *ClassDecl = CD->getParent();

  // Iterate fields in DECLARATION order (not init list order)
  for (FieldDecl *Field : ClassDecl->fields()) {
    QualType fieldType = Field->getType();

    // Check if field has initializer in init list
    CXXCtorInitializer *Init = findInitializerForField(CD, Field);

    if (fieldType->isRecordType()) {
      // Class-type member: needs constructor call
      const RecordType *RT = fieldType->getAs<RecordType>();
      CXXRecordDecl *FieldClass = dyn_cast<CXXRecordDecl>(RT->getDecl());

      if (!FieldClass || !FieldClass->hasDefinition()) {
        continue;
      }

      if (Init) {
        // Has explicit initializer: inner(val) or inner = other
        Expr *InitExpr = Init->getInit();

        if (CXXConstructExpr *CE = dyn_cast<CXXConstructExpr>(InitExpr)) {
          // Constructor call: inner(val)
          CXXConstructorDecl *MemberCtor = CE->getConstructor();

          // Lookup the C constructor function
          auto it = ctorMap.find(MemberCtor);
          if (it == ctorMap.end()) {
            llvm::outs() << "  Warning: Member constructor function not found\n";
            continue;
          }

          FunctionDecl *MemberCFunc = it->second;

          // Build argument list: &this->field, arg1, arg2, ...
          MemberExpr *ThisMember = Builder.arrowMember(Builder.ref(thisParam), Field->getName());
          Expr *memberAddr = Builder.addrOf(ThisMember);

          std::vector<Expr*> args;
          args.push_back(memberAddr);

          for (const Expr *Arg : CE->arguments()) {
            args.push_back(translateExpr(const_cast<Expr*>(Arg)));
          }

          CallExpr *ctorCall = Builder.call(MemberCFunc, args);
          stmts.push_back(ctorCall);

        } else {
          // Copy/assignment: inner = other or inner(other) for copy
          // Treat as assignment for now
          MemberExpr *ThisMember = Builder.arrowMember(Builder.ref(thisParam), Field->getName());
          Expr *TranslatedExpr = translateExpr(InitExpr);
          BinaryOperator *Assignment = Builder.assign(ThisMember, TranslatedExpr);
          stmts.push_back(Assignment);
        }
      } else {
        // No initializer: call default constructor
        // Find default constructor
        CXXConstructorDecl *DefaultCtor = nullptr;
        for (CXXConstructorDecl *Ctor : FieldClass->ctors()) {
          if (Ctor->isDefaultConstructor()) {
            DefaultCtor = Ctor;
            break;
          }
        }

        if (DefaultCtor) {
          // Lookup the C constructor function
          auto it = ctorMap.find(DefaultCtor);
          if (it != ctorMap.end()) {
            FunctionDecl *MemberCFunc = it->second;

            MemberExpr *ThisMember = Builder.arrowMember(Builder.ref(thisParam), Field->getName());
            Expr *memberAddr = Builder.addrOf(ThisMember);

            CallExpr *ctorCall = Builder.call(MemberCFunc, {memberAddr});
            stmts.push_back(ctorCall);
          }
        }
      }
    } else {
      // Primitive member: use assignment if has initializer
      if (Init) {
        MemberExpr *ThisMember = Builder.arrowMember(Builder.ref(thisParam), Field->getName());
        Expr *TranslatedExpr = translateExpr(Init->getInit());
        BinaryOperator *Assignment = Builder.assign(ThisMember, TranslatedExpr);
        stmts.push_back(Assignment);
      }
    }
  }
}

// Emit member destructor calls in reverse declaration order
void CppToCVisitor::emitMemberDestructorCalls(CXXRecordDecl *ClassDecl,
                                               ParmVarDecl *thisParam,
                                               std::vector<Stmt*> &stmts) {
  // Collect fields with non-trivial destructors
  std::vector<FieldDecl*> fieldsToDestroy;

  for (FieldDecl *Field : ClassDecl->fields()) {
    if (hasNonTrivialDestructor(Field->getType())) {
      fieldsToDestroy.push_back(Field);
    }
  }

  // Destroy in REVERSE declaration order
  for (auto it = fieldsToDestroy.rbegin(); it != fieldsToDestroy.rend(); ++it) {
    FieldDecl *Field = *it;
    QualType fieldType = Field->getType();

    // Get destructor for member type
    const RecordType *RT = fieldType->getAs<RecordType>();
    if (!RT) continue;

    CXXRecordDecl *FieldClass = dyn_cast<CXXRecordDecl>(RT->getDecl());
    if (!FieldClass || !FieldClass->hasDefinition()) continue;

    CXXDestructorDecl *FieldDtor = FieldClass->getDestructor();
    if (!FieldDtor) continue;

    // Lookup the C destructor function
    auto it2 = dtorMap.find(FieldDtor);
    if (it2 == dtorMap.end()) {
      continue;
    }

    FunctionDecl *FieldDFunc = it2->second;

    // Build: FieldDtor(&this->field)
    MemberExpr *ThisMember = Builder.arrowMember(Builder.ref(thisParam), Field->getName());
    Expr *memberAddr = Builder.addrOf(ThisMember);
    CallExpr *dtorCall = Builder.call(FieldDFunc, {memberAddr});
    stmts.push_back(dtorCall);
  }
}

// ============================================================================
// Epic #5: RAII Helper Methods
// ============================================================================

// Story #45: Visit return statements for early return detection
bool CppToCVisitor::VisitReturnStmt(ReturnStmt *RS) {
  // Skip if not analyzing a function
  if (currentFunctionObjectsToDestroy.empty()) {
    return true;
  }

  llvm::outs() << "  Detected return statement for early return analysis\n";

  // Track this return statement (we'll analyze scope later during translation)
  ReturnInfo info;
  info.returnStmt = RS;
  // Live objects will be determined during translation phase
  currentFunctionReturns.push_back(info);

  return true;
}

// Story #45: Analyze which objects are live at a specific return point
std::vector<VarDecl*> CppToCVisitor::analyzeLiveObjectsAtReturn(
    ReturnStmt *RS, FunctionDecl *FD) {

  std::vector<VarDecl*> liveObjects;

  if (!FD || !RS) {
    return liveObjects;
  }

  // Get source location of the return statement
  SourceLocation returnLoc = RS->getBeginLoc();

  llvm::outs() << "  Analyzing live objects at return statement...\n";

  // For each object with a destructor in the function
  for (VarDecl *VD : currentFunctionObjectsToDestroy) {
    SourceLocation varLoc = VD->getBeginLoc();

    // Check if variable is declared before the return statement
    if (varLoc.isValid() && returnLoc.isValid()) {
      // Use source manager to compare locations
      SourceManager &SM = Context.getSourceManager();

      // Variable must be declared before return to be live
      if (SM.isBeforeInTranslationUnit(varLoc, returnLoc)) {
        // Additional check: ensure variable is in scope at return point
        // For now, we assume lexical ordering implies scope
        // TODO: More sophisticated scope analysis for nested blocks

        liveObjects.push_back(VD);
        llvm::outs() << "    Variable '" << VD->getNameAsString()
                     << "' is live at return\n";
      }
    }
  }

  return liveObjects;
}

// Story #45: Check if one statement comes before another
bool CppToCVisitor::comesBefore(Stmt *Before, Stmt *After) {
  if (!Before || !After) {
    return false;
  }

  SourceLocation beforeLoc = Before->getBeginLoc();
  SourceLocation afterLoc = After->getBeginLoc();

  if (!beforeLoc.isValid() || !afterLoc.isValid()) {
    return false;
  }

  SourceManager &SM = Context.getSourceManager();
  return SM.isBeforeInTranslationUnit(beforeLoc, afterLoc);
}

// ============================================================================
// Story #46: Nested Scope Tracking Methods
// ============================================================================

// Enter a new scope (push onto scope stack)
void CppToCVisitor::enterScope(CompoundStmt *CS) {
  ScopeInfo info;
  info.stmt = CS;
  info.depth = scopeStack.size();  // Current stack size is the depth
  // objects vector starts empty

  scopeStack.push_back(info);

  llvm::outs() << "  [Scope] Entering scope at depth " << info.depth << "\n";
}

// Exit current scope (pop from scope stack)
CppToCVisitor::ScopeInfo CppToCVisitor::exitScope() {
  if (scopeStack.empty()) {
    llvm::errs() << "Warning: Attempting to exit scope when stack is empty\n";
    return ScopeInfo{nullptr, {}, 0};
  }

  ScopeInfo info = scopeStack.back();
  scopeStack.pop_back();

  llvm::outs() << "  [Scope] Exiting scope at depth " << info.depth
               << " with " << info.objects.size() << " objects\n";

  return info;
}

// Track a variable declaration in the current scope
void CppToCVisitor::trackObjectInCurrentScope(VarDecl *VD) {
  if (scopeStack.empty()) {
    llvm::outs() << "  [Scope] Warning: No active scope to track object in\n";
    return;
  }

  // Add to the current (top) scope
  scopeStack.back().objects.push_back(VD);

  llvm::outs() << "  [Scope] Tracked object '" << VD->getNameAsString()
               << "' in scope depth " << scopeStack.back().depth << "\n";
}

// ============================================================================
// Story #47: Goto Statement Handling Methods
// ============================================================================

// Visit goto statements for detection and tracking
bool CppToCVisitor::VisitGotoStmt(GotoStmt *GS) {
  // Skip if not analyzing a function
  if (currentFunctionObjectsToDestroy.empty()) {
    return true;
  }

  llvm::outs() << "  [Goto] Detected goto to label: " << GS->getLabel()->getName() << "\n";

  // Store goto statement for later analysis
  GotoInfo info;
  info.gotoStmt = GS;
  info.targetLabel = nullptr;  // Will be matched in analyzeGotoStatements()
  currentFunctionGotos.push_back(info);

  return true;
}

// Visit label statements for detection and tracking
bool CppToCVisitor::VisitLabelStmt(LabelStmt *LS) {
  // Skip if not analyzing a function
  if (currentFunctionObjectsToDestroy.empty()) {
    return true;
  }

  std::string labelName = LS->getName();
  llvm::outs() << "  [Goto] Detected label: " << labelName << "\n";

  // Store label for goto matching
  currentFunctionLabels[labelName] = LS;

  return true;
}

// Analyze goto-label pairs and determine objects needing destruction
void CppToCVisitor::analyzeGotoStatements(FunctionDecl *FD) {
  if (currentFunctionGotos.empty()) {
    return;  // No gotos to analyze
  }

  llvm::outs() << "  [Goto] Analyzing " << currentFunctionGotos.size()
               << " goto statement(s)\n";

  // Match each goto to its target label
  for (GotoInfo &info : currentFunctionGotos) {
    std::string labelName = info.gotoStmt->getLabel()->getName().str();

    // Find matching label
    auto it = currentFunctionLabels.find(labelName);
    if (it == currentFunctionLabels.end()) {
      llvm::errs() << "  [Goto] Warning: Label '" << labelName
                   << "' not found for goto\n";
      continue;
    }

    info.targetLabel = it->second;

    // Check if this is a forward jump
    if (isForwardJump(info.gotoStmt, info.targetLabel)) {
      llvm::outs() << "  [Goto] Forward jump to '" << labelName << "'\n";

      // Analyze which objects need destruction
      info.liveObjects = analyzeObjectsForGoto(info.gotoStmt, info.targetLabel, FD);

      llvm::outs() << "    -> " << info.liveObjects.size()
                   << " object(s) need destruction before goto\n";
    } else {
      llvm::outs() << "  [Goto] Backward jump to '" << labelName
                   << "' (no destructor injection)\n";
      // Backward jumps: objects remain alive, no destruction needed
    }
  }
}

// Check if goto comes before its target label (forward jump)
bool CppToCVisitor::isForwardJump(GotoStmt *gotoStmt, LabelStmt *labelStmt) {
  if (!gotoStmt || !labelStmt) {
    return false;
  }

  SourceManager &SM = Context.getSourceManager();
  SourceLocation gotoLoc = gotoStmt->getBeginLoc();
  SourceLocation labelLoc = labelStmt->getBeginLoc();

  // Forward jump: goto comes before label in source
  return SM.isBeforeInTranslationUnit(gotoLoc, labelLoc);
}

// Determine which objects are live at goto and out of scope at label
std::vector<VarDecl*> CppToCVisitor::analyzeObjectsForGoto(
    GotoStmt *gotoStmt,
    LabelStmt *labelStmt,
    FunctionDecl *FD) {

  std::vector<VarDecl*> objectsToDestroy;

  if (!gotoStmt || !labelStmt || !FD) {
    return objectsToDestroy;
  }

  SourceManager &SM = Context.getSourceManager();
  SourceLocation gotoLoc = gotoStmt->getBeginLoc();
  SourceLocation labelLoc = labelStmt->getBeginLoc();

  // For each tracked object in the function
  for (VarDecl *VD : currentFunctionObjectsToDestroy) {
    SourceLocation varLoc = VD->getBeginLoc();

    // Object is live at goto if:
    // 1. It's declared before the goto
    // 2. It needs destruction (already filtered in tracking)
    if (SM.isBeforeInTranslationUnit(varLoc, gotoLoc)) {
      // For forward jumps, all objects constructed before goto need destruction
      // (This is a simplified analysis - a full implementation would check
      //  exact scope boundaries to determine if object is still in scope at label)
      objectsToDestroy.push_back(VD);
      llvm::outs() << "      - Will destroy: " << VD->getNameAsString() << "\n";
    }
  }

  return objectsToDestroy;
}

// ============================================================================
// Story #48: Loop Break/Continue Handling Methods
// ============================================================================

// Visit break statements for detection and tracking
bool CppToCVisitor::VisitBreakStmt(BreakStmt *BS) {
  // Skip if not analyzing a function
  if (currentFunctionObjectsToDestroy.empty() && scopeStack.empty()) {
    return true;
  }

  // Only track breaks inside loops (loopNestingLevel > 0)
  // Breaks in switch statements (loopNestingLevel == 0) are not tracked
  if (loopNestingLevel == 0) {
    llvm::outs() << "  [Break] Detected break in switch (no destructor injection)\n";
    return true;
  }

  llvm::outs() << "  [Break] Detected break in loop (nesting level: "
               << loopNestingLevel << ")\n";

  // Store break statement for later analysis
  BreakContinueInfo info;
  info.stmt = BS;
  info.isBreak = true;
  currentFunctionBreaksContinues.push_back(info);

  return true;
}

// Visit continue statements for detection and tracking
bool CppToCVisitor::VisitContinueStmt(ContinueStmt *CS) {
  // Skip if not analyzing a function
  if (currentFunctionObjectsToDestroy.empty() && scopeStack.empty()) {
    return true;
  }

  // Continue is only valid inside loops
  if (loopNestingLevel == 0) {
    llvm::errs() << "  [Continue] Warning: Continue outside loop (should not happen)\n";
    return true;
  }

  llvm::outs() << "  [Continue] Detected continue in loop (nesting level: "
               << loopNestingLevel << ")\n";

  // Store continue statement for later analysis
  BreakContinueInfo info;
  info.stmt = CS;
  info.isBreak = false;
  currentFunctionBreaksContinues.push_back(info);

  return true;
}

// Visit while statements to track loop nesting
bool CppToCVisitor::VisitWhileStmt(WhileStmt *WS) {
  // Don't increment here - we'll do it during traversal
  // This is just a marker visitor

  // Epic #193: Generate ACSL loop invariants if enabled
  if (m_loopAnnotator && getACSLLevel() == ACSLLevel::Full) {
    std::string loopInvariant = m_loopAnnotator->generateLoopAnnotations(WS);
    if (!loopInvariant.empty()) {
      emitACSL(loopInvariant, getACSLOutputMode());
    }
  }

  return true;
}

// Visit for statements to track loop nesting
bool CppToCVisitor::VisitForStmt(ForStmt *FS) {
  // Don't increment here - we'll do it during traversal
  // This is just a marker visitor

  // Epic #193: Generate ACSL loop invariants if enabled
  if (m_loopAnnotator && getACSLLevel() == ACSLLevel::Full) {
    std::string loopInvariant = m_loopAnnotator->generateLoopAnnotations(FS);
    if (!loopInvariant.empty()) {
      emitACSL(loopInvariant, getACSLOutputMode());
    }
  }

  return true;
}

// Visit do statements to track loop nesting
bool CppToCVisitor::VisitDoStmt(DoStmt *DS) {
  // Don't increment here - we'll do it during traversal
  // This is just a marker visitor

  // Epic #193: Generate ACSL loop invariants if enabled
  if (m_loopAnnotator && getACSLLevel() == ACSLLevel::Full) {
    std::string loopInvariant = m_loopAnnotator->generateLoopAnnotations(DS);
    if (!loopInvariant.empty()) {
      emitACSL(loopInvariant, getACSLOutputMode());
    }
  }

  return true;
}

// Visit range-based for statements to track loop nesting
bool CppToCVisitor::VisitCXXForRangeStmt(CXXForRangeStmt *FRS) {
  // Don't increment here - we'll do it during traversal
  // This is just a marker visitor

  // Epic #193: Note - CXXForRangeStmt not yet supported by ACSLLoopAnnotator
  // TODO: Add generateLoopAnnotations(const clang::CXXForRangeStmt *loop) overload to ACSLLoopAnnotator

  return true;
}

// Analyze break/continue statements and determine objects needing destruction
void CppToCVisitor::analyzeBreakContinueStatements(FunctionDecl *FD) {
  if (currentFunctionBreaksContinues.empty()) {
    return;  // No breaks/continues to analyze
  }

  llvm::outs() << "  [Break/Continue] Analyzing " << currentFunctionBreaksContinues.size()
               << " break/continue statement(s)\n";

  // For each break/continue statement
  for (BreakContinueInfo &info : currentFunctionBreaksContinues) {
    const char *stmtType = info.isBreak ? "break" : "continue";

    // Analyze which objects need destruction
    info.liveObjects = analyzeObjectsForBreakContinue(info.stmt, FD);

    llvm::outs() << "  [" << stmtType << "] " << info.liveObjects.size()
                 << " object(s) need destruction before " << stmtType << "\n";
  }
}

// Determine which objects are live at break/continue and need destruction
std::vector<VarDecl*> CppToCVisitor::analyzeObjectsForBreakContinue(
    Stmt *stmt,
    FunctionDecl *FD) {

  std::vector<VarDecl*> objectsToDestroy;

  if (!stmt || !FD) {
    return objectsToDestroy;
  }

  SourceManager &SM = Context.getSourceManager();
  SourceLocation stmtLoc = stmt->getBeginLoc();

  // For break/continue: destroy all loop-local objects that are live at this point
  // This includes:
  // 1. Objects declared in the loop body before this statement
  // 2. Objects declared in nested scopes that are still alive
  //
  // Simplified approach: Destroy all objects constructed before the break/continue

  for (VarDecl *VD : currentFunctionObjectsToDestroy) {
    SourceLocation varLoc = VD->getBeginLoc();

    // Object is live at break/continue if:
    // 1. It's declared before the break/continue
    // 2. It has a destructor (already filtered in tracking)
    if (SM.isBeforeInTranslationUnit(varLoc, stmtLoc)) {
      objectsToDestroy.push_back(VD);
      llvm::outs() << "      - Will destroy: " << VD->getNameAsString() << "\n";
    }
  }

  return objectsToDestroy;
}

// Visit compound statements for scope tracking
bool CppToCVisitor::VisitCompoundStmt(CompoundStmt *CS) {
  // We don't enter scope here because VisitCompoundStmt is called
  // during traversal, but we need to handle scope entry/exit during
  // translation (in translateCompoundStmt) to properly inject destructors
  // This visitor is just for detection/analysis if needed
  return true;
}

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
// Story #45: Modified to inject destructors before early returns
Stmt* CppToCVisitor::translateReturnStmt(ReturnStmt *RS) {
  // If we have objects to destroy at this return point, we need to
  // inject destructor calls before the return
  // This creates a compound statement: { dtors...; return; }

  Expr *RetValue = RS->getRetValue();
  Expr *TranslatedValue = nullptr;
  if (RetValue) {
    TranslatedValue = translateExpr(RetValue);
  }

  // Story #45: Check if we need to inject destructors before this return
  // For now, we'll do this during the VisitFunctionDecl analysis phase
  // The actual injection happens in a later pass
  // For this implementation, we just return the translated return statement

  if (TranslatedValue) {
    return Builder.returnStmt(TranslatedValue);
  }
  return Builder.returnStmt();
}

// Story #45: Helper - removed inline class since it needs access to private members
// The injection logic is now directly in translateCompoundStmt

// Translate compound statements (blocks)
// Story #46: Enhanced with scope tracking for nested destructor injection
Stmt* CppToCVisitor::translateCompoundStmt(CompoundStmt *CS) {
  // Story #46: Enter this scope
  enterScope(CS);

  std::vector<Stmt*> translatedStmts;

  // Translate all statements in the compound statement
  for (Stmt *S : CS->body()) {
    // Check if this is a VarDecl statement with a destructor
    if (DeclStmt *DS = dyn_cast<DeclStmt>(S)) {
      // Check if any decls in this statement have destructors
      for (Decl *D : DS->decls()) {
        if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
          if (hasNonTrivialDestructor(VD->getType())) {
            // Story #46: Track this object in current scope
            trackObjectInCurrentScope(VD);
          }
        }
      }
    }

    // Story #45: Check if this statement contains a return that needs injection
    if (ReturnStmt *RS = dyn_cast<ReturnStmt>(S)) {
      // Analyze live objects at this return point
      std::vector<VarDecl*> liveObjects = analyzeLiveObjectsAtReturn(RS, nullptr);

      if (!liveObjects.empty()) {
        llvm::outs() << "  Injecting " << liveObjects.size()
                     << " destructors before return in compound\n";

        // Inject destructors in reverse order (LIFO)
        for (auto it = liveObjects.rbegin(); it != liveObjects.rend(); ++it) {
          CallExpr *DtorCall = createDestructorCall(*it);
          if (DtorCall) {
            translatedStmts.push_back(DtorCall);
            llvm::outs() << "    -> " << (*it)->getNameAsString()
                         << " destructor before return\n";
          }
        }
      }

      // Translate and add the return statement
      Stmt *TranslatedStmt = translateStmt(S);
      if (TranslatedStmt) {
        translatedStmts.push_back(TranslatedStmt);
      }
    } else if (BreakStmt *BS = dyn_cast<BreakStmt>(S)) {
      // Story #48: Check if this break needs destructor injection
      for (const BreakContinueInfo &info : currentFunctionBreaksContinues) {
        if (info.stmt == BS && info.isBreak) {
          if (!info.liveObjects.empty()) {
            llvm::outs() << "  Injecting " << info.liveObjects.size()
                         << " destructors before break\n";

            // Inject destructors in reverse order (LIFO)
            for (auto it = info.liveObjects.rbegin(); it != info.liveObjects.rend(); ++it) {
              CallExpr *DtorCall = createDestructorCall(*it);
              if (DtorCall) {
                translatedStmts.push_back(DtorCall);
                llvm::outs() << "    -> " << (*it)->getNameAsString()
                             << " destructor before break\n";
              }
            }
          }
          break;  // Found the matching break info
        }
      }

      // Translate and add the break statement
      Stmt *TranslatedStmt = translateStmt(S);
      if (TranslatedStmt) {
        translatedStmts.push_back(TranslatedStmt);
      }
    } else if (ContinueStmt *CS_Cont = dyn_cast<ContinueStmt>(S)) {
      // Story #48: Check if this continue needs destructor injection
      for (const BreakContinueInfo &info : currentFunctionBreaksContinues) {
        if (info.stmt == CS_Cont && !info.isBreak) {
          if (!info.liveObjects.empty()) {
            llvm::outs() << "  Injecting " << info.liveObjects.size()
                         << " destructors before continue\n";

            // Inject destructors in reverse order (LIFO)
            for (auto it = info.liveObjects.rbegin(); it != info.liveObjects.rend(); ++it) {
              CallExpr *DtorCall = createDestructorCall(*it);
              if (DtorCall) {
                translatedStmts.push_back(DtorCall);
                llvm::outs() << "    -> " << (*it)->getNameAsString()
                             << " destructor before continue\n";
              }
            }
          }
          break;  // Found the matching continue info
        }
      }

      // Translate and add the continue statement
      Stmt *TranslatedStmt = translateStmt(S);
      if (TranslatedStmt) {
        translatedStmts.push_back(TranslatedStmt);
      }
    } else if (IfStmt *IS = dyn_cast<IfStmt>(S)) {
      // Story #45: Recursively handle nested if statements
      // Returns inside if blocks need destructor injection too
      Stmt *TranslatedStmt = translateStmt(S);
      if (TranslatedStmt) {
        translatedStmts.push_back(TranslatedStmt);
      }
    } else {
      // Regular statement translation (includes nested CompoundStmts)
      Stmt *TranslatedStmt = translateStmt(S);
      if (TranslatedStmt) {
        translatedStmts.push_back(TranslatedStmt);
      }
    }
  }

  // Story #46: Exit this scope and inject destructors for scope-local objects
  ScopeInfo exitedScope = exitScope();

  // Inject destructors for objects in THIS scope (not parent scopes)
  // LIFO order: reverse of declaration order
  if (!exitedScope.objects.empty()) {
    llvm::outs() << "  [Scope] Injecting " << exitedScope.objects.size()
                 << " destructor(s) at end of scope depth " << exitedScope.depth << "\n";

    for (auto it = exitedScope.objects.rbegin(); it != exitedScope.objects.rend(); ++it) {
      VarDecl *VD = *it;
      CallExpr *DtorCall = createDestructorCall(VD);
      if (DtorCall) {
        translatedStmts.push_back(DtorCall);
        llvm::outs() << "    -> " << VD->getNameAsString()
                     << " destructor injected at scope exit\n";
      }
    }
  }

  // Story #44: Legacy function-level tracking
  // Only inject if we're at depth 0 (function body) and have no scope stack
  // This maintains backward compatibility with Stories #44 and #45
  if (scopeStack.empty() && !currentFunctionObjectsToDestroy.empty()) {
    // This is the function body exiting - but objects are already handled by scope tracking
    // We can skip this if scope tracking handled them
    llvm::outs() << "  [Legacy] Function-level destruction already handled by scope tracking\n";
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

// ============================================================================
// Prompt #031: extern "C" and Calling Convention Support
// ============================================================================

/**
 * @brief Visit linkage specification declarations (extern "C" blocks)
 *
 * This visitor method is called automatically by Clang's AST traversal when
 * encountering extern "C" { } or extern "C++" { } blocks.
 *
 * Note: The actual linkage information is already available via
 * FunctionDecl::isExternC() and FunctionDecl::getLanguageLinkage(), so
 * this visitor is primarily for logging/debugging purposes.
 *
 * @param LS The LinkageSpecDecl node
 * @return true to continue visiting children
 */
bool CppToCVisitor::VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS) {
  if (!LS) {
    return true;
  }

  // Optional: Track entering extern "C" or extern "C++" blocks for debugging
  // TODO: Fix enum access for LLVM 15 - LinkageSpecDecl::LanguageIDs may have different API
  // if (LS->getLanguage() == LinkageSpecDecl::LanguageIDs::lang_c) {
  //   // This is an extern "C" block
  //   // In the future, we could add logging here if needed
  //   // llvm::outs() << "Entering extern \"C\" block\n";
  // } else if (LS->getLanguage() == LinkageSpecDecl::LanguageIDs::lang_cxx) {
  //   // This is an extern "C++" block (rare, but possible)
  //   // llvm::outs() << "Entering extern \"C++\" block\n";
  // }

  // Continue visiting child declarations (functions, variables, etc.)
  return true;
}

// ============================================================================
// Phase 12: Exception Handling Implementation
// ============================================================================
// NOTE: These visitor methods are commented out pending full Phase 12 integration
// They require additional member variables and includes that are not yet in the header

/* COMMENTED OUT FOR PHASE 13 - NEEDS PHASE 12 COMPLETION
bool CppToCVisitor::VisitCXXTryStmt(CXXTryStmt *S) {
  if (!S) {
    return true;
  }

  llvm::outs() << "Translating try-catch block...\n";

  // Generate unique frame and action table names
  std::string frameVarName = "frame_" + std::to_string(exceptionFrameCounter++);
  std::string actionsTableName = "actions_table_" + std::to_string(tryBlockCounter++);

  // Use TryCatchTransformer to generate complete try-catch code
  std::string transformedCode = TryCatchTransformerInstance.transformTryCatch(
    S, frameVarName, actionsTableName);

  // Output the transformed code
  llvm::outs() << transformedCode;

  llvm::outs() << "Try-catch block translated successfully\n";

  // Return false to prevent default traversal (we handle the try-catch block ourselves)
  return false;
}

bool CppToCVisitor::VisitCXXThrowExpr(CXXThrowExpr *E) {
  if (!E) {
    return true;
  }

  llvm::outs() << "Translating throw expression...\n";

  std::string throwCode;

  if (E->getSubExpr()) {
    // throw expression;
    throwCode = ThrowTranslatorInstance.generateThrowCode(E);
  } else {
    // throw; (re-throw)
    throwCode = ThrowTranslatorInstance.generateRethrowCode();
  }

  // Output the throw code
  llvm::outs() << throwCode;

  llvm::outs() << "Throw expression translated successfully\n";

  // Return true to indicate we've handled this
  return true;
}
END COMMENT */

// ============================================================================
// Epic #193: ACSL Annotation Generation Implementation
// ============================================================================

void CppToCVisitor::emitACSL(const std::string& acsl, ACSLOutputMode mode) {
  if (acsl.empty()) {
    return;  // Nothing to emit
  }

  if (mode == ACSLOutputMode::Inline) {
    // Emit ACSL as inline comments in the C output
    llvm::outs() << "/*@\n" << acsl << "\n*/\n";
  } else {
    // For separate mode, store the annotation for later output
    // Note: Actual file writing will be handled by FileOutputManager or Consumer
    // For now, we just output to stdout with a marker
    llvm::outs() << "/* ACSL (separate mode): */\n";
    llvm::outs() << "/*@\n" << acsl << "\n*/\n";
  }
}

void CppToCVisitor::storeACSLAnnotation(const std::string& key, const std::string& acsl) {
  if (!acsl.empty()) {
    m_acslAnnotations[key] = acsl;
  }
}

#pragma once

#include "ACSLAxiomaticBuilder.h"
#include "ACSLBehaviorAnnotator.h"
#include "ACSLClassAnnotator.h"
#include "ACSLFunctionAnnotator.h"
#include "ACSLGhostCodeInjector.h"
#include "ACSLLoopAnnotator.h"
#include "ACSLStatementAnnotator.h"
#include "ACSLTypeInvariantGenerator.h"
#include "AssumeAttributeHandler.h"
#include "AutoDecayCopyTranslator.h"
#include "CNodeBuilder.h"
#include "ConstevalIfTranslator.h"
#include "ConstexprEnhancementHandler.h"
#include "DeducingThisTranslator.h"
#include "DynamicCastTranslator.h"
#include "ExceptionFrameGenerator.h"
#include "FileOriginTracker.h"
#include "MoveAssignmentTranslator.h"
#include "MoveConstructorTranslator.h"
#include "MultidimSubscriptTranslator.h"
#include "NameMangler.h"
#include "StaticOperatorTranslator.h"
#include "OverrideResolver.h"
#include "RvalueRefParamTranslator.h"
#include "TemplateExtractor.h"
#include "TemplateInstantiationTracker.h"
#include "TemplateMonomorphizer.h"
#include "ThrowTranslator.h"
#include "TryCatchTransformer.h"
#include "TypeidTranslator.h"
#include "VirtualCallTranslator.h"
#include "VirtualMethodAnalyzer.h"
#include "VptrInjector.h"
#include "VtableGenerator.h"
#include "VtableInitializer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <map>
#include <memory>
#include <string>

// RecursiveASTVisitor that traverses C++ AST nodes
// Single Responsibility: Visit and identify AST nodes for translation
class CppToCVisitor : public clang::RecursiveASTVisitor<CppToCVisitor> {
  clang::ASTContext &Context;
  clang::CNodeBuilder &Builder;
  NameMangler Mangler;

  // Phase 34 (v2.5.0): File origin tracking for multi-file transpilation
  cpptoc::FileOriginTracker &fileOriginTracker;

  // Phase 9 (v2.2.0): Virtual method support
  VirtualMethodAnalyzer VirtualAnalyzer;
  VptrInjector VptrInjectorInstance;
  std::unique_ptr<OverrideResolver>
      m_overrideResolver; // Story #170: Override resolution
  std::unique_ptr<VtableGenerator>
      m_vtableGenerator; // Story #168: Vtable generation
  std::unique_ptr<VtableInitializer>
      m_vtableInitializer; // Story #171: Vtable initialization
  std::unique_ptr<VirtualCallTranslator>
      m_virtualCallTrans; // Story #172: Virtual call translation
  std::map<std::string, std::string>
      m_vtableInstances; // Store generated vtable instances (class -> vtable
                         // code)

  // Story #130: Move constructor translation
  MoveConstructorTranslator MoveCtorTranslator;

  // Story #131: Move assignment operator translation
  MoveAssignmentTranslator MoveAssignTranslator;

  // Story #133: Rvalue reference parameter translation
  RvalueRefParamTranslator RvalueRefParamTrans;

  // Epic #193: ACSL Annotation Generation
  std::unique_ptr<ACSLFunctionAnnotator> m_functionAnnotator;
  std::unique_ptr<ACSLLoopAnnotator> m_loopAnnotator;
  std::unique_ptr<ACSLClassAnnotator> m_classAnnotator;
  std::unique_ptr<ACSLStatementAnnotator> m_statementAnnotator;
  std::unique_ptr<ACSLTypeInvariantGenerator> m_typeInvariantGen;
  std::unique_ptr<ACSLAxiomaticBuilder> m_axiomaticBuilder;
  std::unique_ptr<ACSLGhostCodeInjector> m_ghostInjector;
  std::unique_ptr<ACSLBehaviorAnnotator> m_behaviorAnnotator;

  // Mapping: C++ class -> C struct (Story #15)
  std::map<clang::CXXRecordDecl *, clang::RecordDecl *> cppToCMap;

  // Mapping: C++ method -> C function (Story #16)
  std::map<clang::CXXMethodDecl *, clang::FunctionDecl *> methodToCFunc;

  // Mapping: C++ constructor -> C function (Story #17)
  std::map<clang::CXXConstructorDecl *, clang::FunctionDecl *> ctorMap;

  // Mapping: C++ destructor -> C function (Story #152 - Epic #5)
  std::map<clang::CXXDestructorDecl *, clang::FunctionDecl *> dtorMap;

  // Phase 8: Mapping: Standalone functions (by mangled name -> C function)
  std::map<std::string, clang::FunctionDecl *> standaloneFuncMap;

  // Track generated functions to prevent re-processing (fix for pointer recursion bug)
  std::set<clang::FunctionDecl *> generatedFunctions;

  // Phase 11: Template monomorphization infrastructure (v2.4.0)
  std::unique_ptr<TemplateExtractor> m_templateExtractor;
  std::unique_ptr<TemplateMonomorphizer> m_templateMonomorphizer;
  std::unique_ptr<TemplateInstantiationTracker> m_templateTracker;
  std::string m_monomorphizedCode; // Store generated template code

  // Phase 32: C TranslationUnit for generated C code
  clang::TranslationUnitDecl* C_TranslationUnit;

  // Phase 12: Exception handling infrastructure (v2.5.0)
  std::unique_ptr<clang::TryCatchTransformer> m_tryCatchTransformer;
  std::unique_ptr<clang::ThrowTranslator> m_throwTranslator;
  std::shared_ptr<ExceptionFrameGenerator> m_exceptionFrameGen;
  unsigned int m_exceptionFrameCounter = 0; // Counter for unique frame names
  unsigned int m_tryBlockCounter = 0; // Counter for unique action table names

  // Phase 13: RTTI infrastructure (v2.6.0)
  std::unique_ptr<TypeidTranslator> m_typeidTranslator;
  std::unique_ptr<DynamicCastTranslator> m_dynamicCastTranslator;

  // Phase 1: Multidimensional subscript operator support (C++23)
  std::unique_ptr<MultidimSubscriptTranslator> m_multidimSubscriptTrans;

  // Phase 2: Static operator() and operator[] support (C++23)
  std::unique_ptr<StaticOperatorTranslator> m_staticOperatorTrans;

  // Phase 3: [[assume]] attribute handling (C++23)
  std::unique_ptr<AssumeAttributeHandler> m_assumeHandler;

  // Phase 4: Deducing this / explicit object parameter support (C++23 P0847R7)
  std::unique_ptr<DeducingThisTranslator> m_deducingThisTrans;

  // Phase 5: if consteval support (C++23 P1938R3)
  std::unique_ptr<clang::ConstevalIfTranslator> m_constevalIfTrans;

  // Phase 6: auto(x) decay-copy and partial constexpr support (C++23 P0849R8)
  std::unique_ptr<AutoDecayCopyTranslator> m_autoDecayTrans;
  std::unique_ptr<ConstexprEnhancementHandler> m_constexprHandler;

  // Current translation context (Story #19)
  clang::ParmVarDecl *currentThisParam = nullptr;
  clang::CXXMethodDecl *currentMethod = nullptr;

  // Story #44: Track local objects with destructors for current function
  std::vector<clang::VarDecl *> currentFunctionObjectsToDestroy;

  // Story #45: Track return statements and their associated scopes
  struct ReturnInfo {
    clang::ReturnStmt *returnStmt;
    std::vector<clang::VarDecl *> liveObjects; // Objects live at this return
  };
  std::vector<ReturnInfo> currentFunctionReturns;

  // Story #46: Track nested scopes and scope-level objects
  struct ScopeInfo {
    clang::CompoundStmt *stmt; // The compound statement for this scope
    std::vector<clang::VarDecl *> objects; // Objects declared in this scope
    unsigned int depth;                    // Nesting depth (0 = function body)
  };
  std::vector<ScopeInfo> scopeStack; // Stack of currently active scopes

  // Story #47: Track goto statements and labels for destructor injection
  struct GotoInfo {
    clang::GotoStmt *gotoStmt;     // The goto statement
    clang::LabelStmt *targetLabel; // The target label (matched by name)
    std::vector<clang::VarDecl *>
        liveObjects; // Objects live at goto that need destruction
  };
  std::vector<GotoInfo>
      currentFunctionGotos; // Goto statements in current function
  std::map<std::string, clang::LabelStmt *>
      currentFunctionLabels; // Labels in current function

  // Story #48: Track break/continue statements in loops for destructor
  // injection
  struct BreakContinueInfo {
    clang::Stmt *stmt; // The break or continue statement
    bool isBreak;      // true = break, false = continue
    std::vector<clang::VarDecl *>
        liveObjects; // Objects live at break/continue that need destruction
  };
  std::vector<BreakContinueInfo>
      currentFunctionBreaksContinues; // Break/continue statements in current
                                      // function

  // Story #48: Track loop nesting to know when we're inside a loop
  unsigned int loopNestingLevel = 0; // 0 = not in loop, >0 = loop depth

public:
  explicit CppToCVisitor(clang::ASTContext &Context,
                         clang::CNodeBuilder &Builder,
                         cpptoc::FileOriginTracker &tracker);

  // Visit C++ class/struct declarations
  bool VisitCXXRecordDecl(clang::CXXRecordDecl *D);

  // Visit C++ member function declarations
  bool VisitCXXMethodDecl(clang::CXXMethodDecl *MD);

  // Visit C++ constructor declarations (Story #17)
  bool VisitCXXConstructorDecl(clang::CXXConstructorDecl *CD);

  // Visit C++ destructor declarations (Story #152 - Epic #5)
  bool VisitCXXDestructorDecl(clang::CXXDestructorDecl *DD);

  // Visit function declarations (Story #152 - for destructor injection)
  bool VisitFunctionDecl(clang::FunctionDecl *FD);

  // Visit variable declarations (including member variables)
  bool VisitVarDecl(clang::VarDecl *VD);

  // Visit compound statements for scope tracking (Story #46)
  bool VisitCompoundStmt(clang::CompoundStmt *CS);

  // Expression translation (Story #19)
  clang::Expr *translateExpr(clang::Expr *E);
  clang::Expr *translateDeclRefExpr(clang::DeclRefExpr *DRE);
  clang::Expr *translateMemberExpr(clang::MemberExpr *ME);
  clang::Expr *translateCallExpr(clang::CallExpr *CE);
  clang::Expr *translateBinaryOperator(clang::BinaryOperator *BO);
  clang::Expr *translateConstructExpr(clang::CXXConstructExpr *CCE);

  // Statement translation (Story #19)
  clang::Stmt *translateStmt(clang::Stmt *S);
  clang::Stmt *translateReturnStmt(clang::ReturnStmt *RS);
  clang::Stmt *translateCompoundStmt(clang::CompoundStmt *CS);
  clang::Stmt *translateDeclStmt(clang::DeclStmt *DS); // Phase 34-05

  // Story #45: Return statement visitor for early return detection
  bool VisitReturnStmt(clang::ReturnStmt *RS);

  // Story #47: Goto statement visitor for goto handling
  bool VisitGotoStmt(clang::GotoStmt *GS);

  // Story #47: Label statement visitor for goto target detection
  bool VisitLabelStmt(clang::LabelStmt *LS);

  // Story #48: Break statement visitor for loop break handling
  bool VisitBreakStmt(clang::BreakStmt *BS);

  // Story #48: Continue statement visitor for loop continue handling
  bool VisitContinueStmt(clang::ContinueStmt *CS);

  // Story #48: Loop statement visitors to track loop nesting
  bool VisitWhileStmt(clang::WhileStmt *WS);
  bool VisitForStmt(clang::ForStmt *FS);
  bool VisitDoStmt(clang::DoStmt *DS);
  bool VisitCXXForRangeStmt(clang::CXXForRangeStmt *FRS);

  // Prompt #031: extern "C" and calling convention support
  bool VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS);

  // Phase 11: Template monomorphization visitor methods (v2.4.0)
  bool VisitClassTemplateDecl(clang::ClassTemplateDecl *D);
  bool VisitFunctionTemplateDecl(clang::FunctionTemplateDecl *D);
  bool VisitClassTemplateSpecializationDecl(
      clang::ClassTemplateSpecializationDecl *D);

  // Phase 12: Exception handling visitor methods (v2.5.0)
  bool VisitCXXTryStmt(clang::CXXTryStmt *S);
  bool VisitCXXThrowExpr(clang::CXXThrowExpr *E);

  // Phase 13: RTTI visitor methods (v2.6.0)
  bool VisitCXXTypeidExpr(clang::CXXTypeidExpr *E);
  bool VisitCXXDynamicCastExpr(clang::CXXDynamicCastExpr *E);

  // Phase 1: Multidimensional subscript operator visitor (C++23)
  bool VisitCXXOperatorCallExpr(clang::CXXOperatorCallExpr *E);

  // Phase 3: [[assume]] attribute visitor (C++23)
  bool VisitAttributedStmt(clang::AttributedStmt *S);

  // Phase 5: if consteval visitor (C++23 P1938R3)
  bool VisitIfStmt(clang::IfStmt *S);

  // Phase 6: auto(x) decay-copy visitor (C++23 P0849R8)
  bool VisitCXXFunctionalCastExpr(clang::CXXFunctionalCastExpr *E);

  // Retrieve generated C struct by class name (for testing)
  clang::RecordDecl *getCStruct(llvm::StringRef className) const;

  // Retrieve generated C function by name (for testing)
  clang::FunctionDecl *getCFunc(llvm::StringRef funcName) const;

  // Retrieve generated C constructor function by name (for testing)
  clang::FunctionDecl *getCtor(llvm::StringRef funcName) const;

  // Retrieve generated C destructor function by name (for testing - Story #152)
  clang::FunctionDecl *getDtor(llvm::StringRef funcName) const;

  // Phase 11: Template Monomorphization Public Interface (v2.4.0)
  /**
   * @brief Process all template instantiations and generate monomorphized code
   * @param TU Translation unit declaration
   *
   * Single Responsibility: Orchestrate template extraction and monomorphization
   * Called after AST traversal to process all discovered template
   * instantiations.
   */
  void processTemplateInstantiations(clang::TranslationUnitDecl *TU);

  /**
   * @brief Get generated monomorphized template code
   * @return String containing all monomorphized C code
   */
  std::string getMonomorphizedCode() const { return m_monomorphizedCode; }

  /**
   * @brief Get the C TranslationUnit containing generated C AST nodes
   * @return Pointer to C TranslationUnitDecl
   *
   * Phase 32: Fix transpiler architecture - use C AST for output generation.
   * This method returns the C TranslationUnit that contains all generated C
   * AST nodes (structs, functions, etc.) which should be used for code
   * generation instead of the original C++ AST.
   */
  clang::TranslationUnitDecl* getCTranslationUnit() const {
    return C_TranslationUnit;
  }

private:
  // Epic #5: RAII helper methods

  /**
   * @brief Check if a type has a destructor that needs to be called
   * @param type The QualType to check
   * @return true if type has a non-trivial destructor
   */
  bool hasNonTrivialDestructor(clang::QualType type) const;

  /**
   * @brief Create destructor call expression for a variable
   * @param VD Variable declaration to destroy
   * @return CallExpr for the destructor call
   */
  clang::CallExpr *createDestructorCall(clang::VarDecl *VD);

  /**
   * @brief Inject destructor calls at end of compound statement
   * @param CS Compound statement to inject into
   * @param vars Variables to destroy (in reverse construction order)
   */
  void injectDestructorsAtScopeExit(clang::CompoundStmt *CS,
                                    const std::vector<clang::VarDecl *> &vars);

  /**
   * @brief Analyze which objects are live at a specific return statement
   * @param RS The return statement to analyze
   * @param FD The function containing the return
   * @return Vector of live objects at this return point
   *
   * Story #45: Scope analysis for early returns
   * Determines which objects with destructors are constructed and in scope
   * at the given return statement location.
   */
  std::vector<clang::VarDecl *>
  analyzeLiveObjectsAtReturn(clang::ReturnStmt *RS, clang::FunctionDecl *FD);

  /**
   * @brief Check if a statement/decl comes before another in control flow
   * @param Before The statement that should come first
   * @param After The statement that should come after
   * @return true if Before precedes After in the AST
   *
   * Story #45: Helper for scope analysis
   * Uses source location comparison to determine order.
   */
  bool comesBefore(clang::Stmt *Before, clang::Stmt *After);

  /**
   * @brief Enter a new scope (push onto scope stack)
   * @param CS The CompoundStmt representing this scope
   *
   * Story #46: Scope tracking for nested destructor injection
   * Called when entering a compound statement (scope).
   */
  void enterScope(clang::CompoundStmt *CS);

  /**
   * @brief Exit current scope (pop from scope stack)
   * @return ScopeInfo for the exited scope (contains objects to destroy)
   *
   * Story #46: Scope tracking for nested destructor injection
   * Called when exiting a compound statement (scope).
   * Returns the scope info so destructors can be injected.
   */
  ScopeInfo exitScope();

  /**
   * @brief Track a variable declaration in the current scope
   * @param VD Variable declaration to track
   *
   * Story #46: Associate objects with their declaration scope
   * Called when visiting VarDecls with non-trivial destructors.
   */
  void trackObjectInCurrentScope(clang::VarDecl *VD);

  /**
   * @brief Analyze goto-label pairs and determine objects needing destruction
   * @param FD The function containing goto statements
   *
   * Story #47: Goto-label analysis for destructor injection
   * Called after function traversal to match gotos to labels and identify
   * which objects need destruction before each goto (forward jumps only).
   */
  void analyzeGotoStatements(clang::FunctionDecl *FD);

  /**
   * @brief Check if goto comes before its target label (forward jump)
   * @param gotoStmt The goto statement
   * @param labelStmt The target label statement
   * @return true if goto precedes label in control flow
   *
   * Story #47: Helper for determining jump direction
   * Uses source location comparison to classify as forward or backward jump.
   */
  bool isForwardJump(clang::GotoStmt *gotoStmt, clang::LabelStmt *labelStmt);

  /**
   * @brief Determine which objects are live at goto and out of scope at label
   * @param gotoStmt The goto statement
   * @param labelStmt The target label statement
   * @param FD The function containing the goto
   * @return Vector of objects that need destruction before goto
   *
   * Story #47: Scope analysis for goto jumps
   * Identifies objects constructed before goto that won't be in scope at label.
   */
  std::vector<clang::VarDecl *>
  analyzeObjectsForGoto(clang::GotoStmt *gotoStmt, clang::LabelStmt *labelStmt,
                        clang::FunctionDecl *FD);

  // ============================================================================
  // Story #48: Loop Break/Continue Handling Methods
  // ============================================================================

  /**
   * @brief Analyze break/continue statements and determine objects needing
   * destruction
   * @param FD The function containing break/continue statements
   *
   * Story #48: Break/continue analysis for destructor injection
   * Called after function traversal to identify which objects need destruction
   * before each break/continue statement (all loop-local objects).
   */
  void analyzeBreakContinueStatements(clang::FunctionDecl *FD);

  /**
   * @brief Determine which objects are live at break/continue and need
   * destruction
   * @param stmt The break or continue statement
   * @param FD The function containing the statement
   * @return Vector of objects that need destruction before break/continue
   *
   * Story #48: Scope analysis for loop exits
   * Identifies all loop-local objects that need destruction before exiting
   * loop.
   */
  std::vector<clang::VarDecl *>
  analyzeObjectsForBreakContinue(clang::Stmt *stmt, clang::FunctionDecl *FD);

  // Epic #6: Single Inheritance helper methods

  /**
   * @brief Collect all base class fields in inheritance order
   * @param D The C++ class declaration
   * @param fields Output vector to append fields to
   *
   * Single Responsibility: Extract base field collection logic
   * Open/Closed: Can extend for multiple inheritance without modifying
   */
  void collectBaseClassFields(clang::CXXRecordDecl *D,
                              std::vector<clang::FieldDecl *> &fields);

  /**
   * @brief Create base constructor call statements for derived constructor
   * @param CD The C++ constructor declaration
   * @param thisParam The 'this' parameter of the derived constructor
   * @param stmts Output vector to append base constructor calls to
   *
   * Single Responsibility: Handle base constructor chaining logic (Story #51)
   * Open/Closed: Can extend for virtual inheritance without modifying
   *
   * This method processes base class initializers from the constructor's
   * member initialization list and generates calls to base class constructors.
   * Base constructor calls are added in the order they appear in the C++
   * source, ensuring proper initialization semantics.
   */
  void emitBaseConstructorCalls(clang::CXXConstructorDecl *CD,
                                clang::ParmVarDecl *thisParam,
                                std::vector<clang::Stmt *> &stmts);

  /**
   * @brief Create base destructor call statements for derived destructor
   * @param DD The C++ destructor declaration
   * @param thisParam The 'this' parameter of the derived destructor
   * @param stmts Output vector to append base destructor calls to
   *
   * Single Responsibility: Handle base destructor chaining logic (Story #52)
   * Open/Closed: Can extend for virtual inheritance without modifying
   *
   * This method identifies the base classes and generates calls to their
   * destructors. Base destructor calls are added AFTER the derived destructor
   * body, ensuring destruction order is reverse of construction (C++
   * semantics).
   */
  void emitBaseDestructorCalls(clang::CXXDestructorDecl *DD,
                               clang::ParmVarDecl *thisParam,
                               std::vector<clang::Stmt *> &stmts);

  // Story #63: Complete Constructor/Destructor Chaining

  /**
   * @brief Create member constructor call statements for constructor
   * @param CD The C++ constructor declaration
   * @param thisParam The 'this' parameter of the constructor
   * @param stmts Output vector to append member constructor calls to
   *
   * Single Responsibility: Handle member constructor calls (Story #63)
   * Open/Closed: Can extend for const/reference members without modifying
   *
   * Processes member fields in declaration order and generates constructor
   * calls for class-type members, either from explicit init list or default.
   */
  void emitMemberConstructorCalls(clang::CXXConstructorDecl *CD,
                                  clang::ParmVarDecl *thisParam,
                                  std::vector<clang::Stmt *> &stmts);

  /**
   * @brief Create member destructor call statements for destructor
   * @param ClassDecl The C++ class declaration
   * @param thisParam The 'this' parameter of the destructor
   * @param stmts Output vector to append member destructor calls to
   *
   * Single Responsibility: Handle member destructor calls (Story #63)
   * Open/Closed: Can extend for virtual destructors without modifying
   *
   * Processes member fields in REVERSE declaration order and generates
   * destructor calls for class-type members with non-trivial destructors.
   */
  void emitMemberDestructorCalls(clang::CXXRecordDecl *ClassDecl,
                                 clang::ParmVarDecl *thisParam,
                                 std::vector<clang::Stmt *> &stmts);

  /**
   * @brief Find initializer for a specific field in constructor init list
   * @param CD The C++ constructor declaration
   * @param Field The field to find initializer for
   * @return Initializer for the field, or nullptr if not found
   *
   * Single Responsibility: Lookup helper for member initializers
   */
  clang::CXXCtorInitializer *
  findInitializerForField(clang::CXXConstructorDecl *CD,
                          clang::FieldDecl *Field);

  // Epic #7: Implicit Constructor Generation (Story #62)

  /**
   * @brief Generate implicit constructors for a class if needed
   * @param D The C++ class declaration
   *
   * Single Responsibility: Orchestrate implicit constructor generation
   *
   * This method checks if the class needs implicit default or copy constructors
   * and generates them. Called from VisitCXXRecordDecl after struct creation.
   */
  void generateImplicitConstructors(clang::CXXRecordDecl *D);

  /**
   * @brief Generate default constructor for a class
   * @param D The C++ class declaration
   * @return Generated default constructor function
   *
   * Single Responsibility: Build default constructor with zero-initialization
   *
   * Generates: Class__ctor_default(struct Class *this)
   * - Zero-initializes primitive members
   * - Calls default constructors for class-type members
   * - Calls base class default constructor if derived
   */
  clang::FunctionDecl *generateDefaultConstructor(clang::CXXRecordDecl *D);

  /**
   * @brief Generate copy constructor for a class
   * @param D The C++ class declaration
   * @return Generated copy constructor function
   *
   * Single Responsibility: Build copy constructor with memberwise copy
   *
   * Generates: Class__ctor_copy(struct Class *this, const struct Class *other)
   * - Performs memberwise copy for primitive members
   * - Calls copy constructors for class-type members
   * - Performs shallow copy for pointer members
   * - Calls base class copy constructor if derived
   */
  clang::FunctionDecl *generateCopyConstructor(clang::CXXRecordDecl *D);

  /**
   * @brief Check if class needs implicit default constructor
   * @param D The C++ class declaration
   * @return true if default constructor should be generated
   *
   * Returns true if:
   * - No user-declared constructors exist
   */
  bool needsImplicitDefaultConstructor(clang::CXXRecordDecl *D) const;

  /**
   * @brief Check if class needs implicit copy constructor
   * @param D The C++ class declaration
   * @return true if copy constructor should be generated
   *
   * Returns true if:
   * - No user-declared copy constructor exists
   * - Class has at least one constructor (explicit or default)
   */
  bool needsImplicitCopyConstructor(clang::CXXRecordDecl *D) const;

  // ============================================================================
  // Epic #193: ACSL Annotation Generation Helper Methods
  // ============================================================================

  /**
   * @brief Emit ACSL annotation based on output mode
   * @param acsl The ACSL annotation string to emit
   * @param mode Output mode (Inline or Separate)
   *
   * Single Responsibility: Handle ACSL output emission
   * Inline mode: Sends ACSL to current output stream as comments
   * Separate mode: Writes ACSL to separate .acsl file
   */
  void emitACSL(const std::string &acsl, ACSLOutputMode mode);

  /**
   * @brief Store ACSL annotations for later output
   * @param key Identifier for the annotation (e.g., function name)
   * @param acsl The ACSL annotation string
   *
   * Used when --acsl-output=separate is specified
   */
  void storeACSLAnnotation(const std::string &key, const std::string &acsl);

  // Storage for ACSL annotations when using separate output mode
  std::map<std::string, std::string> m_acslAnnotations;

  // ============================================================================
  // Phase 31-03: COM-Style Static Declarations for All Methods
  // ============================================================================

  /**
   * @brief Generate static declarations for ALL methods (virtual and non-virtual)
   * @param RD The class declaration
   * @return C code for static function declarations
   *
   * Generates static function declarations for all methods in a class,
   * providing compile-time type safety for all method signatures.
   * This includes constructors, destructors, and all regular methods.
   */
  std::string generateAllMethodDeclarations(clang::CXXRecordDecl* RD);
};

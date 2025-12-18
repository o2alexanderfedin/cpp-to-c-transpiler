#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ASTContext.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include "VirtualMethodAnalyzer.h"
#include "VptrInjector.h"
#include "MoveConstructorTranslator.h"
#include <map>
#include <string>

// RecursiveASTVisitor that traverses C++ AST nodes
// Single Responsibility: Visit and identify AST nodes for translation
class CppToCVisitor : public clang::RecursiveASTVisitor<CppToCVisitor> {
  clang::ASTContext &Context;
  clang::CNodeBuilder &Builder;
  NameMangler Mangler;

  // Story #169: Virtual function support
  VirtualMethodAnalyzer VirtualAnalyzer;
  VptrInjector VptrInjectorInstance;

  // Story #130: Move constructor translation
  MoveConstructorTranslator MoveCtorTranslator;

  // Mapping: C++ class -> C struct (Story #15)
  std::map<clang::CXXRecordDecl*, clang::RecordDecl*> cppToCMap;

  // Mapping: C++ method -> C function (Story #16)
  std::map<clang::CXXMethodDecl*, clang::FunctionDecl*> methodToCFunc;

  // Mapping: C++ constructor -> C function (Story #17)
  std::map<clang::CXXConstructorDecl*, clang::FunctionDecl*> ctorMap;

  // Mapping: C++ destructor -> C function (Story #152 - Epic #5)
  std::map<clang::CXXDestructorDecl*, clang::FunctionDecl*> dtorMap;

  // Current translation context (Story #19)
  clang::ParmVarDecl *currentThisParam = nullptr;
  clang::CXXMethodDecl *currentMethod = nullptr;

public:
  explicit CppToCVisitor(clang::ASTContext &Context, clang::CNodeBuilder &Builder)
    : Context(Context), Builder(Builder), Mangler(Context),
      VirtualAnalyzer(Context), VptrInjectorInstance(Context, VirtualAnalyzer),
      MoveCtorTranslator(Context) {}

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

  // Retrieve generated C constructor function by name (for testing)
  clang::FunctionDecl* getCtor(llvm::StringRef funcName) const;

  // Retrieve generated C destructor function by name (for testing - Story #152)
  clang::FunctionDecl* getDtor(llvm::StringRef funcName) const;

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
  clang::CallExpr* createDestructorCall(clang::VarDecl *VD);

  /**
   * @brief Inject destructor calls at end of compound statement
   * @param CS Compound statement to inject into
   * @param vars Variables to destroy (in reverse construction order)
   */
  void injectDestructorsAtScopeExit(clang::CompoundStmt *CS,
                                    const std::vector<clang::VarDecl*> &vars);

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
                               std::vector<clang::FieldDecl*> &fields);

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
                                 std::vector<clang::Stmt*> &stmts);

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
   * body, ensuring destruction order is reverse of construction (C++ semantics).
   */
  void emitBaseDestructorCalls(clang::CXXDestructorDecl *DD,
                                clang::ParmVarDecl *thisParam,
                                std::vector<clang::Stmt*> &stmts);

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
                                   std::vector<clang::Stmt*> &stmts);

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
                                  std::vector<clang::Stmt*> &stmts);

  /**
   * @brief Find initializer for a specific field in constructor init list
   * @param CD The C++ constructor declaration
   * @param Field The field to find initializer for
   * @return Initializer for the field, or nullptr if not found
   *
   * Single Responsibility: Lookup helper for member initializers
   */
  clang::CXXCtorInitializer* findInitializerForField(
      clang::CXXConstructorDecl *CD,
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
  clang::FunctionDecl* generateDefaultConstructor(clang::CXXRecordDecl *D);

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
  clang::FunctionDecl* generateCopyConstructor(clang::CXXRecordDecl *D);

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
};

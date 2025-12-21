#pragma once

#include "LambdaCapture.h"
#include "NameMangler.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ExprCXX.h"
#include <map>
#include <string>
#include <vector>

/**
 * @file LambdaTranslator.h
 * @brief Lambda expression translation to C closures
 *
 * Phase 10 (v2.3.0): Lambda Expression Translation
 * Single Responsibility: Translate lambda expressions to C function pointers +
 * closures Open/Closed: Can extend for new lambda patterns without modifying
 * core
 */

namespace clang {

/**
 * @struct LambdaTranslation
 * @brief Complete translation of a lambda expression to C
 */
struct LambdaTranslation {
  std::string closureStructName; // e.g., "lambda_closure_0"
  std::string closureStructDef;  // C struct definition
  std::string funcName;          // e.g., "lambda_func_0"
  std::string funcDef;           // C function definition
  std::string funcSignature;     // Function signature (for typedef)
  std::map<std::string, CaptureInfo> captures; // Capture information
  bool isMutable;                              // Is lambda mutable?
  bool isGeneric;                              // Has auto parameters?
  clang::LambdaExpr *lambdaExpr;               // Original lambda expression

  LambdaTranslation()
      : isMutable(false), isGeneric(false), lambdaExpr(nullptr) {}
};

/**
 * @class LambdaTranslator
 * @brief Translates C++ lambda expressions to C function pointers + closures
 *
 * Single Responsibility: Orchestrate lambda-to-C translation
 * Dependency Inversion: Depends on LambdaCaptureAnalyzer and NameMangler
 * abstractions
 *
 * Translation Strategy:
 * 1. Analyze captures (LambdaCaptureAnalyzer)
 * 2. Generate closure struct (holds captured variables)
 * 3. Generate lambda function (takes closure pointer + parameters)
 * 4. Generate invocation code (initialize closure + call function)
 */
class LambdaTranslator {
  clang::ASTContext &Context;
  LambdaCaptureAnalyzer CaptureAnalyzer;
  NameMangler &Mangler;
  unsigned int lambdaCounter; // Unique ID for each lambda

  // Storage: LambdaExpr -> LambdaTranslation
  std::map<const clang::LambdaExpr *, LambdaTranslation> translations;

public:
  explicit LambdaTranslator(clang::ASTContext &Context, NameMangler &Mangler);

  /**
   * @brief Translate a lambda expression to C
   * @param E Lambda expression
   * @return LambdaTranslation containing all generated C code
   *
   * Main entry point for lambda translation.
   * Orchestrates capture analysis, struct generation, and function generation.
   */
  LambdaTranslation translateLambda(clang::LambdaExpr *E);

  /**
   * @brief Generate closure struct definition
   * @param closureName Closure struct name (e.g., "lambda_closure_0")
   * @param captures Map of captured variables
   * @return C struct definition string
   *
   * Example output:
   * struct lambda_closure_0 {
   *   int x;      // value capture
   *   int *y;     // reference capture
   * };
   */
  std::string generateClosureStruct(
      const std::string &closureName,
      const std::map<std::string, CaptureInfo> &captures);

  /**
   * @brief Generate lambda function definition
   * @param funcName Function name (e.g., "lambda_func_0")
   * @param closureName Closure struct name
   * @param E Lambda expression
   * @param captures Capture information
   * @param isMutable Is lambda mutable?
   * @return C function definition string
   *
   * Example output:
   * int lambda_func_0(struct lambda_closure_0 *closure, int z) {
   *   return closure->x + *closure->y + z;
   * }
   */
  std::string generateLambdaFunction(
      const std::string &funcName, const std::string &closureName,
      clang::LambdaExpr *E, const std::map<std::string, CaptureInfo> &captures,
      bool isMutable);

  /**
   * @brief Generate closure initialization code
   * @param translation Lambda translation info
   * @return C code to initialize closure struct
   *
   * Example output:
   * struct lambda_closure_0 closure;
   * closure.x = x;
   * closure.y = &y;
   */
  std::string generateClosureInit(const LambdaTranslation &translation);

  /**
   * @brief Generate lambda invocation code
   * @param translation Lambda translation info
   * @param args Function call arguments
   * @return C code to invoke lambda function
   *
   * Example output:
   * lambda_func_0(&closure, arg1, arg2)
   */
  std::string generateLambdaCall(const LambdaTranslation &translation,
                                  const std::vector<std::string> &args);

  /**
   * @brief Get translation for a lambda expression
   * @param E Lambda expression
   * @return Pointer to LambdaTranslation, or nullptr if not found
   */
  const LambdaTranslation *getTranslation(const clang::LambdaExpr *E) const;

  /**
   * @brief Check if lambda is generic (has auto parameters)
   * @param E Lambda expression
   * @return true if lambda has at least one auto parameter
   */
  bool isGenericLambda(clang::LambdaExpr *E) const;

  /**
   * @brief Generate specialized function for generic lambda
   * @param translation Base lambda translation
   * @param instantiationType Type for auto parameter
   * @return Function definition for this instantiation
   *
   * For generic lambdas with auto parameters, generates type-specific
   * functions: lambda_func_0_int(closure, int z) lambda_func_0_double(closure,
   * double z)
   */
  std::string
  generateGenericInstantiation(const LambdaTranslation &translation,
                                const std::string &instantiationType);

private:
  /**
   * @brief Generate unique lambda identifier
   * @return Unique string ID (e.g., "lambda_0")
   */
  std::string generateLambdaId();

  /**
   * @brief Translate lambda body to C statements
   * @param body Lambda body (CompoundStmt)
   * @param captures Capture information
   * @param closureName Closure struct name
   * @return C code for lambda body
   *
   * Rewrites variable references to use closure members:
   * - "x" becomes "closure->x" (value capture)
   * - "y" becomes "*closure->y" (reference capture)
   */
  std::string translateLambdaBody(const clang::Stmt *body,
                                   const std::map<std::string, CaptureInfo> &captures,
                                   const std::string &closureName);

  /**
   * @brief Get C function signature for lambda
   * @param E Lambda expression
   * @param closureName Closure struct name
   * @return Function signature string
   *
   * Example: "int (*)(struct lambda_closure_0*, int)"
   */
  std::string getFunctionSignature(clang::LambdaExpr *E,
                                    const std::string &closureName);

  /**
   * @brief Get parameter list for lambda function
   * @param E Lambda expression
   * @return C parameter list string (e.g., "int x, int y")
   */
  std::string getParameterList(clang::LambdaExpr *E);

  /**
   * @brief Get return type for lambda
   * @param E Lambda expression
   * @return C return type string
   */
  std::string getReturnType(clang::LambdaExpr *E);

  /**
   * @brief Rewrite DeclRefExpr to use closure
   * @param varName Variable name
   * @param captures Capture information
   * @param closureName Closure struct name
   * @return Rewritten expression (e.g., "closure->x" or "*closure->y")
   */
  std::string rewriteVariableReference(
      const std::string &varName,
      const std::map<std::string, CaptureInfo> &captures,
      const std::string &closureName);
};

} // namespace clang

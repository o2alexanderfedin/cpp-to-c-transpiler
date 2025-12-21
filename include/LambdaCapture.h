#pragma once

#include "clang/AST/ASTContext.h"
#include "clang/AST/ExprCXX.h"
#include <map>
#include <string>
#include <vector>

/**
 * @file LambdaCapture.h
 * @brief Lambda capture analysis for C++ to C transpiler
 *
 * Phase 10 (v2.3.0): Lambda Expression Translation
 * Single Responsibility: Analyze lambda captures and classify their types
 * Open/Closed: Can extend for new capture patterns without modifying core
 */

namespace clang {

/**
 * @enum CaptureMode
 * @brief Classification of how a variable is captured in a lambda
 */
enum class CaptureMode {
  BY_VALUE,            // [x] - Copy variable value into closure
  BY_REFERENCE,        // [&x] - Store pointer to variable in closure
  IMPLICIT_VALUE,      // [=] - Default capture by value
  IMPLICIT_REFERENCE,  // [&] - Default capture by reference
  THIS_POINTER,        // [this] - Capture this pointer
  THIS_COPY            // [*this] - Capture copy of *this (C++17)
};

/**
 * @struct CaptureInfo
 * @brief Information about a single captured variable
 */
struct CaptureInfo {
  std::string varName;          // Variable name
  std::string typeName;         // C type name for the variable
  CaptureMode mode;             // How it's captured
  clang::QualType type;         // Original Clang type
  const clang::VarDecl *varDecl; // Original variable declaration (if available)
  bool isMutable;               // Is this capture mutable?

  CaptureInfo()
      : varName(""), typeName(""), mode(CaptureMode::BY_VALUE),
        varDecl(nullptr), isMutable(false) {}
};

/**
 * @class LambdaCaptureAnalyzer
 * @brief Analyzes lambda captures and extracts capture information
 *
 * Single Responsibility: Extract and classify lambda captures
 * Interface Segregation: Minimal interface for capture analysis
 * Dependency Inversion: Depends on Clang AST abstractions
 */
class LambdaCaptureAnalyzer {
  clang::ASTContext &Context;

public:
  explicit LambdaCaptureAnalyzer(clang::ASTContext &Context);

  /**
   * @brief Analyze all captures in a lambda expression
   * @param E Lambda expression to analyze
   * @return Map of variable name -> CaptureInfo
   *
   * Analyzes both explicit captures (e.g., [x, &y]) and implicit captures
   * (e.g., [=], [&]). Handles mixed capture modes (e.g., [=, &y]).
   */
  std::map<std::string, CaptureInfo> analyzeCaptures(clang::LambdaExpr *E);

  /**
   * @brief Determine if lambda has default capture mode
   * @param E Lambda expression
   * @return true if lambda uses [=] or [&]
   */
  bool hasDefaultCapture(clang::LambdaExpr *E) const;

  /**
   * @brief Get default capture mode
   * @param E Lambda expression
   * @return IMPLICIT_VALUE for [=], IMPLICIT_REFERENCE for [&]
   */
  CaptureMode getDefaultCaptureMode(clang::LambdaExpr *E) const;

  /**
   * @brief Get C type name for a captured variable
   * @param type QualType of the variable
   * @param mode Capture mode
   * @return C type string (e.g., "int", "int*" for reference)
   *
   * Reference captures become pointers in C.
   * Value captures retain their original type.
   */
  std::string getCTypeName(clang::QualType type, CaptureMode mode) const;

  /**
   * @brief Analyze implicit captures (variables referenced in lambda body)
   * @param E Lambda expression
   * @param defaultMode Default capture mode ([=] or [&])
   * @return Map of implicitly captured variable names -> CaptureInfo
   *
   * Scans lambda body to find all variable references.
   * Only includes variables not already in explicit capture list.
   */
  std::map<std::string, CaptureInfo>
  analyzeImplicitCaptures(clang::LambdaExpr *E, CaptureMode defaultMode);

private:
  /**
   * @brief Process a single lambda capture
   * @param capture Lambda capture from Clang
   * @param E Parent lambda expression
   * @return CaptureInfo for this capture
   */
  CaptureInfo processCapture(const clang::LambdaCapture &capture,
                               clang::LambdaExpr *E);

  /**
   * @brief Find all variable references in lambda body
   * @param body Lambda body statement
   * @return Vector of referenced variable declarations
   *
   * Helper for implicit capture analysis.
   * Recursively traverses lambda body to find all DeclRefExprs.
   */
  std::vector<const clang::VarDecl *>
  findReferencedVariables(const clang::Stmt *body);

  /**
   * @brief Check if variable is already explicitly captured
   * @param varName Variable name
   * @param explicitCaptures Map of explicit captures
   * @return true if variable is in explicit capture list
   */
  bool isExplicitlyCaptured(
      const std::string &varName,
      const std::map<std::string, CaptureInfo> &explicitCaptures) const;
};

} // namespace clang

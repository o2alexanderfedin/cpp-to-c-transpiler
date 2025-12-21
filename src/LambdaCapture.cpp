#include "LambdaCapture.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>

using namespace clang;

// ============================================================================
// LambdaCaptureAnalyzer Implementation
// ============================================================================

LambdaCaptureAnalyzer::LambdaCaptureAnalyzer(ASTContext &Context)
    : Context(Context) {}

std::map<std::string, CaptureInfo>
LambdaCaptureAnalyzer::analyzeCaptures(LambdaExpr *E) {
  std::map<std::string, CaptureInfo> captures;

  // Step 1: Process explicit captures
  for (const auto &capture : E->captures()) {
    CaptureInfo info = processCapture(capture, E);
    if (!info.varName.empty()) {
      captures[info.varName] = info;
    }
  }

  // Step 2: If default capture exists, process implicit captures
  if (hasDefaultCapture(E)) {
    CaptureMode defaultMode = getDefaultCaptureMode(E);
    auto implicitCaptures = analyzeImplicitCaptures(E, defaultMode);

    // Merge implicit captures (only add if not already explicitly captured)
    for (const auto &entry : implicitCaptures) {
      if (captures.find(entry.first) == captures.end()) {
        captures[entry.first] = entry.second;
      }
    }
  }

  return captures;
}

bool LambdaCaptureAnalyzer::hasDefaultCapture(LambdaExpr *E) const {
  return E->getCaptureDefault() != LCD_None;
}

CaptureMode LambdaCaptureAnalyzer::getDefaultCaptureMode(LambdaExpr *E) const {
  switch (E->getCaptureDefault()) {
  case LCD_ByCopy:
    return CaptureMode::IMPLICIT_VALUE;
  case LCD_ByRef:
    return CaptureMode::IMPLICIT_REFERENCE;
  case LCD_None:
  default:
    return CaptureMode::BY_VALUE; // Fallback
  }
}

std::string LambdaCaptureAnalyzer::getCTypeName(QualType type,
                                                 CaptureMode mode) const {
  // For reference captures, we use pointers in C
  if (mode == CaptureMode::BY_REFERENCE ||
      mode == CaptureMode::IMPLICIT_REFERENCE) {
    // Get the underlying type (without const/volatile)
    QualType pointeeType = type.getNonReferenceType();
    std::string baseType = pointeeType.getAsString();

    // Remove const/volatile qualifiers for pointer target
    baseType = pointeeType.getUnqualifiedType().getAsString();

    return baseType + " *";
  }

  // For value captures, use the type directly
  QualType valueType = type.getNonReferenceType().getUnqualifiedType();
  return valueType.getAsString();
}

CaptureInfo
LambdaCaptureAnalyzer::processCapture(const LambdaCapture &capture,
                                       LambdaExpr *E) {
  CaptureInfo info;

  // Handle 'this' capture
  if (capture.capturesThis()) {
    info.varName = "this";
    info.mode = CaptureMode::THIS_POINTER;
    info.typeName = "void*"; // this is a pointer

    // Check for [*this] (copy capture of this)
    if (capture.getCaptureKind() == LCK_StarThis) {
      info.mode = CaptureMode::THIS_COPY;
      // Need to get the actual class type
      const CXXRecordDecl *lambdaClass = E->getLambdaClass();
      if (lambdaClass && lambdaClass->getNumBases() > 0) {
        // Get parent class type
        info.typeName = "struct " +
                        lambdaClass->bases_begin()->getType().getAsString();
      }
    }

    return info;
  }

  // Handle variable capture
  if (!capture.capturesVariable()) {
    return info; // Return empty info
  }

  const VarDecl *varDecl = capture.getCapturedVar();
  if (!varDecl) {
    return info;
  }

  info.varName = varDecl->getNameAsString();
  info.varDecl = varDecl;
  info.type = varDecl->getType();

  // Determine capture mode
  switch (capture.getCaptureKind()) {
  case LCK_ByCopy:
    info.mode = CaptureMode::BY_VALUE;
    break;
  case LCK_ByRef:
    info.mode = CaptureMode::BY_REFERENCE;
    break;
  case LCK_VLAType:
    info.mode = CaptureMode::BY_VALUE; // VLA captured by value
    break;
  case LCK_StarThis:
    info.mode = CaptureMode::THIS_COPY;
    break;
  case LCK_This:
    info.mode = CaptureMode::THIS_POINTER;
    break;
  }

  // Get C type name
  info.typeName = getCTypeName(info.type, info.mode);

  return info;
}

// Helper visitor to find variable references in lambda body
class VarRefFinder : public RecursiveASTVisitor<VarRefFinder> {
public:
  std::vector<const VarDecl *> referencedVars;

  bool VisitDeclRefExpr(DeclRefExpr *E) {
    if (const VarDecl *VD = dyn_cast<VarDecl>(E->getDecl())) {
      // Only add if not already in list
      if (std::find(referencedVars.begin(), referencedVars.end(), VD) ==
          referencedVars.end()) {
        referencedVars.push_back(VD);
      }
    }
    return true;
  }

  // Don't descend into nested lambdas
  bool TraverseLambdaExpr(LambdaExpr *E) { return true; }
};

std::vector<const VarDecl *>
LambdaCaptureAnalyzer::findReferencedVariables(const Stmt *body) {
  VarRefFinder finder;
  finder.TraverseStmt(const_cast<Stmt *>(body));
  return finder.referencedVars;
}

std::map<std::string, CaptureInfo>
LambdaCaptureAnalyzer::analyzeImplicitCaptures(LambdaExpr *E,
                                                 CaptureMode defaultMode) {
  std::map<std::string, CaptureInfo> implicitCaptures;

  // Get lambda body
  const CXXMethodDecl *callOp = E->getCallOperator();
  if (!callOp || !callOp->hasBody()) {
    return implicitCaptures;
  }

  const Stmt *body = callOp->getBody();

  // Find all variable references in body
  std::vector<const VarDecl *> referencedVars = findReferencedVariables(body);

  // Build map of explicit captures for quick lookup
  std::map<std::string, CaptureInfo> explicitCaptures;
  for (const auto &capture : E->captures()) {
    if (capture.capturesVariable()) {
      const VarDecl *VD = capture.getCapturedVar();
      if (VD) {
        explicitCaptures[VD->getNameAsString()] = CaptureInfo();
      }
    }
  }

  // Process referenced variables
  for (const VarDecl *VD : referencedVars) {
    std::string varName = VD->getNameAsString();

    // Skip if already explicitly captured
    if (isExplicitlyCaptured(varName, explicitCaptures)) {
      continue;
    }

    // Skip local variables declared in lambda
    if (VD->getDeclContext() == callOp) {
      continue;
    }

    // Skip function parameters (they're not captures)
    if (isa<ParmVarDecl>(VD)) {
      // Check if it's a parameter of the lambda itself
      for (const auto *param : callOp->parameters()) {
        if (param == VD) {
          goto skip_var; // It's a lambda parameter, not a capture
        }
      }
    }

    // Create capture info for this implicit capture
    CaptureInfo info;
    info.varName = varName;
    info.varDecl = VD;
    info.type = VD->getType();
    info.mode = defaultMode;
    info.typeName = getCTypeName(info.type, info.mode);

    implicitCaptures[varName] = info;

  skip_var:
    continue;
  }

  return implicitCaptures;
}

bool LambdaCaptureAnalyzer::isExplicitlyCaptured(
    const std::string &varName,
    const std::map<std::string, CaptureInfo> &explicitCaptures) const {
  return explicitCaptures.find(varName) != explicitCaptures.end();
}

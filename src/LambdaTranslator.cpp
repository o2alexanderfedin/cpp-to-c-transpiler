#include "LambdaTranslator.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

using namespace clang;

// ============================================================================
// LambdaTranslator Implementation
// ============================================================================

LambdaTranslator::LambdaTranslator(ASTContext &Context, NameMangler &Mangler)
    : Context(Context), CaptureAnalyzer(Context), Mangler(Mangler),
      lambdaCounter(0) {}

LambdaTranslation LambdaTranslator::translateLambda(LambdaExpr *E) {
  LambdaTranslation translation;
  translation.lambdaExpr = E;

  // Step 1: Generate unique lambda ID
  std::string lambdaId = generateLambdaId();

  // Step 2: Analyze captures
  translation.captures = CaptureAnalyzer.analyzeCaptures(E);

  // Step 3: Determine lambda properties
  translation.isMutable = E->isMutable();
  translation.isGeneric = isGenericLambda(E);

  // Step 4: Generate closure struct name and definition
  translation.closureStructName = lambdaId + "_closure";
  translation.closureStructDef =
      generateClosureStruct(translation.closureStructName, translation.captures);

  // Step 5: Generate lambda function name and definition
  translation.funcName = lambdaId + "_func";
  translation.funcDef = generateLambdaFunction(
      translation.funcName, translation.closureStructName, E,
      translation.captures, translation.isMutable);

  // Step 6: Generate function signature (for typedef)
  translation.funcSignature =
      getFunctionSignature(E, translation.closureStructName);

  // Step 7: Store translation for later retrieval
  translations[E] = translation;

  return translation;
}

std::string LambdaTranslator::generateClosureStruct(
    const std::string &closureName,
    const std::map<std::string, CaptureInfo> &captures) {

  std::ostringstream oss;

  // Generate struct definition
  oss << "struct " << closureName << " {\n";

  if (captures.empty()) {
    // Empty closure (stateless lambda)
    oss << "    char dummy;  /* Empty closure */\n";
  } else {
    // Generate member for each capture
    for (const auto &entry : captures) {
      const CaptureInfo &info = entry.second;
      oss << "    " << info.typeName << " " << info.varName << ";\n";
    }
  }

  oss << "};\n";

  return oss.str();
}

std::string LambdaTranslator::generateLambdaFunction(
    const std::string &funcName, const std::string &closureName,
    LambdaExpr *E, const std::map<std::string, CaptureInfo> &captures,
    bool isMutable) {

  std::ostringstream oss;

  // Get return type
  std::string returnType = getReturnType(E);

  // Get parameter list
  std::string params = getParameterList(E);

  // Generate function signature
  oss << returnType << " " << funcName << "(";

  // Add closure pointer parameter
  if (isMutable) {
    oss << "struct " << closureName << " *__closure";
  } else {
    oss << "const struct " << closureName << " *__closure";
  }

  // Add lambda parameters
  if (!params.empty()) {
    oss << ", " << params;
  }

  oss << ") {\n";

  // Translate lambda body
  const CXXMethodDecl *callOp = E->getCallOperator();
  if (callOp && callOp->hasBody()) {
    std::string body = translateLambdaBody(callOp->getBody(), captures, "__closure");
    oss << body;
  }

  oss << "}\n";

  return oss.str();
}

std::string
LambdaTranslator::generateClosureInit(const LambdaTranslation &translation) {
  std::ostringstream oss;

  // Declare closure struct
  oss << "struct " << translation.closureStructName << " __lambda_closure;\n";

  // Initialize captured variables
  for (const auto &entry : translation.captures) {
    const CaptureInfo &info = entry.second;

    if (info.mode == CaptureMode::BY_VALUE ||
        info.mode == CaptureMode::IMPLICIT_VALUE) {
      // Value capture: copy value
      oss << "__lambda_closure." << info.varName << " = " << info.varName
          << ";\n";
    } else if (info.mode == CaptureMode::BY_REFERENCE ||
               info.mode == CaptureMode::IMPLICIT_REFERENCE) {
      // Reference capture: store address
      oss << "__lambda_closure." << info.varName << " = &" << info.varName
          << ";\n";
    } else if (info.mode == CaptureMode::THIS_POINTER) {
      // This pointer capture
      oss << "__lambda_closure." << info.varName << " = this;\n";
    } else if (info.mode == CaptureMode::THIS_COPY) {
      // This copy capture
      oss << "__lambda_closure." << info.varName << " = *this;\n";
    }
  }

  return oss.str();
}

std::string
LambdaTranslator::generateLambdaCall(const LambdaTranslation &translation,
                                      const std::vector<std::string> &args) {
  std::ostringstream oss;

  // Function call: funcName(&closure, args...)
  oss << translation.funcName << "(&__lambda_closure";

  for (const auto &arg : args) {
    oss << ", " << arg;
  }

  oss << ")";

  return oss.str();
}

const LambdaTranslation *
LambdaTranslator::getTranslation(const LambdaExpr *E) const {
  auto it = translations.find(E);
  if (it != translations.end()) {
    return &it->second;
  }
  return nullptr;
}

bool LambdaTranslator::isGenericLambda(LambdaExpr *E) const {
  const CXXMethodDecl *callOp = E->getCallOperator();
  if (!callOp) {
    return false;
  }

  // Check if any parameter has auto type
  for (const auto *param : callOp->parameters()) {
    if (param->getType()->getContainedAutoType()) {
      return true;
    }
  }

  return false;
}

std::string LambdaTranslator::generateGenericInstantiation(
    const LambdaTranslation &translation,
    const std::string &instantiationType) {

  // For now, return empty string - generic lambdas require template
  // instantiation This is a complex feature that may be implemented in a future
  // phase
  return "/* Generic lambda instantiation not yet implemented */\n";
}

std::string LambdaTranslator::generateLambdaId() {
  std::ostringstream oss;
  oss << "lambda_" << lambdaCounter++;
  return oss.str();
}

// Helper visitor to translate lambda body
class LambdaBodyTranslator : public RecursiveASTVisitor<LambdaBodyTranslator> {
public:
  std::ostringstream &output;
  const std::map<std::string, CaptureInfo> &captures;
  const std::string &closureName;
  ASTContext &Context;
  unsigned int indentLevel;

  LambdaBodyTranslator(std::ostringstream &output,
                        const std::map<std::string, CaptureInfo> &captures,
                        const std::string &closureName, ASTContext &Context)
      : output(output), captures(captures), closureName(closureName),
        Context(Context), indentLevel(1) {}

  std::string getIndent() const { return std::string(indentLevel * 4, ' '); }

  bool TraverseCompoundStmt(CompoundStmt *S) {
    // Don't add extra braces - they're already in the function definition
    for (auto *child : S->body()) {
      TraverseStmt(child);
    }
    return true;
  }

  bool TraverseDeclStmt(DeclStmt *S) {
    output << getIndent();
    for (auto *decl : S->decls()) {
      if (VarDecl *VD = dyn_cast<VarDecl>(decl)) {
        output << VD->getType().getAsString() << " " << VD->getNameAsString();
        if (VD->hasInit()) {
          output << " = ";
          TraverseStmt(VD->getInit());
        }
        output << ";\n";
      }
    }
    return true;
  }

  bool TraverseReturnStmt(ReturnStmt *S) {
    output << getIndent() << "return ";
    if (S->getRetValue()) {
      TraverseStmt(S->getRetValue());
    }
    output << ";\n";
    return true;
  }

  bool TraverseBinaryOperator(BinaryOperator *E) {
    TraverseStmt(E->getLHS());
    output << " " << E->getOpcodeStr().str() << " ";
    TraverseStmt(E->getRHS());
    return true;
  }

  bool TraverseDeclRefExpr(DeclRefExpr *E) {
    std::string varName = E->getDecl()->getNameAsString();

    // Check if this variable is captured
    auto it = captures.find(varName);
    if (it != captures.end()) {
      const CaptureInfo &info = it->second;

      // Rewrite to use closure
      if (info.mode == CaptureMode::BY_VALUE ||
          info.mode == CaptureMode::IMPLICIT_VALUE) {
        output << closureName << "->" << varName;
      } else if (info.mode == CaptureMode::BY_REFERENCE ||
                 info.mode == CaptureMode::IMPLICIT_REFERENCE) {
        output << "(*" << closureName << "->" << varName << ")";
      } else if (info.mode == CaptureMode::THIS_POINTER) {
        output << closureName << "->this";
      }
    } else {
      // Not captured - just output variable name
      output << varName;
    }

    return true;
  }

  bool TraverseIntegerLiteral(IntegerLiteral *E) {
    output << E->getValue().toString(10, true);
    return true;
  }

  bool TraverseCallExpr(CallExpr *E) {
    TraverseStmt(E->getCallee());
    output << "(";
    for (unsigned i = 0; i < E->getNumArgs(); ++i) {
      if (i > 0)
        output << ", ";
      TraverseStmt(E->getArg(i));
    }
    output << ")";
    return true;
  }

  bool TraverseExprWithCleanups(ExprWithCleanups *E) {
    TraverseStmt(E->getSubExpr());
    return true;
  }

  bool TraverseCXXConstructExpr(CXXConstructExpr *E) {
    // For now, just output the arguments
    output << "{";
    for (unsigned i = 0; i < E->getNumArgs(); ++i) {
      if (i > 0)
        output << ", ";
      TraverseStmt(E->getArg(i));
    }
    output << "}";
    return true;
  }
};

std::string LambdaTranslator::translateLambdaBody(
    const Stmt *body, const std::map<std::string, CaptureInfo> &captures,
    const std::string &closureName) {

  std::ostringstream oss;
  LambdaBodyTranslator translator(oss, captures, closureName, Context);
  translator.TraverseStmt(const_cast<Stmt *>(body));
  return oss.str();
}

std::string
LambdaTranslator::getFunctionSignature(LambdaExpr *E,
                                        const std::string &closureName) {
  std::ostringstream oss;

  // Return type
  std::string returnType = getReturnType(E);

  // Function pointer type
  oss << returnType << " (*)(";

  // Closure pointer parameter
  oss << "struct " << closureName << "*";

  // Lambda parameters
  const CXXMethodDecl *callOp = E->getCallOperator();
  if (callOp) {
    for (const auto *param : callOp->parameters()) {
      oss << ", " << param->getType().getAsString();
    }
  }

  oss << ")";

  return oss.str();
}

std::string LambdaTranslator::getParameterList(LambdaExpr *E) {
  std::ostringstream oss;

  const CXXMethodDecl *callOp = E->getCallOperator();
  if (!callOp) {
    return "";
  }

  bool first = true;
  for (const auto *param : callOp->parameters()) {
    if (!first) {
      oss << ", ";
    }
    first = false;

    oss << param->getType().getAsString() << " " << param->getNameAsString();
  }

  return oss.str();
}

std::string LambdaTranslator::getReturnType(LambdaExpr *E) {
  const CXXMethodDecl *callOp = E->getCallOperator();
  if (!callOp) {
    return "void";
  }

  QualType returnType = callOp->getReturnType();
  return returnType.getAsString();
}

std::string LambdaTranslator::rewriteVariableReference(
    const std::string &varName,
    const std::map<std::string, CaptureInfo> &captures,
    const std::string &closureName) {

  auto it = captures.find(varName);
  if (it == captures.end()) {
    // Not captured - return as-is
    return varName;
  }

  const CaptureInfo &info = it->second;

  // Rewrite based on capture mode
  if (info.mode == CaptureMode::BY_VALUE ||
      info.mode == CaptureMode::IMPLICIT_VALUE) {
    return closureName + "->" + varName;
  } else if (info.mode == CaptureMode::BY_REFERENCE ||
             info.mode == CaptureMode::IMPLICIT_REFERENCE) {
    return "(*" + closureName + "->" + varName + ")";
  } else if (info.mode == CaptureMode::THIS_POINTER) {
    return closureName + "->this";
  }

  return varName;
}

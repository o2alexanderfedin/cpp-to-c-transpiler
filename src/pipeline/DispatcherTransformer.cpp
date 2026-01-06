#include "pipeline/DispatcherTransformer.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"

// Include all handlers
#include "dispatch/TypeHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/RecoveryExprHandler.h"
#include "dispatch/UnresolvedLookupExprHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/MemberExprHandler.h"
#include "dispatch/ArraySubscriptExprHandler.h"
#include "dispatch/ParenExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/BinaryOperatorHandler.h"
#include "dispatch/CallExprHandler.h"
#include "dispatch/CXXOperatorCallExprHandler.h"
#include "dispatch/CXXMemberCallExprHandler.h"
#include "dispatch/CXXTypeidExprHandler.h"
#include "dispatch/CXXDynamicCastExprHandler.h"
#include "dispatch/CXXStaticCastExprHandler.h"
#include "dispatch/CXXFunctionalCastExprHandler.h"
#include "dispatch/CStyleCastExprHandler.h"
#include "dispatch/CompoundAssignOperatorHandler.h"
#include "dispatch/CXXDependentScopeMemberExprHandler.h"
#include "dispatch/CommaOperatorHandler.h"
#include "dispatch/ConditionalOperatorHandler.h"
#include "dispatch/CXXConstructExprHandler.h"
#include "dispatch/CXXTemporaryObjectExprHandler.h"
#include "dispatch/CXXNullPtrLiteralExprHandler.h"
#include "dispatch/CXXDefaultArgExprHandler.h"
#include "dispatch/CXXNewExprHandler.h"
#include "dispatch/CXXDeleteExprHandler.h"
#include "dispatch/CXXThisExprHandler.h"
#include "dispatch/CompoundLiteralExprHandler.h"
#include "dispatch/ExprWithCleanupsHandler.h"
#include "dispatch/MaterializeTemporaryExprHandler.h"
#include "dispatch/InitListExprHandler.h"
#include "dispatch/CompoundStmtHandler.h"
#include "dispatch/ReturnStmtHandler.h"
#include "dispatch/IfStmtHandler.h"
#include "dispatch/SwitchStmtHandler.h"
#include "dispatch/ForStmtHandler.h"
#include "dispatch/WhileStmtHandler.h"
#include "dispatch/DeclStmtHandler.h"
#include "dispatch/TryStmtHandler.h"
#include "dispatch/ThrowExprHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/RecordHandler.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/InstanceMethodHandler.h"
#include "dispatch/StaticMethodHandler.h"
#include "dispatch/VirtualMethodHandler.h"
#include "dispatch/NamespaceHandler.h"
#include "dispatch/TranslationUnitHandler.h"

namespace cpptoc {
namespace pipeline {

DispatcherTransformer::DispatcherTransformer(const PipelineConfig& config)
  : config_(config) {}

void DispatcherTransformer::transform(
    clang::ASTContext& cppASTContext,
    clang::TranslationUnitDecl* cppTU,
    const std::string& sourceFilePath) {

  // Get singletons
  TargetContext& targetCtx = TargetContext::getInstance();
  clang::ASTContext& cCtx = targetCtx.getContext();

  // Create PathMapper
  PathMapper pathMapper(
    config_.sourceDir,
    config_.outputDir
  );

  // Map source file to target path
  std::string targetPath = pathMapper.mapSourceToTarget(sourceFilePath);

  // Create mappers
  DeclLocationMapper locMapper(pathMapper);
  DeclMapper declMapper;
  TypeMapper typeMapper;
  ExprMapper exprMapper;
  StmtMapper stmtMapper;

  // Create dispatcher
  CppToCVisitorDispatcher dispatcher(
    pathMapper,
    locMapper,
    declMapper,
    typeMapper,
    exprMapper,
    stmtMapper
  );

  // Register all handlers in dependency order (matches CppToCFrontendAction.cpp)
  TypeHandler::registerWith(dispatcher);
  ParameterHandler::registerWith(dispatcher);
  LiteralHandler::registerWith(dispatcher);
  RecoveryExprHandler::registerWith(dispatcher);
  UnresolvedLookupExprHandler::registerWith(dispatcher);
  DeclRefExprHandler::registerWith(dispatcher);
  MemberExprHandler::registerWith(dispatcher);
  ArraySubscriptExprHandler::registerWith(dispatcher);
  ParenExprHandler::registerWith(dispatcher);
  ImplicitCastExprHandler::registerWith(dispatcher);
  UnaryOperatorHandler::registerWith(dispatcher);
  BinaryOperatorHandler::registerWith(dispatcher);
  CompoundAssignOperatorHandler::registerWith(dispatcher);
  CallExprHandler::registerWith(dispatcher);
  CXXOperatorCallExprHandler::registerWith(dispatcher);
  CXXMemberCallExprHandler::registerWith(dispatcher);
  CXXTypeidExprHandler::registerWith(dispatcher);
  CXXDynamicCastExprHandler::registerWith(dispatcher);
  CXXStaticCastExprHandler::registerWith(dispatcher);
  CXXFunctionalCastExprHandler::registerWith(dispatcher);
  CStyleCastExprHandler::registerWith(dispatcher);
  CXXDependentScopeMemberExprHandler::registerWith(dispatcher);
  CommaOperatorHandler::registerWith(dispatcher);
  ConditionalOperatorHandler::registerWith(dispatcher);
  InitListExprHandler::registerWith(dispatcher);
  CXXConstructExprHandler::registerWith(dispatcher);
  CXXTemporaryObjectExprHandler::registerWith(dispatcher);
  CXXNullPtrLiteralExprHandler::registerWith(dispatcher);
  CXXDefaultArgExprHandler::registerWith(dispatcher);
  CXXNewExprHandler::registerWith(dispatcher);
  CXXDeleteExprHandler::registerWith(dispatcher);
  CXXThisExprHandler::registerWith(dispatcher);
  CompoundLiteralExprHandler::registerWith(dispatcher);
  ExprWithCleanupsHandler::registerWith(dispatcher);
  MaterializeTemporaryExprHandler::registerWith(dispatcher);
  ThrowExprHandler::registerWith(dispatcher);
  IfStmtHandler::registerWith(dispatcher);
  SwitchStmtHandler::registerWith(dispatcher);
  ForStmtHandler::registerWith(dispatcher);
  WhileStmtHandler::registerWith(dispatcher);
  DeclStmtHandler::registerWith(dispatcher);
  TryStmtHandler::registerWith(dispatcher);
  CompoundStmtHandler::registerWith(dispatcher);
  ReturnStmtHandler::registerWith(dispatcher);
  VariableHandler::registerWith(dispatcher);
  RecordHandler::registerWith(dispatcher);
  FunctionHandler::registerWith(dispatcher);
  InstanceMethodHandler::registerWith(dispatcher);
  StaticMethodHandler::registerWith(dispatcher);
  VirtualMethodHandler::registerWith(dispatcher);
  NamespaceHandler::registerWith(dispatcher);
  TranslationUnitHandler::registerWith(dispatcher);

  // Dispatch on Translation Unit
  dispatcher.dispatch(cppASTContext, cCtx, cppTU);
}

TargetContext& DispatcherTransformer::getTargetContext() {
  return TargetContext::getInstance();
}

}} // namespace cpptoc::pipeline

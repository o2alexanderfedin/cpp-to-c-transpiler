#include "CppToCFrontendAction.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "dispatch/TranslationUnitHandler.h"
#include "dispatch/NamespaceHandler.h"
#include "dispatch/RecordHandler.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/InstanceMethodHandler.h"
#include "dispatch/StaticMethodHandler.h"
#include "dispatch/VirtualMethodHandler.h"
#include "dispatch/TypeHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/CompoundStmtHandler.h"
#include "dispatch/ReturnStmtHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/MemberExprHandler.h"
#include "dispatch/ArraySubscriptExprHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/RecoveryExprHandler.h"
#include "dispatch/UnresolvedLookupExprHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/BinaryOperatorHandler.h"
#include "dispatch/ParenExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
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
#include "dispatch/IfStmtHandler.h"
#include "dispatch/SwitchStmtHandler.h"
#include "dispatch/ForStmtHandler.h"
#include "dispatch/WhileStmtHandler.h"
#include "dispatch/DeclStmtHandler.h"
#include "dispatch/VariableHandler.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "CodeGenerator.h"
#include "FileOutputManager.h"
#include "TargetContext.h"
#include "clang/AST/ASTConsumer.h"
#include "llvm/Support/raw_ostream.h"
#include <atomic>

// External accessors (defined in main.cpp)
extern std::string getSourceDir();
extern std::string getOutputDir();
extern std::atomic<int> g_filesGeneratedCount;

namespace {

// Custom ASTConsumer that uses dispatcher architecture
class DispatcherConsumer : public clang::ASTConsumer {
  std::string InputFilename;
  std::string SourceDir;

public:
  DispatcherConsumer(const std::string& filename, const std::string& sourceDir)
    : InputFilename(filename), SourceDir(sourceDir) {}

  void HandleTranslationUnit(clang::ASTContext& Context) override {
    // RAII: Create TargetContext instance for this transpilation session
    // Must be created BEFORE mappers since they may depend on it
    TargetContext targetCtx;
    clang::ASTContext& cCtx = targetCtx.getContext();

    // PathMapper Integration: Get output directory configuration
    std::string outputDir = getOutputDir();
    if (outputDir.empty()) {
      outputDir = ".";
    }

    // Create PathMapper instance with dependency injection
    cpptoc::PathMapper pathMapper(targetCtx, SourceDir, outputDir);

    // Map source file to target path and get/create C_TU
    std::string targetPath = pathMapper.mapSourceToTarget(InputFilename);
    clang::TranslationUnitDecl* C_TU = pathMapper.getOrCreateTU(targetPath);
    llvm::outs() << "[PathMapper] Mapped " << InputFilename << " -> " << targetPath << "\n";

    // Create mapping utilities
    cpptoc::DeclLocationMapper locMapper(pathMapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    // Create dispatcher with all mappers
    CppToCVisitorDispatcher dispatcher(pathMapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

    // Set the current target path so all declarations go to the correct C_TU
    dispatcher.setCurrentTargetPath(targetPath);

    // Register all handlers in dependency order
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::RecoveryExprHandler::registerWith(dispatcher);
    cpptoc::UnresolvedLookupExprHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::CompoundAssignOperatorHandler::registerWith(dispatcher);
    cpptoc::CallExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);
    cpptoc::CXXMemberCallExprHandler::registerWith(dispatcher);
    cpptoc::CXXTypeidExprHandler::registerWith(dispatcher);
    cpptoc::CXXDynamicCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXStaticCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXFunctionalCastExprHandler::registerWith(dispatcher);
    cpptoc::CStyleCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXDependentScopeMemberExprHandler::registerWith(dispatcher);
    cpptoc::CommaOperatorHandler::registerWith(dispatcher);
    cpptoc::ConditionalOperatorHandler::registerWith(dispatcher);
    cpptoc::InitListExprHandler::registerWith(dispatcher);
    cpptoc::CXXConstructExprHandler::registerWith(dispatcher);
    cpptoc::CXXTemporaryObjectExprHandler::registerWith(dispatcher);
    cpptoc::CXXNullPtrLiteralExprHandler::registerWith(dispatcher);
    cpptoc::CXXDefaultArgExprHandler::registerWith(dispatcher);
    cpptoc::CXXNewExprHandler::registerWith(dispatcher);
    cpptoc::CXXDeleteExprHandler::registerWith(dispatcher);
    cpptoc::CXXThisExprHandler::registerWith(dispatcher);
    cpptoc::CompoundLiteralExprHandler::registerWith(dispatcher);
    cpptoc::ExprWithCleanupsHandler::registerWith(dispatcher);
    cpptoc::MaterializeTemporaryExprHandler::registerWith(dispatcher);
    cpptoc::IfStmtHandler::registerWith(dispatcher);
    cpptoc::SwitchStmtHandler::registerWith(dispatcher);
    cpptoc::ForStmtHandler::registerWith(dispatcher);
    cpptoc::WhileStmtHandler::registerWith(dispatcher);
    cpptoc::DeclStmtHandler::registerWith(dispatcher);
    cpptoc::CompoundStmtHandler::registerWith(dispatcher);
    cpptoc::ReturnStmtHandler::registerWith(dispatcher);
    cpptoc::VariableHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);
    cpptoc::FunctionHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);
    cpptoc::VirtualMethodHandler::registerWith(dispatcher);
    cpptoc::NamespaceHandler::registerWith(dispatcher);
    cpptoc::TranslationUnitHandler::registerWith(dispatcher);

    // Traverse and dispatch AST nodes
    auto* TU = Context.getTranslationUnitDecl();
    dispatcher.dispatch(Context, cCtx, TU);

    // Generate C code using CodeGenerator
    // TODO: This should use C ASTContext (cCtx), but currently uses C++ Context
    // because CodeGenerator's type checking doesn't work correctly with separate contexts
    std::string headerContent;
    std::string implContent;
    llvm::raw_string_ostream headerOS(headerContent);
    llvm::raw_string_ostream implOS(implContent);

    CodeGenerator headerGen(headerOS, Context, InputFilename);
    CodeGenerator implGen(implOS, Context, InputFilename);

    // Generate header file (.h)
    headerOS << "#pragma once\n\n";
    for (auto* D : C_TU->decls()) {
      if (!D->isImplicit()) {
        headerGen.printDecl(D, true);
      }
    }

    // Generate implementation file (.c)
    // Extract base name for #include
    size_t lastSlash = InputFilename.find_last_of("/\\");
    std::string baseName = (lastSlash != std::string::npos) ? InputFilename.substr(lastSlash + 1) : InputFilename;
    size_t dotPos = baseName.find_last_of('.');
    if (dotPos != std::string::npos) {
      baseName = baseName.substr(0, dotPos);
    }
    implOS << "#include \"" << baseName << ".h\"\n\n";

    for (auto* D : C_TU->decls()) {
      if (!D->isImplicit()) {
        implGen.printDecl(D, false);
      }
    }

    headerOS.flush();
    implOS.flush();

    // Use FileOutputManager to write files
    FileOutputManager outputMgr;
    outputMgr.setInputFilename(InputFilename);
    if (!outputDir.empty()) {
      outputMgr.setOutputDir(outputDir);
    }
    if (!SourceDir.empty()) {
      outputMgr.setSourceDir(SourceDir);
    }

    // Write the files
    if (outputMgr.writeFiles(headerContent, implContent)) {
      llvm::outs() << "Generated files:\n";
      llvm::outs() << "  " << outputMgr.getHeaderFilename() << "\n";
      llvm::outs() << "  " << outputMgr.getImplFilename() << "\n";
      g_filesGeneratedCount++;
    } else {
      llvm::errs() << "Error: Failed to write output files\n";
    }
  }
};

} // anonymous namespace

std::unique_ptr<clang::ASTConsumer>
CppToCFrontendAction::CreateASTConsumer(clang::CompilerInstance &CI,
                                        llvm::StringRef file) {
  std::string sourceDir = getSourceDir();
  return std::make_unique<DispatcherConsumer>(file.str(), sourceDir);
}

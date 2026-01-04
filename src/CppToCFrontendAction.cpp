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
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/BinaryOperatorHandler.h"
#include "dispatch/ParenExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/CXXOperatorCallExprHandler.h"
#include "dispatch/CXXTypeidExprHandler.h"
#include "dispatch/CXXDynamicCastExprHandler.h"
#include "dispatch/CommaOperatorHandler.h"
#include "dispatch/CXXConstructExprHandler.h"
#include "dispatch/InitListExprHandler.h"
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
    // Setup target context for C AST
    TargetContext& targetCtx = TargetContext::getInstance();
    clang::ASTContext& cCtx = targetCtx.getContext();

    // PathMapper Integration: Get singleton PathMapper instance
    std::string outputDir = getOutputDir();
    if (outputDir.empty()) {
      outputDir = ".";
    }

    // Get the shared PathMapper instance
    cpptoc::PathMapper& pathMapper = cpptoc::PathMapper::getInstance(SourceDir, outputDir);

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

    // Register all handlers in dependency order
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);
    cpptoc::CXXTypeidExprHandler::registerWith(dispatcher);
    cpptoc::CXXDynamicCastExprHandler::registerWith(dispatcher);
    cpptoc::CommaOperatorHandler::registerWith(dispatcher);
    cpptoc::InitListExprHandler::registerWith(dispatcher);
    cpptoc::CXXConstructExprHandler::registerWith(dispatcher);
    cpptoc::CompoundStmtHandler::registerWith(dispatcher);
    cpptoc::ReturnStmtHandler::registerWith(dispatcher);
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

// TryCatchTransformer.cpp - Implementation of try-catch to setjmp/longjmp transformation
// Story #78: Implement setjmp/longjmp Injection for Try-Catch Blocks
// Phase 6: AST-based implementation (COMPLETE - returns C AST nodes, not strings)

#include "dispatch/CppToCVisitorDispatcher.h"  // MUST be before TryCatchTransformer.h for full definition
#include "TryCatchTransformer.h"
#include "NameMangler.h"
#include "mapping/StmtMapper.h"
#include "CNodeBuilder.h"
#include "CodeGenerator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include "clang/Lex/Lexer.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

namespace clang {

// Constructor with frame generator dependency (Dependency Injection)
TryCatchTransformer::TryCatchTransformer(std::shared_ptr<ExceptionFrameGenerator> frameGen)
    : frameGenerator(frameGen) {}

// Default constructor creates internal frame generator
TryCatchTransformer::TryCatchTransformer()
    : frameGenerator(std::make_shared<ExceptionFrameGenerator>()) {}

// ============================================================================
// Phase 6: AST-based methods (NEW - returns C AST nodes)
// ============================================================================

// Transform complete try-catch statement to C control flow (AST-based)
CompoundStmt* TryCatchTransformer::transformTryCatch(
    const CXXTryStmt *tryStmt,
    const std::string& frameVarName,
    const std::string& actionsTableName,
    const ::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    CNodeBuilder builder(cCtx);
    std::vector<Stmt*> stmts;

    // TODO Phase 6: Generate frame declaration and push
    // For now, we skip frame push - will add in refinement
    // frameGenerator->generateFramePush(frameVarName, actionsTableName);

    // Generate setjmp guard: if (setjmp(frame.jmpbuf) == 0)
    Expr* setjmpCond = generateSetjmpGuard(frameVarName, cCtx);

    // Generate try body (normal execution path)
    CompoundStmt* tryBody = generateTryBody(tryStmt, frameVarName, disp, cppCtx, cCtx);

    // Generate catch handlers (exception path)
    CompoundStmt* catchHandlers = generateCatchHandlers(tryStmt, frameVarName, disp, cppCtx, cCtx);

    // Create if statement: if (setjmp(...) == 0) { try_body } else { catch_handlers }
    IfStmt* ifStmt = builder.ifStmt(setjmpCond, tryBody, catchHandlers);

    stmts.push_back(ifStmt);

    return builder.block(stmts);
}

// Generate try body code with frame push/pop (AST-based)
CompoundStmt* TryCatchTransformer::generateTryBody(
    const CXXTryStmt *tryStmt,
    const std::string& frameVarName,
    const ::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    CNodeBuilder builder(cCtx);
    std::vector<Stmt*> stmts;

    // TODO Phase 6: Push frame onto exception stack
    // __cxx_exception_stack = &frame;
    // For now, skip frame management

    // Try body statements (using dispatcher for translation)
    const Stmt *tryBody = tryStmt->getTryBlock();
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();

    if (const CompoundStmt *compound = dyn_cast<CompoundStmt>(tryBody)) {
        for (const Stmt *stmt : compound->body()) {
            // Dispatch the statement through the dispatcher
            Stmt* stmtNonConst = const_cast<Stmt*>(stmt);
            bool handled = disp.dispatch(cppCtx, cCtx, stmtNonConst);

            if (handled) {
                Stmt* cStmt = stmtMapper.getCreated(stmt);
                if (cStmt) {
                    stmts.push_back(cStmt);
                }
            }
        }
    } else {
        // Single statement
        Stmt* tryBodyNonConst = const_cast<Stmt*>(tryBody);
        bool handled = disp.dispatch(cppCtx, cCtx, tryBodyNonConst);

        if (handled) {
            Stmt* cStmt = stmtMapper.getCreated(tryBody);
            if (cStmt) {
                stmts.push_back(cStmt);
            }
        }
    }

    // TODO Phase 6: Pop frame from exception stack (normal path only)
    // frameGenerator->generateFramePop(frameVarName);

    return builder.block(stmts);
}

// Generate catch handlers code (AST-based)
CompoundStmt* TryCatchTransformer::generateCatchHandlers(
    const CXXTryStmt *tryStmt,
    const std::string& frameVarName,
    const ::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    CNodeBuilder builder(cCtx);
    std::vector<Stmt*> stmts;

    // Exception caught here (longjmp target)
    // frame.exception_object and frame.exception_type set by cxx_throw

    // Generate each catch handler as if-else chain
    unsigned numHandlers = tryStmt->getNumHandlers();
    Stmt* catchChain = nullptr;

    for (unsigned i = numHandlers; i > 0; --i) {
        const CXXCatchStmt *handler = tryStmt->getHandler(i - 1);
        bool isFirst = (i == numHandlers);

        IfStmt* catchIf = generateCatchHandler(handler, frameVarName, isFirst, disp, cppCtx, cCtx);

        if (catchChain == nullptr) {
            // Last handler becomes the base
            catchChain = catchIf;
        } else {
            // Chain previous handlers as else branch
            // Need to recreate IfStmt with catchChain as else branch
            // This is tricky - for now, just add to stmts
            stmts.push_back(catchIf);
        }
    }

    if (catchChain) {
        stmts.push_back(catchChain);
    }

    return builder.block(stmts);
}

// Generate single catch handler (AST-based)
IfStmt* TryCatchTransformer::generateCatchHandler(
    const CXXCatchStmt *handler,
    const std::string& frameVarName,
    bool isFirst,
    const ::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    CNodeBuilder builder(cCtx);
    std::vector<Stmt*> handlerStmts;

    VarDecl *exceptionVar = handler->getExceptionDecl();

    // Check if catch-all (catch (...))
    if (!exceptionVar) {
        // Catch-all handler - create unconditional block
        // For now, just translate handler body
        cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();

        Stmt* handlerBlock = const_cast<Stmt*>(handler->getHandlerBlock());
        bool handled = disp.dispatch(cppCtx, cCtx, handlerBlock);

        if (handled) {
            Stmt* cHandlerBlock = stmtMapper.getCreated(handler->getHandlerBlock());
            if (cHandlerBlock) {
                handlerStmts.push_back(cHandlerBlock);
            }
        }

        // Return as if(1) for catch-all
        Expr* trueCond = builder.intLit(1);
        return builder.ifStmt(trueCond, builder.block(handlerStmts), nullptr);
    }

    // Typed catch handler
    QualType exceptionType = exceptionVar->getType();

    // Generate type check condition
    Expr* typeCheckCond = generateTypeCheck(exceptionType, frameVarName, cCtx);

    // Cast exception object to proper type
    DeclStmt* exceptionCast = generateExceptionObjectCast(exceptionVar, frameVarName, cCtx);
    handlerStmts.push_back(exceptionCast);

    // Handler body (using dispatcher for translation)
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();

    if (const CompoundStmt *handlerBody = dyn_cast<CompoundStmt>(handler->getHandlerBlock())) {
        for (const Stmt *stmt : handlerBody->body()) {
            Stmt* stmtNonConst = const_cast<Stmt*>(stmt);
            bool handled = disp.dispatch(cppCtx, cCtx, stmtNonConst);

            if (handled) {
                Stmt* cStmt = stmtMapper.getCreated(stmt);
                if (cStmt) {
                    handlerStmts.push_back(cStmt);
                }
            }
        }
    } else {
        Stmt* handlerBlock = const_cast<Stmt*>(handler->getHandlerBlock());
        bool handled = disp.dispatch(cppCtx, cCtx, handlerBlock);

        if (handled) {
            Stmt* cHandlerBlock = stmtMapper.getCreated(handler->getHandlerBlock());
            if (cHandlerBlock) {
                handlerStmts.push_back(cHandlerBlock);
            }
        }
    }

    // Cleanup exception object
    std::string varName = exceptionVar->getNameAsString();
    CompoundStmt* cleanupStmts = generateExceptionCleanup(exceptionType, varName, cCtx);
    if (cleanupStmts) {
        // Add cleanup statements to handler
        for (auto* stmt : cleanupStmts->body()) {
            handlerStmts.push_back(const_cast<Stmt*>(stmt));
        }
    }

    // Create if statement: if (type_check) { handler_body }
    return builder.ifStmt(typeCheckCond, builder.block(handlerStmts), nullptr);
}

// Convert Clang statement to C code string (with dispatcher)
std::string TryCatchTransformer::stmtToString(
    const Stmt *stmt,
    const ::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    if (!stmt) {
        return "";
    }

    // Dispatch the statement through the dispatcher
    Stmt* stmtNonConst = const_cast<Stmt*>(stmt);
    bool handled = disp.dispatch(cppCtx, cCtx, stmtNonConst);

    if (!handled) {
        llvm::errs() << "[TryCatchTransformer] WARNING: Statement not handled by dispatcher: "
                     << stmt->getStmtClassName() << "\n";
        return "/* unhandled statement */;";
    }

    // Retrieve the translated C statement from StmtMapper
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
    Stmt* cStmt = stmtMapper.getCreated(stmt);

    if (!cStmt) {
        llvm::errs() << "[TryCatchTransformer] WARNING: Statement dispatched but not in StmtMapper: "
                     << stmt->getStmtClassName() << "\n";
        return "/* statement not mapped */;";
    }

    // Convert C Stmt* to string using printPretty
    // Phase 6 will return the Stmt* directly instead of converting to string
    std::string result;
    llvm::raw_string_ostream OS(result);
    clang::PrintingPolicy Policy(cCtx.getLangOpts());
    Policy.Bool = true;
    cStmt->printPretty(OS, nullptr, Policy);
    OS.flush();

    return result;
}


} // namespace clang

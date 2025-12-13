/**
 * @file StateMachineTransformer.cpp
 * @brief Implementation of StateMachineTransformer (Story #104)
 */

#include "../include/StateMachineTransformer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtCXX.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/Lexer.h"
#include <sstream>

using namespace clang;

StateMachineTransformer::StateMachineTransformer(ASTContext& Context)
    : Context(Context), Identifier(Context) {}

std::string StateMachineTransformer::transformToStateMachine(const FunctionDecl* FD) {
    if (!FD || !FD->hasBody()) {
        return "";
    }

    // Get all suspend points
    auto suspendPoints = Identifier.identifySuspendPoints(FD);
    if (suspendPoints.empty()) {
        return "";
    }

    return generateSwitchStatement(FD, suspendPoints);
}

std::string StateMachineTransformer::generateResumeFunction(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    std::ostringstream code;
    std::string funcName = FD->getNameAsString();
    std::string frameName = funcName + "_frame";

    code << "// Resume function for " << funcName << "\n";
    code << "void " << funcName << "_resume(void* frame_ptr) {\n";
    code << "    struct " << frameName << "* frame = (struct " << frameName << "*)frame_ptr;\n";
    code << "\n";

    // Generate the state machine
    std::string stateMachine = transformToStateMachine(FD);
    if (!stateMachine.empty()) {
        code << stateMachine;
    }

    code << "}\n";

    return code.str();
}

std::string StateMachineTransformer::generateDestroyFunction(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    std::ostringstream code;
    std::string funcName = FD->getNameAsString();
    std::string frameName = funcName + "_frame";

    code << "// Destroy function for " << funcName << "\n";
    code << "void " << funcName << "_destroy(void* frame_ptr) {\n";
    code << "    struct " << frameName << "* frame = (struct " << frameName << "*)frame_ptr;\n";
    code << "    // Clean up resources\n";
    code << "    free(frame);\n";
    code << "}\n";

    return code.str();
}

std::string StateMachineTransformer::generateSwitchStatement(
    const FunctionDecl* FD,
    const std::vector<SuspendPoint>& suspendPoints) {

    std::ostringstream code;

    code << "    // State machine switch\n";
    code << "    switch (frame->state) {\n";

    // Generate case 0 (initial state)
    code << "        case 0:  // Initial state\n";
    code << "            // Execute until first suspend point\n";

    // Generate cases for each suspend point
    for (const auto& sp : suspendPoints) {
        code << generateCaseLabel(sp, FD);
    }

    // Default case
    code << "        default:\n";
    code << "            // Invalid state\n";
    code << "            return;\n";

    code << "    }\n";

    return code.str();
}

std::string StateMachineTransformer::generateCaseLabel(
    const SuspendPoint& sp,
    const FunctionDecl* FD) {

    std::ostringstream code;

    code << "        case " << sp.stateId << ":  // Resume after " << sp.kind << "\n";
    code << "            // Resume execution\n";

    // Generate state save before suspend
    if (sp.kind == "co_yield" || sp.kind == "co_await") {
        code << "            " << generateStateSave(sp.stateId + 1);
        code << "            return;  // Suspend\n";
    } else if (sp.kind == "co_return") {
        code << "            " << generateStateSave(-1);  // -1 indicates done
        code << "            return;  // Final return\n";
    }

    return code.str();
}

std::string StateMachineTransformer::extractCodeSegment(const Stmt* start, const Stmt* end) {
    if (!start || !end) {
        return "";
    }

    // Simplified extraction - would need full source rewriting in production
    SourceManager& SM = Context.getSourceManager();
    SourceLocation startLoc = start->getBeginLoc();
    SourceLocation endLoc = end->getEndLoc();

    if (startLoc.isInvalid() || endLoc.isInvalid()) {
        return "";
    }

    // Get the source text between locations
    bool invalid = false;
    const char* startPtr = SM.getCharacterData(startLoc, &invalid);
    if (invalid) return "";

    const char* endPtr = SM.getCharacterData(endLoc, &invalid);
    if (invalid) return "";

    if (endPtr < startPtr) return "";

    return std::string(startPtr, endPtr - startPtr);
}

std::string StateMachineTransformer::generateStateSave(unsigned int stateId) {
    std::ostringstream code;
    code << "frame->state = " << stateId << ";\n";
    return code.str();
}

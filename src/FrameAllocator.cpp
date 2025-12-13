/**
 * @file FrameAllocator.cpp
 * @brief Implementation of FrameAllocator (Story #107)
 */

#include "../include/FrameAllocator.h"
#include "clang/AST/Type.h"
#include <sstream>

using namespace clang;

FrameAllocator::FrameAllocator(ASTContext& Context)
    : Context(Context) {}

std::string FrameAllocator::generateFrameAllocation(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    std::ostringstream code;
    std::string frameName = getFrameTypeName(FD);

    code << "    // Allocate coroutine frame on heap\n";
    code << "    struct " << frameName << "* frame = (struct " << frameName << "*)\n";
    code << "        malloc(sizeof(struct " << frameName << "));\n";

    return code.str();
}

std::string FrameAllocator::generateCoroutineHandle(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    std::ostringstream code;
    std::string handleName = getHandleTypeName(FD);
    std::string frameName = getFrameTypeName(FD);

    code << "// Coroutine handle for " << FD->getNameAsString() << "\n";
    code << "struct " << handleName << " {\n";
    code << "    struct " << frameName << "* frame;\n";
    code << "};\n";

    return code.str();
}

std::string FrameAllocator::generateResumeOperation(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    std::ostringstream code;
    std::string handleName = getHandleTypeName(FD);
    std::string funcName = FD->getNameAsString();

    code << "// Resume operation for " << funcName << "\n";
    code << "void " << handleName << "_resume(struct " << handleName << "* handle) {\n";
    code << "    if (handle->frame) {\n";
    code << "        " << funcName << "_resume(handle->frame);\n";
    code << "    }\n";
    code << "}\n";

    return code.str();
}

std::string FrameAllocator::generateDestroyOperation(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    std::ostringstream code;
    std::string handleName = getHandleTypeName(FD);
    std::string funcName = FD->getNameAsString();

    code << "// Destroy operation for " << funcName << "\n";
    code << "void " << handleName << "_destroy(struct " << handleName << "* handle) {\n";
    code << "    if (handle->frame) {\n";
    code << "        " << funcName << "_destroy(handle->frame);\n";
    code << "        handle->frame = NULL;\n";
    code << "    }\n";
    code << "}\n";

    return code.str();
}

std::string FrameAllocator::generateFrameInitialization(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    std::ostringstream code;
    std::string funcName = FD->getNameAsString();

    code << "    // Initialize frame\n";
    code << "    frame->state = 0;  // Initial state\n";
    code << "    frame->resume_fn = (void(*)(void*))" << funcName << "_resume;\n";
    code << "    frame->destroy_fn = (void(*)(void*))" << funcName << "_destroy;\n";

    // Copy parameters to frame
    if (FD->getNumParams() > 0) {
        code << "\n";
        code << "    // Copy parameters to frame\n";
        for (unsigned i = 0; i < FD->getNumParams(); ++i) {
            const ParmVarDecl* param = FD->getParamDecl(i);
            std::string paramName = param->getNameAsString();
            code << "    frame->" << paramName << " = " << paramName << ";\n";
        }
    }

    return code.str();
}

std::string FrameAllocator::generateHandleReturn(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    std::ostringstream code;
    std::string handleName = getHandleTypeName(FD);

    code << "    // Return coroutine handle\n";
    code << "    struct " << handleName << " handle;\n";
    code << "    handle.frame = frame;\n";
    code << "    return handle;\n";

    return code.str();
}

std::string FrameAllocator::getFrameTypeName(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }
    return FD->getNameAsString() + "_frame";
}

std::string FrameAllocator::getHandleTypeName(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    // Try to get the return type name
    QualType returnType = FD->getReturnType();
    if (auto* recordType = returnType->getAsCXXRecordDecl()) {
        return recordType->getNameAsString();
    }

    // Fallback to function name + _handle
    return FD->getNameAsString() + "_handle";
}

// ExceptionFrameGenerator.cpp - Implementation of exception frame generator
// Story #76: Implement Exception Frame Structure and Thread-Local Stack

#include "ExceptionFrameGenerator.h"
#include <sstream>

std::string ExceptionFrameGenerator::generateFrameStruct() const {
    // Generate the exception frame struct following PNaCl SJLJ pattern
    std::ostringstream oss;
    oss << "struct __cxx_exception_frame {\n"
        << "    jmp_buf jmpbuf;\n"
        << "    struct __cxx_exception_frame *next;\n"
        << "    const struct __cxx_action_entry *actions;\n"
        << "    void *exception_object;\n"
        << "    const char *exception_type;\n"
        << "};\n";
    return oss.str();
}

std::string ExceptionFrameGenerator::generateThreadLocalStack() const {
    // Generate thread-local exception stack declaration
    // _Thread_local ensures each thread has its own independent stack
    return "_Thread_local struct __cxx_exception_frame *__cxx_exception_stack = NULL;\n";
}

std::string ExceptionFrameGenerator::generateFramePush(const std::string& frameVar,
                                                        const std::string& actionsTable) const {
    // Generate code to push a frame onto the exception stack
    // This creates a new frame, links it to the current stack top, and makes it the new top
    std::ostringstream oss;
    oss << "struct __cxx_exception_frame " << frameVar << ";\n"
        << frameVar << ".next = __cxx_exception_stack;\n"
        << frameVar << ".actions = " << actionsTable << ";\n"
        << "__cxx_exception_stack = &" << frameVar << ";\n";
    return oss.str();
}

std::string ExceptionFrameGenerator::generateFramePop(const std::string& frameVar) const {
    // Generate code to pop a frame from the exception stack
    // This restores the previous stack frame
    std::ostringstream oss;
    oss << "__cxx_exception_stack = " << frameVar << ".next;\n";
    return oss.str();
}

std::string ExceptionFrameGenerator::generateActionEntryStruct() const {
    // Generate the action entry struct
    // Action entries map program counter ranges to catch handlers
    std::ostringstream oss;
    oss << "struct __cxx_action_entry {\n"
        << "    const void *start_pc;\n"
        << "    const void *end_pc;\n"
        << "    const void *handler;\n"
        << "    const char *type_info;\n"
        << "};\n";
    return oss.str();
}

std::string ExceptionFrameGenerator::generateExceptionSupportHeader() const {
    // Generate the complete exception_support.h header file
    std::ostringstream oss;

    // Include guard
    oss << "#ifndef __EXCEPTION_SUPPORT_H__\n"
        << "#define __EXCEPTION_SUPPORT_H__\n\n";

    // Required includes
    oss << "#include <setjmp.h>\n"
        << "#include <stddef.h>\n\n";

    // Action entry struct
    oss << "// Action table entry for mapping PC ranges to handlers\n"
        << generateActionEntryStruct() << "\n";

    // Exception frame struct
    oss << "// Exception frame for SJLJ exception handling\n"
        << generateFrameStruct() << "\n";

    // Thread-local stack declaration
    oss << "// Thread-local exception stack\n"
        << "extern " << generateThreadLocalStack() << "\n";

    // Close include guard
    oss << "#endif // __EXCEPTION_SUPPORT_H__\n";

    return oss.str();
}

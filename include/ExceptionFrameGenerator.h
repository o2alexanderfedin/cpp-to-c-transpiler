// ExceptionFrameGenerator.h - Exception frame structure and thread-local stack generator
// Story #76: Implement Exception Frame Structure and Thread-Local Stack
// SOLID Principles:
//   - Single Responsibility: Generates exception frame structures and stack operations
//   - Open/Closed: Extensible for different exception handling strategies
//   - Dependency Inversion: Depends on abstractions (string generation)

#ifndef EXCEPTION_FRAME_GENERATOR_H
#define EXCEPTION_FRAME_GENERATOR_H

#include <string>

/// @brief Generates exception frame structures and thread-local stack management code
///
/// This class is responsible for generating the C code structures and operations
/// needed for SJLJ (setjmp/longjmp) exception handling. It creates:
/// - Exception frame struct definitions
/// - Thread-local stack declarations
/// - Frame push/pop operations
/// - Complete exception support header
class ExceptionFrameGenerator {
public:
    /// @brief Generate the exception frame struct definition
    /// @return C code defining struct __cxx_exception_frame
    std::string generateFrameStruct() const;

    /// @brief Generate the thread-local exception stack declaration
    /// @return C code declaring _Thread_local __cxx_exception_stack
    std::string generateThreadLocalStack() const;

    /// @brief Generate code to push a frame onto the exception stack
    /// @param frameVar Name of the frame variable
    /// @param actionsTable Name of the action table for this try block
    /// @return C code that initializes and pushes the frame
    std::string generateFramePush(const std::string& frameVar,
                                   const std::string& actionsTable) const;

    /// @brief Generate code to pop a frame from the exception stack
    /// @param frameVar Name of the frame variable to pop
    /// @return C code that restores the previous stack frame
    std::string generateFramePop(const std::string& frameVar) const;

    /// @brief Generate the complete exception_support.h header file
    /// @return Complete header with frame struct, stack declaration, and includes
    std::string generateExceptionSupportHeader() const;

private:
    /// @brief Generate the action entry struct (forward declaration or definition)
    /// @return C code for struct __cxx_action_entry
    std::string generateActionEntryStruct() const;
};

#endif // EXCEPTION_FRAME_GENERATOR_H

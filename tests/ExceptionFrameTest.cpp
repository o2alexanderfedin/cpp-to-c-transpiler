// ExceptionFrameTest.cpp - Tests for exception frame structure and thread-local stack (Story #76)
// Following TDD: Write failing tests first

#include "ExceptionFrameGenerator.h"
#include <cassert>
#include <iostream>
#include <string>

// ============================================================================
// Test Suite: Exception Frame Structure Generation (AC #1)
// ============================================================================

void test_GenerateExceptionFrameStruct() {
    std::cout << "Running test_GenerateExceptionFrameStruct... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating the exception frame struct definition
    std::string frameStruct = generator.generateFrameStruct();

    // THEN: Should contain all required fields
    assert(frameStruct.find("struct __cxx_exception_frame") != std::string::npos);
    assert(frameStruct.find("jmp_buf jmpbuf") != std::string::npos);
    assert(frameStruct.find("struct __cxx_exception_frame *next") != std::string::npos);
    assert(frameStruct.find("const struct __cxx_action_entry *actions") != std::string::npos);
    assert(frameStruct.find("void *exception_object") != std::string::npos);
    assert(frameStruct.find("const char *exception_type") != std::string::npos);

    std::cout << "✓" << std::endl;
}

void test_FrameStructFieldOrder() {
    std::cout << "Running test_FrameStructFieldOrder... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating the exception frame struct definition
    std::string frameStruct = generator.generateFrameStruct();

    // THEN: Fields should be in correct order for memory layout
    size_t jmpbuf_pos = frameStruct.find("jmp_buf jmpbuf");
    size_t next_pos = frameStruct.find("struct __cxx_exception_frame *next");
    size_t actions_pos = frameStruct.find("const struct __cxx_action_entry *actions");
    size_t obj_pos = frameStruct.find("void *exception_object");
    size_t type_pos = frameStruct.find("const char *exception_type");

    assert(jmpbuf_pos < next_pos);
    assert(next_pos < actions_pos);
    assert(actions_pos < obj_pos);
    assert(obj_pos < type_pos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite: Thread-Local Stack Declaration (AC #2)
// ============================================================================

void test_GenerateThreadLocalStack() {
    std::cout << "Running test_GenerateThreadLocalStack... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating the thread-local stack declaration
    std::string stackDecl = generator.generateThreadLocalStack();

    // THEN: Should declare thread-local exception stack
    assert(stackDecl.find("_Thread_local") != std::string::npos);
    assert(stackDecl.find("struct __cxx_exception_frame") != std::string::npos);
    assert(stackDecl.find("*__cxx_exception_stack") != std::string::npos);
    assert(stackDecl.find("= NULL") != std::string::npos);

    std::cout << "✓" << std::endl;
}

void test_ThreadLocalStackInitializedToNull() {
    std::cout << "Running test_ThreadLocalStackInitializedToNull... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating the thread-local stack declaration
    std::string stackDecl = generator.generateThreadLocalStack();

    // THEN: Should initialize to NULL
    assert(stackDecl.find("NULL") != std::string::npos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite: Frame Push/Pop Operations (AC #3)
// ============================================================================

void test_GenerateFramePush() {
    std::cout << "Running test_GenerateFramePush... ";

    // GIVEN: An exception frame generator and action table name
    ExceptionFrameGenerator generator;
    std::string actionsTable = "test_actions_table";
    std::string frameVar = "frame";

    // WHEN: Generating frame push code
    std::string pushCode = generator.generateFramePush(frameVar, actionsTable);

    // THEN: Should link frame to stack
    assert(pushCode.find("struct __cxx_exception_frame " + frameVar) != std::string::npos);
    assert(pushCode.find(frameVar + ".next = __cxx_exception_stack") != std::string::npos);
    assert(pushCode.find(frameVar + ".actions = " + actionsTable) != std::string::npos);
    assert(pushCode.find("__cxx_exception_stack = &" + frameVar) != std::string::npos);

    std::cout << "✓" << std::endl;
}

void test_GenerateFramePop() {
    std::cout << "Running test_GenerateFramePop... ";

    // GIVEN: An exception frame generator and frame variable
    ExceptionFrameGenerator generator;
    std::string frameVar = "frame";

    // WHEN: Generating frame pop code
    std::string popCode = generator.generateFramePop(frameVar);

    // THEN: Should restore previous stack frame
    assert(popCode.find("__cxx_exception_stack = " + frameVar + ".next") != std::string::npos);

    std::cout << "✓" << std::endl;
}

void test_FramePushPopSymmetry() {
    std::cout << "Running test_FramePushPopSymmetry... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;
    std::string frameVar = "test_frame";
    std::string actionsTable = "actions";

    // WHEN: Generating push and pop code
    std::string pushCode = generator.generateFramePush(frameVar, actionsTable);
    std::string popCode = generator.generateFramePop(frameVar);

    // THEN: Push sets stack, pop restores it
    assert(pushCode.find("__cxx_exception_stack = &" + frameVar) != std::string::npos);
    assert(popCode.find("__cxx_exception_stack = " + frameVar + ".next") != std::string::npos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite: Frame Initialization (AC #4)
// ============================================================================

void test_FrameInitializationSetsActions() {
    std::cout << "Running test_FrameInitializationSetsActions... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;
    std::string frameVar = "myframe";
    std::string actionsTable = "my_actions";

    // WHEN: Generating frame push code
    std::string pushCode = generator.generateFramePush(frameVar, actionsTable);

    // THEN: Should initialize actions pointer
    assert(pushCode.find(frameVar + ".actions = " + actionsTable) != std::string::npos);

    std::cout << "✓" << std::endl;
}

void test_FrameInitializationLinksNext() {
    std::cout << "Running test_FrameInitializationLinksNext... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;
    std::string frameVar = "myframe";
    std::string actionsTable = "actions";

    // WHEN: Generating frame push code
    std::string pushCode = generator.generateFramePush(frameVar, actionsTable);

    // THEN: Should link to previous frame
    assert(pushCode.find(frameVar + ".next = __cxx_exception_stack") != std::string::npos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite: Header Generation (AC #6)
// ============================================================================

void test_GenerateExceptionSupportHeader() {
    std::cout << "Running test_GenerateExceptionSupportHeader... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating exception support header
    std::string header = generator.generateExceptionSupportHeader();

    // THEN: Should contain include guard
    assert(header.find("#ifndef __EXCEPTION_SUPPORT_H__") != std::string::npos);
    assert(header.find("#define __EXCEPTION_SUPPORT_H__") != std::string::npos);
    assert(header.find("#endif") != std::string::npos);

    std::cout << "✓" << std::endl;
}

void test_HeaderContainsFrameStruct() {
    std::cout << "Running test_HeaderContainsFrameStruct... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating exception support header
    std::string header = generator.generateExceptionSupportHeader();

    // THEN: Should contain frame struct definition
    assert(header.find("struct __cxx_exception_frame") != std::string::npos);
    assert(header.find("jmp_buf jmpbuf") != std::string::npos);

    std::cout << "✓" << std::endl;
}

void test_HeaderContainsThreadLocalStack() {
    std::cout << "Running test_HeaderContainsThreadLocalStack... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating exception support header
    std::string header = generator.generateExceptionSupportHeader();

    // THEN: Should contain thread-local stack declaration
    assert(header.find("_Thread_local") != std::string::npos);
    assert(header.find("__cxx_exception_stack") != std::string::npos);

    std::cout << "✓" << std::endl;
}

void test_HeaderIncludesSetjmp() {
    std::cout << "Running test_HeaderIncludesSetjmp... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating exception support header
    std::string header = generator.generateExceptionSupportHeader();

    // THEN: Should include setjmp.h for jmp_buf
    assert(header.find("#include <setjmp.h>") != std::string::npos);

    std::cout << "✓" << std::endl;
}

void test_HeaderIncludesStddef() {
    std::cout << "Running test_HeaderIncludesStddef... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating exception support header
    std::string header = generator.generateExceptionSupportHeader();

    // THEN: Should include stddef.h for NULL
    assert(header.find("#include <stddef.h>") != std::string::npos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite: Action Entry Struct (for completeness)
// ============================================================================

void test_HeaderContainsActionEntryStruct() {
    std::cout << "Running test_HeaderContainsActionEntryStruct... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating exception support header
    std::string header = generator.generateExceptionSupportHeader();

    // THEN: Should contain action entry struct (forward declaration or definition)
    assert(header.find("struct __cxx_action_entry") != std::string::npos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Thread Safety Tests (AC #5)
// ============================================================================

void test_ThreadLocalStackDeclaration() {
    std::cout << "Running test_ThreadLocalStackDeclaration... ";

    // GIVEN: An exception frame generator
    ExceptionFrameGenerator generator;

    // WHEN: Generating thread-local stack
    std::string stackDecl = generator.generateThreadLocalStack();

    // THEN: Should use _Thread_local for thread safety
    assert(stackDecl.find("_Thread_local") != std::string::npos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Main
// ============================================================================

int main() {
    std::cout << "===================================" << std::endl;
    std::cout << "Exception Frame Structure Tests" << std::endl;
    std::cout << "Story #76" << std::endl;
    std::cout << "===================================" << std::endl;

    // Exception Frame Structure Tests (AC #1)
    test_GenerateExceptionFrameStruct();
    test_FrameStructFieldOrder();

    // Thread-Local Stack Tests (AC #2)
    test_GenerateThreadLocalStack();
    test_ThreadLocalStackInitializedToNull();

    // Frame Push/Pop Tests (AC #3)
    test_GenerateFramePush();
    test_GenerateFramePop();
    test_FramePushPopSymmetry();

    // Frame Initialization Tests (AC #4)
    test_FrameInitializationSetsActions();
    test_FrameInitializationLinksNext();

    // Thread Safety Tests (AC #5)
    test_ThreadLocalStackDeclaration();

    // Header Generation Tests (AC #6)
    test_GenerateExceptionSupportHeader();
    test_HeaderContainsFrameStruct();
    test_HeaderContainsThreadLocalStack();
    test_HeaderIncludesSetjmp();
    test_HeaderIncludesStddef();

    // Action Entry Struct Tests
    test_HeaderContainsActionEntryStruct();

    std::cout << "===================================" << std::endl;
    std::cout << "All tests passed! ✓" << std::endl;
    std::cout << "===================================" << std::endl;

    return 0;
}

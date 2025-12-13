// TryCatchTransformerTest.cpp - Tests for try-catch to setjmp/longjmp transformation
// Story #78: Implement setjmp/longjmp Injection for Try-Catch Blocks
// Test-Driven Development: Write tests first, then implement

#include "TryCatchTransformer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <string>

using namespace clang;

// Helper visitor to find try statements in AST
class TryStmtFinder : public RecursiveASTVisitor<TryStmtFinder> {
public:
    CXXTryStmt *foundTryStmt = nullptr;

    bool VisitCXXTryStmt(CXXTryStmt *tryStmt) {
        if (!foundTryStmt) {
            foundTryStmt = tryStmt;
        }
        return true;
    }
};

// Test helper: Parse C++ code and find first try statement
CXXTryStmt* parseTryStatement(const std::string& code) {
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
    if (!AST) {
        std::cerr << "Failed to parse code" << std::endl;
        return nullptr;
    }

    TryStmtFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    return finder.foundTryStmt;
}

// Test 1: Generate setjmp guard
void test_generateSetjmpGuard() {
    std::cout << "Test 1: Generate setjmp guard... ";

    TryCatchTransformer transformer;
    std::string result = transformer.generateSetjmpGuard("frame");

    // Should generate: if (setjmp(frame.jmpbuf) == 0)
    assert(result.find("setjmp") != std::string::npos);
    assert(result.find("frame.jmpbuf") != std::string::npos);
    assert(result.find("== 0") != std::string::npos);

    std::cout << "PASS" << std::endl;
}

// Test 2: Transform basic try-catch block
void test_transformBasicTryCatch() {
    std::cout << "Test 2: Transform basic try-catch block... ";

    std::string code = R"(
        struct Error {
            int code;
        };

        void test() {
            try {
                int x = 42;
            } catch (Error& e) {
                int y = e.code;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.transformTryCatch(tryStmt, "frame", "actions_table_0");

    // Verify key components are present
    assert(result.find("struct __cxx_exception_frame frame") != std::string::npos);
    assert(result.find("frame.actions = actions_table_0") != std::string::npos);
    assert(result.find("setjmp(frame.jmpbuf) == 0") != std::string::npos);
    assert(result.find("__cxx_exception_stack = &frame") != std::string::npos);
    assert(result.find("__cxx_exception_stack = frame.next") != std::string::npos);

    std::cout << "PASS" << std::endl;
}

// Test 3: Generate try body with frame push/pop
void test_generateTryBody() {
    std::cout << "Test 3: Generate try body with frame push/pop... ";

    std::string code = R"(
        void test() {
            try {
                int x = 42;
            } catch (...) {
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.generateTryBody(tryStmt, "frame");

    // Should have frame push at start and pop at end
    assert(result.find("__cxx_exception_stack = &frame") != std::string::npos);
    assert(result.find("__cxx_exception_stack = frame.next") != std::string::npos);

    std::cout << "PASS" << std::endl;
}

// Test 4: Generate catch handlers with type checking
void test_generateCatchHandlers() {
    std::cout << "Test 4: Generate catch handlers with type checking... ";

    std::string code = R"(
        struct Error {
            int code;
        };

        void test() {
            try {
                int x = 42;
            } catch (Error& e) {
                int y = e.code;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // Should have type check for Error
    assert(result.find("frame.exception_type") != std::string::npos);
    assert(result.find("strcmp") != std::string::npos ||
           result.find("Error") != std::string::npos);

    std::cout << "PASS" << std::endl;
}

// Test 5: Generate exception object cast
void test_generateExceptionObjectCast() {
    std::cout << "Test 5: Generate exception object cast... ";

    std::string code = R"(
        struct Error {
            int code;
        };

        void test() {
            try {
                int x = 42;
            } catch (Error& e) {
                int y = e.code;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);
    assert(tryStmt->getNumHandlers() > 0);

    CXXCatchStmt *catchStmt = tryStmt->getHandler(0);
    VarDecl *exceptionVar = catchStmt->getExceptionDecl();
    assert(exceptionVar != nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.generateExceptionObjectCast(exceptionVar, "frame");

    // Should cast frame.exception_object to Error*
    assert(result.find("frame.exception_object") != std::string::npos);
    assert(result.find("struct Error") != std::string::npos || result.find("Error") != std::string::npos);

    std::cout << "PASS" << std::endl;
}

// Test 6: Generate exception cleanup
void test_generateExceptionCleanup() {
    std::cout << "Test 6: Generate exception cleanup... ";

    std::string code = R"(
        struct Error {
            ~Error();
            int code;
        };

        void test() {
            try {
                int x = 42;
            } catch (Error& e) {
                int y = e.code;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);
    assert(tryStmt->getNumHandlers() > 0);

    CXXCatchStmt *catchStmt = tryStmt->getHandler(0);
    VarDecl *exceptionVar = catchStmt->getExceptionDecl();
    QualType exceptionType = exceptionVar->getType();

    TryCatchTransformer transformer;
    std::string result = transformer.generateExceptionCleanup(exceptionType, "e");

    // Should call destructor and free
    assert(result.find("dtor") != std::string::npos || result.find("~") != std::string::npos);
    assert(result.find("free") != std::string::npos);

    std::cout << "PASS" << std::endl;
}

// Test 7: Multiple catch handlers
void test_multipleCatchHandlers() {
    std::cout << "Test 7: Multiple catch handlers... ";

    std::string code = R"(
        struct Error1 { int x; };
        struct Error2 { int y; };

        void test() {
            try {
                int x = 42;
            } catch (Error1& e1) {
                int a = e1.x;
            } catch (Error2& e2) {
                int b = e2.y;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);
    assert(tryStmt->getNumHandlers() == 2);

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // Should have type checks for both Error1 and Error2
    assert(result.find("Error1") != std::string::npos);
    assert(result.find("Error2") != std::string::npos);

    std::cout << "PASS" << std::endl;
}

// Test 8: Integration test - complete transformation
void test_completeTransformation() {
    std::cout << "Test 8: Complete transformation (integration)... ";

    std::string code = R"(
        struct MyError {
            int errorCode;
            ~MyError();
        };

        void mayThrow();
        void handle(int code);

        void test() {
            try {
                mayThrow();
            } catch (MyError& e) {
                handle(e.errorCode);
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.transformTryCatch(tryStmt, "frame", "actions_table_0");

    // Verify all key components
    assert(result.find("struct __cxx_exception_frame frame") != std::string::npos);  // Frame declaration
    assert(result.find("frame.next = __cxx_exception_stack") != std::string::npos);   // Frame linkage
    assert(result.find("frame.actions = actions_table_0") != std::string::npos);      // Action table
    assert(result.find("setjmp(frame.jmpbuf) == 0") != std::string::npos);            // setjmp guard
    assert(result.find("__cxx_exception_stack = &frame") != std::string::npos);       // Frame push
    assert(result.find("__cxx_exception_stack = frame.next") != std::string::npos);   // Frame pop
    assert(result.find("MyError") != std::string::npos);                               // Exception type

    std::cout << "PASS" << std::endl;
    std::cout << "\nGenerated code:\n" << result << std::endl;
}

int main() {
    std::cout << "=== TryCatchTransformer Tests ===" << std::endl;
    std::cout << "Story #78: setjmp/longjmp Injection for Try-Catch Blocks" << std::endl;
    std::cout << std::endl;

    // Run all tests
    test_generateSetjmpGuard();
    test_transformBasicTryCatch();
    test_generateTryBody();
    test_generateCatchHandlers();
    test_generateExceptionObjectCast();
    test_generateExceptionCleanup();
    test_multipleCatchHandlers();
    test_completeTransformation();

    std::cout << "\n=== All Tests Passed ===" << std::endl;
    return 0;
}

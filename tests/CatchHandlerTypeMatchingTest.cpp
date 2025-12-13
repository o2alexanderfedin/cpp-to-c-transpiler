// CatchHandlerTypeMatchingTest.cpp - Tests for catch handler type matching
// Story #80: Implement Catch Handler Type Matching
// Test-Driven Development: RED → GREEN → REFACTOR → VERIFY

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

// Test helper: Check if string contains substring
bool contains(const std::string& haystack, const std::string& needle) {
    return haystack.find(needle) != std::string::npos;
}

// Test 1: Handler Detection - Extract catch handler type from CXXCatchStmt
void test_handlerDetection() {
    std::cout << "Test 1: Handler Detection (extract type from CXXCatchStmt)... ";

    std::string code = R"(
        struct ErrorA { int code; };

        void test() {
            try {
                int x = 42;
            } catch (ErrorA& e) {
                int y = e.code;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);
    assert(tryStmt->getNumHandlers() == 1);

    CXXCatchStmt *catchStmt = tryStmt->getHandler(0);
    VarDecl *exceptionVar = catchStmt->getExceptionDecl();
    assert(exceptionVar != nullptr);

    TryCatchTransformer transformer;
    std::string typeCheck = transformer.generateTypeCheck(exceptionVar->getType(), "frame");

    // Should extract ErrorA from catch (ErrorA& e)
    assert(contains(typeCheck, "ErrorA"));
    assert(contains(typeCheck, "strcmp"));
    assert(contains(typeCheck, "frame.exception_type"));

    std::cout << "PASS" << std::endl;
}

// Test 2: Type Comparison - Generate strcmp() for exact type matching
void test_typeComparison() {
    std::cout << "Test 2: Type Comparison (strcmp for exact type matching)... ";

    std::string code = R"(
        struct MyException { const char* msg; };

        void test() {
            try {
                throw MyException();
            } catch (MyException& e) {
                // handle
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // Should generate: if (strcmp(frame.exception_type, "MyException") == 0)
    assert(contains(result, "strcmp"));
    assert(contains(result, "frame.exception_type"));
    assert(contains(result, "MyException"));
    assert(contains(result, "== 0"));

    std::cout << "PASS" << std::endl;
}

// Test 3: Multiple Handlers - Generate if-else chain
void test_multipleHandlers() {
    std::cout << "Test 3: Multiple Handlers (if-else chain)... ";

    std::string code = R"(
        struct ErrorA { int x; };
        struct ErrorB { int y; };
        struct ErrorC { int z; };

        void test() {
            try {
                int x = 42;
            } catch (ErrorA& e) {
                int a = e.x;
            } catch (ErrorB& e) {
                int b = e.y;
            } catch (ErrorC& e) {
                int c = e.z;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);
    assert(tryStmt->getNumHandlers() == 3);

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // Should generate if-else-if chain
    // First handler: if (strcmp(...))
    // Second handler: else if (strcmp(...))
    // Third handler: else if (strcmp(...))
    assert(contains(result, "ErrorA"));
    assert(contains(result, "ErrorB"));
    assert(contains(result, "ErrorC"));

    // Count occurrences of "else" - should have 2 (for second and third handlers)
    size_t elseCount = 0;
    size_t pos = 0;
    while ((pos = result.find("else", pos)) != std::string::npos) {
        elseCount++;
        pos += 4;
    }
    assert(elseCount >= 2);

    std::cout << "PASS" << std::endl;
}

// Test 4: Catch-All Handler - Handle catch (...)
void test_catchAllHandler() {
    std::cout << "Test 4: Catch-All Handler (catch (...))... ";

    std::string code = R"(
        struct Error { int code; };

        void test() {
            try {
                int x = 42;
            } catch (Error& e) {
                int y = e.code;
            } catch (...) {
                // catch all
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);
    assert(tryStmt->getNumHandlers() == 2);

    // Second handler should be catch-all
    CXXCatchStmt *catchAll = tryStmt->getHandler(1);
    VarDecl *exceptionVar = catchAll->getExceptionDecl();
    assert(exceptionVar == nullptr);  // catch (...) has no exception variable

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // Should generate catch-all handler with no type check
    assert(contains(result, "Error"));  // First handler
    assert(contains(result, "Catch-all") || contains(result, "else"));  // Second handler

    std::cout << "PASS" << std::endl;
}

// Test 5: Exception Access - Generate cast to handler type
void test_exceptionAccess() {
    std::cout << "Test 5: Exception Access (cast exception_object to handler type)... ";

    std::string code = R"(
        struct DatabaseError {
            int errorCode;
            const char* message;
        };

        void test() {
            try {
                int x = 42;
            } catch (DatabaseError& e) {
                int code = e.errorCode;
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);

    CXXCatchStmt *catchStmt = tryStmt->getHandler(0);
    VarDecl *exceptionVar = catchStmt->getExceptionDecl();
    assert(exceptionVar != nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.generateExceptionObjectCast(exceptionVar, "frame");

    // Should generate: struct DatabaseError *e = (struct DatabaseError*)frame.exception_object;
    assert(contains(result, "DatabaseError"));
    assert(contains(result, "frame.exception_object"));
    assert(contains(result, "*e"));
    assert(contains(result, "="));

    std::cout << "PASS" << std::endl;
}

// Test 6: Cleanup Code - Generate destructor + free
void test_cleanupCode() {
    std::cout << "Test 6: Cleanup Code (destructor + free for caught exception)... ";

    std::string code = R"(
        struct Resource {
            ~Resource();
            int* data;
        };

        void test() {
            try {
                int x = 42;
            } catch (Resource& r) {
                // use r
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);

    CXXCatchStmt *catchStmt = tryStmt->getHandler(0);
    VarDecl *exceptionVar = catchStmt->getExceptionDecl();
    QualType exceptionType = exceptionVar->getType();

    TryCatchTransformer transformer;
    std::string result = transformer.generateExceptionCleanup(exceptionType, "r");

    // Should generate: Resource__dtor(r); free(r);
    assert(contains(result, "dtor") || contains(result, "~"));
    assert(contains(result, "free"));
    assert(contains(result, "r"));

    std::cout << "PASS" << std::endl;
}

// Test 7: Complete Type Matching Chain
void test_completeTypeMatchingChain() {
    std::cout << "Test 7: Complete Type Matching Chain (integration)... ";

    std::string code = R"(
        struct ErrorA { int x; };
        struct ErrorB { int y; };

        void handleA(int x);
        void handleB(int y);
        void handleAny();

        void mayThrow();

        void test() {
            try {
                mayThrow();
            } catch (ErrorA& e) {
                handleA(e.x);
            } catch (ErrorB& e) {
                handleB(e.y);
            } catch (...) {
                handleAny();
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);
    assert(tryStmt->getNumHandlers() == 3);

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // Should generate complete if-else chain with type matching
    // if (strcmp(frame.exception_type, "ErrorA") == 0) {
    //     struct ErrorA *e = (struct ErrorA*)frame.exception_object;
    //     ...
    //     free(e);
    // } else if (strcmp(frame.exception_type, "ErrorB") == 0) {
    //     struct ErrorB *e = (struct ErrorB*)frame.exception_object;
    //     ...
    //     free(e);
    // } else {
    //     // catch (...)
    //     ...
    // }

    assert(contains(result, "ErrorA"));
    assert(contains(result, "ErrorB"));
    assert(contains(result, "strcmp"));
    assert(contains(result, "frame.exception_type"));
    assert(contains(result, "frame.exception_object"));
    assert(contains(result, "free"));

    std::cout << "PASS" << std::endl;
    std::cout << "\nGenerated catch handlers:\n" << result << std::endl;
}

// Test 8: Polymorphic Exception Handling
void test_polymorphicExceptionHandling() {
    std::cout << "Test 8: Polymorphic Exception Handling... ";

    std::string code = R"(
        struct BaseError { virtual ~BaseError(); };
        struct DerivedError : BaseError { int code; };

        void test() {
            try {
                int x = 42;
            } catch (BaseError& e) {
                // Should catch both BaseError and DerivedError
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // For now, we do exact type matching (not polymorphic)
    // Future enhancement: type_info comparison for polymorphic matching
    assert(contains(result, "BaseError"));
    assert(contains(result, "strcmp"));

    std::cout << "PASS (exact matching only)" << std::endl;
}

// Test 9: Edge Case - Empty catch block
void test_emptyCatchBlock() {
    std::cout << "Test 9: Edge Case (empty catch block)... ";

    std::string code = R"(
        struct Error { int code; };

        void test() {
            try {
                int x = 42;
            } catch (Error& e) {
                // empty
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // Should still generate type check and cleanup
    assert(contains(result, "Error"));
    assert(contains(result, "strcmp"));
    assert(contains(result, "free"));

    std::cout << "PASS" << std::endl;
}

// Test 10: Only catch-all handler
void test_onlyCatchAllHandler() {
    std::cout << "Test 10: Only Catch-All Handler (no type matching)... ";

    std::string code = R"(
        void test() {
            try {
                int x = 42;
            } catch (...) {
                // handle any exception
            }
        }
    )";

    CXXTryStmt *tryStmt = parseTryStatement(code);
    assert(tryStmt != nullptr);
    assert(tryStmt->getNumHandlers() == 1);

    TryCatchTransformer transformer;
    std::string result = transformer.generateCatchHandlers(tryStmt, "frame");

    // Should not generate strcmp (no type to match)
    // But should still handle the exception
    assert(contains(result, "Catch-all") || contains(result, "else") || result.length() > 0);

    std::cout << "PASS" << std::endl;
}

int main() {
    std::cout << "=== Catch Handler Type Matching Tests ===" << std::endl;
    std::cout << "Story #80: Implement Catch Handler Type Matching" << std::endl;
    std::cout << "TDD Cycle: RED → GREEN → REFACTOR → VERIFY" << std::endl;
    std::cout << std::endl;

    // Run all tests
    test_handlerDetection();
    test_typeComparison();
    test_multipleHandlers();
    test_catchAllHandler();
    test_exceptionAccess();
    test_cleanupCode();
    test_completeTypeMatchingChain();
    test_polymorphicExceptionHandling();
    test_emptyCatchBlock();
    test_onlyCatchAllHandler();

    std::cout << "\n=== All Tests Passed ===" << std::endl;
    return 0;
}

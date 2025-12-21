// TDD Tests for ACSLMemoryPredicateAnalyzer - Phase 6, v1.23.0
// Advanced memory reasoning predicates
//
// Epic #193: ACSL Annotation Generation for Transpiled Code
// Phase 6: Memory Predicates (\allocable, \freeable, \block_length, \base_addr)

#include "ACSLMemoryPredicateAnalyzer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <string>
#include <memory>
#include <vector>

using namespace clang;

// Simple test framework
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }
#define ASSERT_CONTAINS(haystack, needle, msg) \
    if ((haystack).find(needle) == std::string::npos) { \
        TEST_FAIL("", std::string(msg) + " - Expected to find: " + needle); \
        return; \
    }
#define ASSERT_NOT_CONTAINS(haystack, needle, msg) \
    if ((haystack).find(needle) != std::string::npos) { \
        TEST_FAIL("", std::string(msg) + " - Did not expect to find: " + needle); \
        return; \
    }

// Store AST units to prevent premature destruction
// FIX: Heap-use-after-free bug - parseFunctionDecl() was returning FunctionDecl*
// pointers that became dangling when the ASTUnit was destroyed. This vector keeps
// all ASTUnits alive until program exit, preventing use-after-free crashes.
static std::vector<std::unique_ptr<ASTUnit>> persistentASTs;

// Helper: Parse C++ code and return FunctionDecl
FunctionDecl* parseFunctionDecl(const std::string& code, const std::string& funcName) {
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
    if (!AST) return nullptr;

    ASTContext& ctx = AST->getASTContext();
    TranslationUnitDecl* TU = ctx.getTranslationUnitDecl();

    FunctionDecl* result = nullptr;
    for (auto* decl : TU->decls()) {
        if (auto* func = dyn_cast<FunctionDecl>(decl)) {
            if (func->getNameAsString() == funcName) {
                result = func;
                break;
            }
        }
    }

    // Keep AST alive until program exit to prevent dangling pointers
    persistentASTs.push_back(std::move(AST));
    return result;
}

// Test 1: AllocablePrecondition - malloc/new requires
void test_AllocablePrecondition() {
    TEST_START("AllocablePrecondition");

    std::string code = R"(
        #include <cstdlib>
        void* allocate(size_t size) {
            return malloc(size);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "allocate");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "\\allocable", "Should generate \\allocable precondition");
    ASSERT_CONTAINS(contract, "size", "Should reference size parameter");

    TEST_PASS("AllocablePrecondition");
}

// Test 2: FreeablePrecondition - free/delete requires
void test_FreeablePrecondition() {
    TEST_START("FreeablePrecondition");

    std::string code = R"(
        #include <cstdlib>
        void deallocate(void* ptr) {
            free(ptr);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "deallocate");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "\\freeable(ptr)", "Should generate \\freeable precondition");
    ASSERT_CONTAINS(contract, "ensures !\\valid(ptr)", "Should ensure pointer is no longer valid after free");

    TEST_PASS("FreeablePrecondition");
}

// Test 3: BlockLengthPostcondition - Allocation size tracking
void test_BlockLengthPostcondition() {
    TEST_START("BlockLengthPostcondition");

    std::string code = R"(
        #include <cstdlib>
        void* allocate(size_t size) {
            return malloc(size);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "allocate");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "\\block_length(\\result)", "Should generate \\block_length for allocation");
    ASSERT_CONTAINS(contract, "== size", "Block length should equal size parameter");

    TEST_PASS("BlockLengthPostcondition");
}

// Test 4: BaseAddressComputation - Base pointer reasoning
void test_BaseAddressComputation() {
    TEST_START("BaseAddressComputation");

    std::string code = R"(
        void* get_base(void* ptr) {
            return (void*)((unsigned long)ptr & ~0xFUL);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "get_base");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "\\base_addr", "Should use \\base_addr for base pointer");
    ASSERT_CONTAINS(contract, "\\result", "Should reference result in postcondition");

    TEST_PASS("BaseAddressComputation");
}

// Test 5: PointerArithmeticSafety - Offset within bounds
void test_PointerArithmeticSafety() {
    TEST_START("PointerArithmeticSafety");

    std::string code = R"(
        void* offset_pointer(void* ptr, size_t offset) {
            return (char*)ptr + offset;
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "offset_pointer");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "offset < \\block_length(ptr)", "Should verify offset is within block length");
    ASSERT_CONTAINS(contract, "\\valid(\\result)", "Result should be valid");

    TEST_PASS("PointerArithmeticSafety");
}

// Test 6: CustomAllocator - Pool/arena allocators
void test_CustomAllocator() {
    TEST_START("CustomAllocator");

    std::string code = R"(
        class MemoryPool {
            void* allocate(size_t size);
        };
        void* MemoryPool::allocate(size_t size) {
            return nullptr; // simplified
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "allocate");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "\\allocable", "Custom allocator should have \\allocable");
    ASSERT_CONTAINS(contract, "\\fresh(\\result", "Should ensure fresh memory");

    TEST_PASS("CustomAllocator");
}

// Test 7: PartialAllocation - Struct member allocation
void test_PartialAllocation() {
    TEST_START("PartialAllocation");

    std::string code = R"(
        struct Data {
            void* buffer;
        };
        void allocate_member(Data* data, size_t size) {
            data->buffer = malloc(size);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "allocate_member");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "\\valid(data)", "Struct pointer should be valid");
    ASSERT_CONTAINS(contract, "\\fresh", "Member allocation should be fresh");

    TEST_PASS("PartialAllocation");
}

// Test 8: ReallocTracking - Reallocation size update
void test_ReallocTracking() {
    TEST_START("ReallocTracking");

    std::string code = R"(
        #include <cstdlib>
        void* resize(void* ptr, size_t old_size, size_t new_size) {
            return realloc(ptr, new_size);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "resize");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "\\freeable(ptr)", "Realloc requires freeable pointer");
    ASSERT_CONTAINS(contract, "\\block_length(\\result) == new_size", "New block should have new size");

    TEST_PASS("ReallocTracking");
}

// Test 9: DoubleFreeDetection - Freeable only once
void test_DoubleFreeDetection() {
    TEST_START("DoubleFreeDetection");

    std::string code = R"(
        #include <cstdlib>
        void safe_free(void** ptr) {
            if (ptr && *ptr) {
                free(*ptr);
                *ptr = nullptr;
            }
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "safe_free");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "\\freeable", "Should check freeable before free");
    ASSERT_CONTAINS(contract, "!\\valid", "After free, pointer should not be valid");

    TEST_PASS("DoubleFreeDetection");
}

// Test 10: UseAfterFreeDetection - Not valid after free
void test_UseAfterFreeDetection() {
    TEST_START("UseAfterFreeDetection");

    std::string code = R"(
        #include <cstdlib>
        void release(void* ptr) {
            free(ptr);
            // ptr should not be dereferenced here
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "release");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "requires \\freeable(ptr)", "Should require freeable");
    ASSERT_CONTAINS(contract, "ensures !\\valid(ptr)", "Should ensure not valid after free");

    TEST_PASS("UseAfterFreeDetection");
}

// Test 11: FreshMemoryAllocation - Memory allocation freshness
void test_FreshMemoryAllocation() {
    TEST_START("FreshMemoryAllocation");

    std::string code = R"(
        #include <cstdlib>
        void* create_buffer(size_t size) {
            void* buf = malloc(size);
            return buf;
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "create_buffer");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_CONTAINS(contract, "\\fresh(\\result, size)", "Allocated memory should be fresh");
    ASSERT_CONTAINS(contract, "\\valid(\\result", "Result should be valid or null");

    TEST_PASS("FreshMemoryAllocation");
}

// Test 12: NoMemoryPredicates - Non-memory function
void test_NoMemoryPredicates() {
    TEST_START("NoMemoryPredicates");

    std::string code = R"(
        int add(int a, int b) {
            return a + b;
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "add");
    ASSERT(func != nullptr, "Failed to parse function");

    ACSLMemoryPredicateAnalyzer analyzer;
    std::string contract = analyzer.generateMemoryPredicates(func);

    ASSERT_NOT_CONTAINS(contract, "\\allocable", "Non-memory function should not have allocable");
    ASSERT_NOT_CONTAINS(contract, "\\freeable", "Non-memory function should not have freeable");
    ASSERT_NOT_CONTAINS(contract, "\\block_length", "Non-memory function should not have block_length");

    TEST_PASS("NoMemoryPredicates");
}

int main() {
    std::cout << "=== ACSLMemoryPredicateAnalyzer Tests ===" << std::endl;
    std::cout << "Phase 6: Advanced Memory Predicates (v1.23.0)" << std::endl;
    std::cout << std::endl;

    // Run all tests
    test_AllocablePrecondition();
    test_FreeablePrecondition();
    test_BlockLengthPostcondition();
    test_BaseAddressComputation();
    test_PointerArithmeticSafety();
    test_CustomAllocator();
    test_PartialAllocation();
    test_ReallocTracking();
    test_DoubleFreeDetection();
    test_UseAfterFreeDetection();
    test_FreshMemoryAllocation();
    test_NoMemoryPredicates();

    // Summary
    std::cout << std::endl;
    std::cout << "=== Test Summary ===" << std::endl;
    std::cout << "Passed: " << tests_passed << std::endl;
    std::cout << "Failed: " << tests_failed << std::endl;

    return tests_failed > 0 ? 1 : 0;
}

// tests/gtest/ACSLMemoryPredicateAnalyzerTest_GTest.cpp
// Unit tests for ACSL Memory Predicate Analyzer (Phase 6, v1.23.0)
// Migrated to Google Test framework
//
// Advanced memory reasoning predicates
// Epic #193: ACSL Annotation Generation for Transpiled Code
// Phase 6: Memory Predicates (\allocable, \freeable, \block_length, \base_addr)

#include "../../include/ACSLMemoryPredicateAnalyzer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>
#include <vector>

using namespace clang;
using namespace std;

// Store AST units to prevent premature destruction
// FIX: Heap-use-after-free bug - keeps ASTUnits alive until program exit
static vector<unique_ptr<ASTUnit>> persistentASTs;

// Test fixture for ACSL Memory Predicate Analyzer
class ACSLMemoryPredicateAnalyzerTest : public ::testing::Test {
protected:
    ACSLMemoryPredicateAnalyzer analyzer;

    // Helper: Parse C++ code and return FunctionDecl
    FunctionDecl* parseFunctionDecl(const string& code, const string& funcName) {
        unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
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

    void SetUp() override {
        analyzer = ACSLMemoryPredicateAnalyzer();
    }
};

// Test 1: AllocablePrecondition - malloc/new requires
TEST_F(ACSLMemoryPredicateAnalyzerTest, AllocablePrecondition) {
    string code = R"(
        #include <cstdlib>
        void* allocate(size_t size) {
            return malloc(size);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "allocate");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("\\allocable"), string::npos)
        << "Should generate \\allocable precondition";
    EXPECT_NE(contract.find("size"), string::npos)
        << "Should reference size parameter";
}

// Test 2: FreeablePrecondition - free/delete requires
TEST_F(ACSLMemoryPredicateAnalyzerTest, FreeablePrecondition) {
    string code = R"(
        #include <cstdlib>
        void deallocate(void* ptr) {
            free(ptr);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "deallocate");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("\\freeable(ptr)"), string::npos)
        << "Should generate \\freeable precondition";
    EXPECT_NE(contract.find("ensures !\\valid(ptr)"), string::npos)
        << "Should ensure pointer is no longer valid after free";
}

// Test 3: BlockLengthPostcondition - Allocation size tracking
TEST_F(ACSLMemoryPredicateAnalyzerTest, BlockLengthPostcondition) {
    string code = R"(
        #include <cstdlib>
        void* allocate(size_t size) {
            return malloc(size);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "allocate");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("\\block_length(\\result)"), string::npos)
        << "Should generate \\block_length for allocation";
    EXPECT_NE(contract.find("== size"), string::npos)
        << "Block length should equal size parameter";
}

// Test 4: BaseAddressComputation - Base pointer reasoning
TEST_F(ACSLMemoryPredicateAnalyzerTest, BaseAddressComputation) {
    string code = R"(
        void* get_base(void* ptr) {
            return (void*)((unsigned long)ptr & ~0xFUL);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "get_base");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("\\base_addr"), string::npos)
        << "Should use \\base_addr for base pointer";
    EXPECT_NE(contract.find("\\result"), string::npos)
        << "Should reference result in postcondition";
}

// Test 5: PointerArithmeticSafety - Offset within bounds
TEST_F(ACSLMemoryPredicateAnalyzerTest, PointerArithmeticSafety) {
    string code = R"(
        void* offset_pointer(void* ptr, size_t offset) {
            return (char*)ptr + offset;
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "offset_pointer");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("offset < \\block_length(ptr)"), string::npos)
        << "Should verify offset is within block length";
    EXPECT_NE(contract.find("\\valid(\\result)"), string::npos)
        << "Result should be valid";
}

// Test 6: CustomAllocator - Pool/arena allocators
TEST_F(ACSLMemoryPredicateAnalyzerTest, CustomAllocator) {
    string code = R"(
        class MemoryPool {
            void* allocate(size_t size);
        };
        void* MemoryPool::allocate(size_t size) {
            return nullptr; // simplified
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "allocate");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("\\allocable"), string::npos)
        << "Custom allocator should have \\allocable";
    EXPECT_NE(contract.find("\\fresh(\\result"), string::npos)
        << "Should ensure fresh memory";
}

// Test 7: PartialAllocation - Struct member allocation
TEST_F(ACSLMemoryPredicateAnalyzerTest, PartialAllocation) {
    string code = R"(
        struct Data {
            void* buffer;
        };
        void allocate_member(Data* data, size_t size) {
            data->buffer = malloc(size);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "allocate_member");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("\\valid(data)"), string::npos)
        << "Struct pointer should be valid";
    EXPECT_NE(contract.find("\\fresh"), string::npos)
        << "Member allocation should be fresh";
}

// Test 8: ReallocTracking - Reallocation size update
TEST_F(ACSLMemoryPredicateAnalyzerTest, ReallocTracking) {
    string code = R"(
        #include <cstdlib>
        void* resize(void* ptr, size_t old_size, size_t new_size) {
            return realloc(ptr, new_size);
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "resize");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("\\freeable(ptr)"), string::npos)
        << "Realloc requires freeable pointer";
    EXPECT_NE(contract.find("\\block_length(\\result) == new_size"), string::npos)
        << "New block should have new size";
}

// Test 9: DoubleFreeDetection - Freeable only once
TEST_F(ACSLMemoryPredicateAnalyzerTest, DoubleFreeDetection) {
    string code = R"(
        #include <cstdlib>
        void safe_free(void** ptr) {
            if (ptr && *ptr) {
                free(*ptr);
                *ptr = nullptr;
            }
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "safe_free");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("\\freeable"), string::npos)
        << "Should check freeable before free";
    EXPECT_NE(contract.find("!\\valid"), string::npos)
        << "After free, pointer should not be valid";
}

// Test 10: UseAfterFreeDetection - Not valid after free
TEST_F(ACSLMemoryPredicateAnalyzerTest, UseAfterFreeDetection) {
    string code = R"(
        #include <cstdlib>
        void release(void* ptr) {
            free(ptr);
            // ptr should not be dereferenced here
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "release");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("requires \\freeable(ptr)"), string::npos)
        << "Should require freeable";
    EXPECT_NE(contract.find("ensures !\\valid(ptr)"), string::npos)
        << "Should ensure not valid after free";
}

// Test 11: FreshMemoryAllocation - Memory allocation freshness
TEST_F(ACSLMemoryPredicateAnalyzerTest, FreshMemoryAllocation) {
    string code = R"(
        #include <cstdlib>
        void* create_buffer(size_t size) {
            void* buf = malloc(size);
            return buf;
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "create_buffer");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_NE(contract.find("\\fresh(\\result, size)"), string::npos)
        << "Allocated memory should be fresh";
    EXPECT_NE(contract.find("\\valid(\\result"), string::npos)
        << "Result should be valid or null";
}

// Test 12: NoMemoryPredicates - Non-memory function
TEST_F(ACSLMemoryPredicateAnalyzerTest, NoMemoryPredicates) {
    string code = R"(
        int add(int a, int b) {
            return a + b;
        }
    )";

    FunctionDecl* func = parseFunctionDecl(code, "add");
    ASSERT_NE(func, nullptr) << "Failed to parse function";

    string contract = analyzer.generateMemoryPredicates(func);

    EXPECT_EQ(contract.find("\\allocable"), string::npos)
        << "Non-memory function should not have allocable";
    EXPECT_EQ(contract.find("\\freeable"), string::npos)
        << "Non-memory function should not have freeable";
    EXPECT_EQ(contract.find("\\block_length"), string::npos)
        << "Non-memory function should not have block_length";
}

// Main function for standalone execution
int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}

// TDD Tests for ACSLMemoryPredicateAnalyzer - Phase 6, v1.23.0
// Advanced memory reasoning predicates
//
// Epic #193: ACSL Annotation Generation for Transpiled Code
// Phase 6: Memory Predicates (\allocable, \freeable, \block_length, \base_addr)

#include <gtest/gtest.h>
#include "ACSLMemoryPredicateAnalyzer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <string>
#include <memory>
#include <vector>
#include <cstdlib>
#include <cstdlib>
#include <cstdlib>
#include <cstdlib>
#include <cstdlib>
#include <cstdlib>
#include <cstdlib>

using namespace clang;

// Global storage for AST units to keep them alive
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

// Test fixture
class ACSLMemoryPredicateAnalyzerTest : public ::testing::Test {
protected:
};

TEST_F(ACSLMemoryPredicateAnalyzerTest, AllocablePrecondition) {
    std::string code = R"(
            #include <cstdlib>
            void* allocate(size_t size) {
                return malloc(size);
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "allocate");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("\\allocable"), std::string::npos) << "Should generate \\allocable precondition";
        EXPECT_NE((contract).find("size"), std::string::npos) << "Should reference size parameter";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, FreeablePrecondition) {
    std::string code = R"(
            #include <cstdlib>
            void deallocate(void* ptr) {
                free(ptr);
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "deallocate");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("\\freeable(ptr)"), std::string::npos) << "Should generate \\freeable precondition";
        EXPECT_NE((contract).find("ensures !\\valid(ptr)"), std::string::npos) << "Should ensure pointer is no longer valid after free";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, BlockLengthPostcondition) {
    std::string code = R"(
            #include <cstdlib>
            void* allocate(size_t size) {
                return malloc(size);
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "allocate");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("\\block_length(\\result)"), std::string::npos) << "Should generate \\block_length for allocation";
        EXPECT_NE((contract).find("== size"), std::string::npos) << "Block length should equal size parameter";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, BaseAddressComputation) {
    std::string code = R"(
            void* get_base(void* ptr) {
                return (void*)((unsigned long)ptr & ~0xFUL);
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "get_base");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("\\base_addr"), std::string::npos) << "Should use \\base_addr for base pointer";
        EXPECT_NE((contract).find("\\result"), std::string::npos) << "Should reference result in postcondition";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, PointerArithmeticSafety) {
    std::string code = R"(
            void* offset_pointer(void* ptr, size_t offset) {
                return (char*)ptr + offset;
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "offset_pointer");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("offset < \\block_length(ptr)"), std::string::npos) << "Should verify offset is within block length";
        EXPECT_NE((contract).find("\\valid(\\result)"), std::string::npos) << "Result should be valid";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, CustomAllocator) {
    std::string code = R"(
            class MemoryPool {
                void* allocate(size_t size);
            };
            void* MemoryPool::allocate(size_t size) {
                return nullptr; // simplified
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "allocate");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("\\allocable"), std::string::npos) << "Custom allocator should have \\allocable";
        EXPECT_NE((contract).find("\\fresh(\\result"), std::string::npos) << "Should ensure fresh memory";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, PartialAllocation) {
    std::string code = R"(
            struct Data {
                void* buffer;
            };
            void allocate_member(Data* data, size_t size) {
                data->buffer = malloc(size);
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "allocate_member");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("\\valid(data)"), std::string::npos) << "Struct pointer should be valid";
        EXPECT_NE((contract).find("\\fresh"), std::string::npos) << "Member allocation should be fresh";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, ReallocTracking) {
    std::string code = R"(
            #include <cstdlib>
            void* resize(void* ptr, size_t old_size, size_t new_size) {
                return realloc(ptr, new_size);
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "resize");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("\\freeable(ptr)"), std::string::npos) << "Realloc requires freeable pointer";
        EXPECT_NE((contract).find("\\block_length(\\result) == new_size"), std::string::npos) << "New block should have new size";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, DoubleFreeDetection) {
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
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("\\freeable"), std::string::npos) << "Should check freeable before free";
        EXPECT_NE((contract).find("!\\valid"), std::string::npos) << "After free, pointer should not be valid";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, UseAfterFreeDetection) {
    std::string code = R"(
            #include <cstdlib>
            void release(void* ptr) {
                free(ptr);
                // ptr should not be dereferenced here
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "release");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("requires \\freeable(ptr)"), std::string::npos) << "Should require freeable";
        EXPECT_NE((contract).find("ensures !\\valid(ptr)"), std::string::npos) << "Should ensure not valid after free";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, FreshMemoryAllocation) {
    std::string code = R"(
            #include <cstdlib>
            void* create_buffer(size_t size) {
                void* buf = malloc(size);
                return buf;
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "create_buffer");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_NE((contract).find("\\fresh(\\result"), std::string::npos) << "Allocated memory should be fresh";
        EXPECT_NE((contract).find("\\valid(\\result"), std::string::npos) << "Result should be valid or null";
}

TEST_F(ACSLMemoryPredicateAnalyzerTest, NoMemoryPredicates) {
    std::string code = R"(
            int add(int a, int b) {
                return a + b;
            }
        )";

        FunctionDecl* func = parseFunctionDecl(code, "add");
        ASSERT_TRUE(func != nullptr) << "Failed to parse function";

        ACSLMemoryPredicateAnalyzer analyzer;
        std::string contract = analyzer.generateMemoryPredicates(func);

        EXPECT_EQ((contract).find("\\allocable"), std::string::npos) << "Non-memory function should not have allocable";
        EXPECT_EQ((contract).find("\\freeable"), std::string::npos) << "Non-memory function should not have freeable";
        EXPECT_EQ((contract).find("\\block_length"), std::string::npos) << "Non-memory function should not have block_length";
}

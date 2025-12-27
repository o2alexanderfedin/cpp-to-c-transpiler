/**
 * @file PointersIntegrationTest.cpp
 * @brief Integration tests for pointers, references, and pointer operations
 *
 * Tests Phase 42 features working together with Phase 1-3 features:
 * - Pointer types and declarations
 * - Address-of and dereference operators
 * - Pointer arithmetic
 * - C++ references transformed to C pointers
 * - Null pointer handling
 * - Integration with control flow and arrays
 */

#include "handlers/FunctionHandler.h"
#include "handlers/VariableHandler.h"
#include "handlers/ExpressionHandler.h"
#include "handlers/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class PointersIntegrationTest
 * @brief Test fixture for Phase 42 integration testing
 */
class PointersIntegrationTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    std::unique_ptr<FunctionHandler> funcHandler;
    std::unique_ptr<VariableHandler> varHandler;
    std::unique_ptr<ExpressionHandler> exprHandler;
    std::unique_ptr<StatementHandler> stmtHandler;

    void SetUp() override {
        // Create real AST contexts
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr);
        ASSERT_NE(cAST, nullptr);

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Create all handlers
        funcHandler = std::make_unique<FunctionHandler>();
        varHandler = std::make_unique<VariableHandler>();
        exprHandler = std::make_unique<ExpressionHandler>();
        stmtHandler = std::make_unique<StatementHandler>();
    }

    void TearDown() override {
        stmtHandler.reset();
        exprHandler.reset();
        varHandler.reset();
        funcHandler.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Helper to translate a function by name
     */
    clang::FunctionDecl* translateFunction(const std::string& code, const std::string& funcName) {
        auto testAST = clang::tooling::buildASTFromCode(code);
        if (!testAST) return nullptr;

        clang::FunctionDecl* cppFunc = nullptr;
        for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
                if (func->getNameAsString() == funcName) {
                    cppFunc = func;
                    break;
                }
            }
        }

        if (!cppFunc) return nullptr;

        return llvm::dyn_cast<clang::FunctionDecl>(
            funcHandler->handleDecl(cppFunc, *context)
        );
    }
};

// ============================================================================
// Pointer Parameters Integration Tests (4 tests)
// ============================================================================

TEST_F(PointersIntegrationTest, FunctionWithPointerParameter) {
    // Test: Function taking pointer parameter
    std::string code = R"(
        void increment(int* ptr) {
            *ptr = *ptr + 1;
        }
    )";

    auto* cFunc = translateFunction(code, "increment");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "increment");
    EXPECT_EQ(cFunc->getNumParams(), 1);
}

TEST_F(PointersIntegrationTest, FunctionWithMultiplePointerParams) {
    // Test: Function with multiple pointer parameters
    std::string code = R"(
        void swap(int* a, int* b) {
            int temp = *a;
            *a = *b;
            *b = temp;
        }
    )";

    auto* cFunc = translateFunction(code, "swap");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

TEST_F(PointersIntegrationTest, PointerParameterWithArrayAccess) {
    // Test: Pointer parameter used with array-style access
    std::string code = R"(
        int sum_array(int* arr, int size) {
            int total = 0;
            for (int i = 0; i < size; i++) {
                total += arr[i];
            }
            return total;
        }
    )";

    auto* cFunc = translateFunction(code, "sum_array");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

TEST_F(PointersIntegrationTest, ConstPointerParameter) {
    // Test: Const pointer parameter
    std::string code = R"(
        int read_value(const int* ptr) {
            return *ptr;
        }
    )";

    auto* cFunc = translateFunction(code, "read_value");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 1);
}

// ============================================================================
// Pointer Return Types Integration Tests (3 tests)
// ============================================================================

TEST_F(PointersIntegrationTest, FunctionReturningPointer) {
    // Test: Function returning pointer
    std::string code = R"(
        int global_value = 42;

        int* get_pointer() {
            return &global_value;
        }
    )";

    auto* cFunc = translateFunction(code, "get_pointer");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "get_pointer");
}

TEST_F(PointersIntegrationTest, FindFirstOccurrence) {
    // Test: Function returning pointer to found element
    std::string code = R"(
        int* find_value(int* arr, int size, int target) {
            for (int i = 0; i < size; i++) {
                if (arr[i] == target) {
                    return &arr[i];
                }
            }
            return 0;
        }
    )";

    auto* cFunc = translateFunction(code, "find_value");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 3);
}

TEST_F(PointersIntegrationTest, ConditionalPointerReturn) {
    // Test: Conditional return of different pointers
    std::string code = R"(
        int* select_pointer(int* a, int* b, int condition) {
            if (condition > 0) {
                return a;
            } else {
                return b;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "select_pointer");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Pointer Arithmetic in Loops Integration Tests (4 tests)
// ============================================================================

TEST_F(PointersIntegrationTest, PointerIterationLoop) {
    // Test: Loop using pointer increment
    std::string code = R"(
        int sum_with_pointer(int* arr, int size) {
            int sum = 0;
            int* end = arr + size;
            for (int* ptr = arr; ptr < end; ptr++) {
                sum += *ptr;
            }
            return sum;
        }
    )";

    auto* cFunc = translateFunction(code, "sum_with_pointer");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, PointerArithmeticInWhileLoop) {
    // Test: While loop with pointer arithmetic
    std::string code = R"(
        int count_until_zero(int* arr) {
            int count = 0;
            while (*arr != 0) {
                count++;
                arr++;
            }
            return count;
        }
    )";

    auto* cFunc = translateFunction(code, "count_until_zero");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, PointerOffsetCalculation) {
    // Test: Pointer arithmetic with offset
    std::string code = R"(
        int get_element_at_offset(int* base, int offset) {
            return *(base + offset);
        }
    )";

    auto* cFunc = translateFunction(code, "get_element_at_offset");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, TwoPointerTechnique) {
    // Test: Two pointer technique
    std::string code = R"(
        int find_pair_sum(int* arr, int size, int target) {
            int* left = arr;
            int* right = arr + size - 1;

            while (left < right) {
                int sum = *left + *right;
                if (sum == target) {
                    return 1;
                } else if (sum < target) {
                    left++;
                } else {
                    right--;
                }
            }
            return 0;
        }
    )";

    auto* cFunc = translateFunction(code, "find_pair_sum");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Reference Parameters Integration Tests (3 tests)
// ============================================================================

TEST_F(PointersIntegrationTest, ReferenceParameterModification) {
    // Test: Function modifying value through reference
    std::string code = R"(
        void modify_by_reference(int& x) {
            x = x * 2;
        }
    )";

    auto* cFunc = translateFunction(code, "modify_by_reference");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 1);
}

TEST_F(PointersIntegrationTest, ConstReferenceParameter) {
    // Test: Const reference parameter
    std::string code = R"(
        int use_const_reference(const int& value) {
            return value + 10;
        }
    )";

    auto* cFunc = translateFunction(code, "use_const_reference");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, MultipleReferenceParameters) {
    // Test: Multiple reference parameters
    std::string code = R"(
        void compute(int& result, const int& a, const int& b) {
            result = a + b;
        }
    )";

    auto* cFunc = translateFunction(code, "compute");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 3);
}

// ============================================================================
// Null Pointer Integration Tests (3 tests)
// ============================================================================

TEST_F(PointersIntegrationTest, NullPointerCheck) {
    // Test: Null pointer check
    std::string code = R"(
        int safe_dereference(int* ptr) {
            if (ptr != 0) {
                return *ptr;
            }
            return -1;
        }
    )";

    auto* cFunc = translateFunction(code, "safe_dereference");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, NullPointerInitialization) {
    // Test: Initialize pointer to null
    std::string code = R"(
        int* get_null_pointer() {
            int* ptr = 0;
            return ptr;
        }
    )";

    auto* cFunc = translateFunction(code, "get_null_pointer");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, ConditionalNullReturn) {
    // Test: Return null on condition
    std::string code = R"(
        int* find_positive(int* arr, int size) {
            for (int i = 0; i < size; i++) {
                if (arr[i] > 0) {
                    return &arr[i];
                }
            }
            return 0;
        }
    )";

    auto* cFunc = translateFunction(code, "find_positive");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Multi-level Pointers Integration Tests (2 tests)
// ============================================================================

TEST_F(PointersIntegrationTest, PointerToPointer) {
    // Test: Pointer to pointer
    std::string code = R"(
        void modify_pointer(int** pp, int* new_value) {
            *pp = new_value;
        }
    )";

    auto* cFunc = translateFunction(code, "modify_pointer");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

TEST_F(PointersIntegrationTest, DoubleIndirection) {
    // Test: Double indirection access
    std::string code = R"(
        int get_value_indirect(int** pp) {
            return **pp;
        }
    )";

    auto* cFunc = translateFunction(code, "get_value_indirect");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Complex Integration Tests (7 tests)
// ============================================================================

TEST_F(PointersIntegrationTest, ArrayReversalWithPointers) {
    // Test: Array reversal using two pointers
    std::string code = R"(
        void reverse_array(int* arr, int size) {
            int* left = arr;
            int* right = arr + size - 1;

            while (left < right) {
                int temp = *left;
                *left = *right;
                *right = temp;
                left++;
                right--;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "reverse_array");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, PointerBasedCopy) {
    // Test: Copy array using pointers
    std::string code = R"(
        void copy_array(int* dest, const int* src, int size) {
            int* dest_end = dest + size;
            while (dest < dest_end) {
                *dest = *src;
                dest++;
                src++;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "copy_array");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, FindMaxWithPointer) {
    // Test: Find max element, return pointer
    std::string code = R"(
        int* find_max(int* arr, int size) {
            if (size <= 0) {
                return 0;
            }

            int* max_ptr = arr;
            for (int i = 1; i < size; i++) {
                if (arr[i] > *max_ptr) {
                    max_ptr = &arr[i];
                }
            }
            return max_ptr;
        }
    )";

    auto* cFunc = translateFunction(code, "find_max");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, PointerWithGlobalVariable) {
    // Test: Pointer to global variable
    std::string code = R"(
        int global_counter = 0;

        void increment_global() {
            int* ptr = &global_counter;
            *ptr = *ptr + 1;
        }
    )";

    auto* cFunc = translateFunction(code, "increment_global");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, PointerArrayNavigation) {
    // Test: Navigate through array with pointer arithmetic
    std::string code = R"(
        int sum_range(int* start, int* end) {
            int sum = 0;
            while (start < end) {
                sum += *start;
                start++;
            }
            return sum;
        }
    )";

    auto* cFunc = translateFunction(code, "sum_range");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, PartitionWithPointers) {
    // Test: Array partition using pointers
    std::string code = R"(
        int partition(int* arr, int size, int pivot) {
            int* left = arr;
            int* right = arr + size - 1;

            while (left <= right) {
                while (left <= right && *left < pivot) {
                    left++;
                }
                while (left <= right && *right >= pivot) {
                    right--;
                }
                if (left < right) {
                    int temp = *left;
                    *left = *right;
                    *right = temp;
                }
            }
            return left - arr;
        }
    )";

    auto* cFunc = translateFunction(code, "partition");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(PointersIntegrationTest, ComplexPointerExpressions) {
    // Test: Complex pointer expressions with mixed operations
    std::string code = R"(
        int calculate(int* arr, int index, int offset) {
            int* base = arr + index;
            int value1 = *(base + offset);
            int value2 = *(base - offset);
            return value1 + value2;
        }
    )";

    auto* cFunc = translateFunction(code, "calculate");
    ASSERT_NE(cFunc, nullptr);
}

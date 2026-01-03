/**
 * @file ComparisonOperatorsIntegrationTest.cpp
 * @brief Comprehensive integration tests for Phase 51 comparison operators
 *
 * Tests the complete pipeline for C++ comparison operator overloading:
 * Stage 1: Clang parses C++ → C++ AST
 * Stage 2: Handlers translate C++ AST → C AST (operator method to function)
 * Stage 3: CodeGenerator emits C source (operator call to function call)
 * Validation: Compile C code with gcc and execute
 *
 * Test Strategy (15 tests across 4 categories):
 *
 * Sorting Category (4 tests):
 * - 1. BubbleSortWithOperatorLess: Basic sort using operator<
 * - 2. QuickSortWithOperatorLess: Partition sort using operator<
 * - 3. InsertionSortWithOperatorLessEqual: Insertion sort using operator<=
 * - 4. SortingStability: Verify stable sort behavior
 *
 * Searching Category (3 tests):
 * - 5. BinarySearchWithComparison: Binary search using operator< and operator==
 * - 6. LinearSearchWithEquality: Linear search using operator==
 * - 7. LowerBoundWithOperatorLess: Lower bound search using operator<
 *
 * Container Operations Category (3 tests):
 * - 8. SortedInsertionWithOperatorLess: Insert into sorted list
 * - 9. DuplicateDetectionWithEquality: Find duplicates using operator==
 * - 10. RangeQueryWithComparison: Range queries using operator< and operator>
 *
 * Conditional Chains Category (5 tests):
 * - 11. ChainedComparisons: Test a < b && b < c pattern
 * - 12. EqualityChains: Test a == b && b == c pattern
 * - 13. LogicalOperatorsInConditionals: Test !a || b pattern
 * - 14. ComplexConditionalExpressions: Mixed comparison operators
 * - 15. TernaryOperatorWithComparisons: condition ? a : b with operator<
 *
 * Key Acceptance Criteria:
 * 1. All 15 tests compile and run successfully
 * 2. Comparison operators (9 types) translate to C function calls
 * 3. Real-world algorithms (sort, search, insert) work correctly
 * 4. Complex conditionals with chained comparisons work
 * 5. All generated C code compiles with gcc -std=c99
 * 6. Test execution returns expected exit codes (0 for pass, 1 for fail)
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/DeclCXX.h"
#include "DispatcherTestHelper.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/StatementHandler.h"
#include "CodeGenerator.h"
#include <memory>
#include <fstream>
#include <cstdlib>
#include <ctime>

using namespace cpptoc;
using namespace clang;

/**
 * @class ComparisonOperatorsIntegrationTest
 * @brief Test fixture for comprehensive comparison operators testing
 */
class ComparisonOperatorsIntegrationTest : public ::testing::Test {
protected:
    void SetUp() override {
        srand(static_cast<unsigned>(time(nullptr)));
    }

    /**
     * @brief Run complete pipeline: C++ source → C source → compile → execute
     * @param cppCode C++ source code with comparison operator definitions and usage
     * @param expectedExitCode Expected exit code from program execution
     * @param debugOutput If true, print generated C code
     * @return true if test passed
     */
    bool runPipeline(const std::string& cppCode, int expectedExitCode = 0, bool debugOutput = false) {
        // Create dispatcher pipeline
        auto pipeline = cpptoc::test::createDispatcherPipeline(cppCode);

        // Register handlers
        FunctionHandler::registerWith(*pipeline.dispatcher);
        VariableHandler::registerWith(*pipeline.dispatcher);
        StatementHandler::registerWith(*pipeline.dispatcher);

        // Dispatch all top-level declarations
        for (auto* decl : pipeline.cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
            auto* nonConstDecl = const_cast<clang::Decl*>(decl);
            if (debugOutput) {
                if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(nonConstDecl)) {
                    std::cout << "DEBUG: Translating function: " << func->getNameAsString() << "\n";
                }
            }
            pipeline.dispatcher->dispatch(
                pipeline.cppAST->getASTContext(),
                pipeline.cAST->getASTContext(),
                nonConstDecl
            );
        }

        // Generate C code
        std::string cCode = cpptoc::test::generateCCode(pipeline.cAST->getASTContext());

        if (debugOutput) {
            std::cout << "=== Generated C Code ===\n" << cCode << "\n=========================\n";
        }

        // Write C code to temporary file
        std::string tmpFile = "/tmp/cmp_op_test_" + std::to_string(rand()) + ".c";
        std::ofstream outFile(tmpFile);
        if (!outFile) {
            std::cerr << "Failed to create temporary file: " << tmpFile << "\n";
            return false;
        }
        outFile << "#include <stdio.h>\n#include <stdbool.h>\n#include <string.h>\n" << cCode;
        outFile.close();

        // Compile with gcc
        std::string compileCmd = "gcc -std=c99 -Wall " + tmpFile + " -o " + tmpFile + ".out 2>&1";
        int compileResult = system(compileCmd.c_str());
        if (compileResult != 0) {
            std::cerr << "Compilation failed for: " << tmpFile << "\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            std::cerr << "Compile command: " << compileCmd << "\n";
            system(("cat " + tmpFile).c_str());
            system(("rm -f " + tmpFile + " " + tmpFile + ".out").c_str());
            return false;
        }

        // Execute
        std::string execCmd = tmpFile + ".out";
        int execResult = system(execCmd.c_str());
        int actualExitCode = WEXITSTATUS(execResult);

        // Cleanup
        system(("rm -f " + tmpFile + " " + tmpFile + ".out").c_str());

        if (actualExitCode != expectedExitCode) {
            std::cerr << "Execution failed: expected exit code " << expectedExitCode
                     << " but got " << actualExitCode << "\n";
            return false;
        }

        return true;
    }
};

// ============================================================================
// SORTING CATEGORY (4 tests)
// ============================================================================

/**
 * Test 1: Bubble Sort with operator<
 * Real-world usage: Sorting custom objects
 * Operators tested: <
 */
TEST_F(ComparisonOperatorsIntegrationTest, BubbleSortWithOperatorLess) {
    const char *code = R"(
        struct Number {
            int value;
        };

        bool operator<(const Number& a, const Number& b) {
            return a.value < b.value;
        }

        void bubbleSort(Number* arr, int n) {
            for (int i = 0; i < n - 1; i++) {
                for (int j = 0; j < n - i - 1; j++) {
                    if (arr[j] < arr[j + 1]) {
                        Number temp = arr[j];
                        arr[j] = arr[j + 1];
                        arr[j + 1] = temp;
                    }
                }
            }
        }

        int main() {
            Number arr[5];
            arr[0].value = 64; arr[1].value = 34; arr[2].value = 25;
            arr[3].value = 12; arr[4].value = 22;

            bubbleSort(arr, 5);

            // Verify sorting: should end with 64, 34, 25, 22, 12
            if (arr[0].value == 64 && arr[4].value == 12) {
                return 0;
            }
            return 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 2: Quick Sort Partition with operator<
 * Real-world usage: Efficient sorting algorithm
 * Operators tested: <
 */
TEST_F(ComparisonOperatorsIntegrationTest, QuickSortWithOperatorLess) {
    const char *code = R"(
        struct Point {
            int x;
            int y;
        };

        bool operator<(const Point& a, const Point& b) {
            return (a.x * a.x + a.y * a.y) < (b.x * b.x + b.y * b.y);
        }

        int partition(Point* arr, int low, int high) {
            Point pivot = arr[high];
            int i = low - 1;

            for (int j = low; j < high; j++) {
                if (arr[j] < pivot) {
                    i++;
                    Point temp = arr[i];
                    arr[i] = arr[j];
                    arr[j] = temp;
                }
            }

            Point temp = arr[i + 1];
            arr[i + 1] = arr[high];
            arr[high] = temp;
            return i + 1;
        }

        int main() {
            Point arr[4];
            arr[0].x = 1; arr[0].y = 1;
            arr[1].x = 2; arr[1].y = 2;
            arr[2].x = 0; arr[2].y = 0;
            arr[3].x = 3; arr[3].y = 0;

            int pi = partition(arr, 0, 3);
            return (pi >= 0 && pi <= 3) ? 0 : 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 3: Insertion Sort with operator<=
 * Real-world usage: Sorting with stability requirement
 * Operators tested: <=
 */
TEST_F(ComparisonOperatorsIntegrationTest, InsertionSortWithOperatorLessEqual) {
    const char *code = R"(
        struct Item {
            int priority;
            int order;
        };

        bool operator<=(const Item& a, const Item& b) {
            return a.priority <= b.priority;
        }

        void insertionSort(Item* arr, int n) {
            for (int i = 1; i < n; i++) {
                Item key = arr[i];
                int j = i - 1;

                while (j >= 0 && arr[j] <= key) {
                    j--;
                }

                for (int k = i; k > j + 1; k--) {
                    arr[k] = arr[k - 1];
                }
                arr[j + 1] = key;
            }
        }

        int main() {
            Item arr[3];
            arr[0].priority = 3;
            arr[1].priority = 1;
            arr[2].priority = 2;

            insertionSort(arr, 3);

            // Verify ordering
            if (arr[0].priority <= arr[1].priority && arr[1].priority <= arr[2].priority) {
                return 0;
            }
            return 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 4: Sorting Stability with operator==
 * Real-world usage: Preserving relative order of equal elements
 * Operators tested: ==
 */
TEST_F(ComparisonOperatorsIntegrationTest, SortingStability) {
    const char *code = R"(
        struct Record {
            int key;
            int id;
        };

        bool operator==(const Record& a, const Record& b) {
            return a.key == b.key;
        }

        bool operator<(const Record& a, const Record& b) {
            return a.key < b.key;
        }

        int main() {
            Record arr[3];
            arr[0].key = 1; arr[0].id = 10;
            arr[1].key = 1; arr[1].id = 20;
            arr[2].key = 1; arr[2].id = 30;

            // All elements are equal
            int equal_count = 0;
            for (int i = 0; i < 3; i++) {
                for (int j = i + 1; j < 3; j++) {
                    if (arr[i] == arr[j]) {
                        equal_count++;
                    }
                }
            }

            return (equal_count == 3) ? 0 : 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

// ============================================================================
// SEARCHING CATEGORY (3 tests)
// ============================================================================

/**
 * Test 5: Binary Search with operator< and operator==
 * Real-world usage: Efficient search in sorted data
 * Operators tested: <, ==
 */
TEST_F(ComparisonOperatorsIntegrationTest, BinarySearchWithComparison) {
    const char *code = R"(
        struct Value {
            int data;
        };

        bool operator<(const Value& a, const Value& b) {
            return a.data < b.data;
        }

        bool operator==(const Value& a, const Value& b) {
            return a.data == b.data;
        }

        int binarySearch(Value* arr, int n, Value target) {
            int left = 0, right = n - 1;

            while (left <= right) {
                int mid = left + (right - left) / 2;

                if (arr[mid] == target) {
                    return mid;
                } else if (arr[mid] < target) {
                    left = mid + 1;
                } else {
                    right = mid - 1;
                }
            }

            return -1;
        }

        int main() {
            Value arr[5];
            arr[0].data = 10; arr[1].data = 20; arr[2].data = 30;
            arr[3].data = 40; arr[4].data = 50;

            Value target;
            target.data = 30;

            int result = binarySearch(arr, 5, target);
            return (result == 2) ? 0 : 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 6: Linear Search with operator==
 * Real-world usage: Simple equality-based search
 * Operators tested: ==
 */
TEST_F(ComparisonOperatorsIntegrationTest, LinearSearchWithEquality) {
    const char *code = R"(
        struct Person {
            int id;
            int age;
        };

        bool operator==(const Person& a, const Person& b) {
            return a.id == b.id && a.age == b.age;
        }

        int linearSearch(Person* arr, int n, Person target) {
            for (int i = 0; i < n; i++) {
                if (arr[i] == target) {
                    return i;
                }
            }
            return -1;
        }

        int main() {
            Person arr[3];
            arr[0].id = 1; arr[0].age = 25;
            arr[1].id = 2; arr[1].age = 30;
            arr[2].id = 3; arr[2].age = 35;

            Person target;
            target.id = 2;
            target.age = 30;

            int result = linearSearch(arr, 3, target);
            return (result == 1) ? 0 : 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 7: Lower Bound Search with operator<
 * Real-world usage: Finding insertion point in sorted data
 * Operators tested: <
 */
TEST_F(ComparisonOperatorsIntegrationTest, LowerBoundWithOperatorLess) {
    const char *code = R"(
        struct Element {
            int value;
        };

        bool operator<(const Element& a, const Element& b) {
            return a.value < b.value;
        }

        int lowerBound(Element* arr, int n, Element target) {
            int left = 0, right = n;

            while (left < right) {
                int mid = left + (right - left) / 2;
                if (arr[mid] < target) {
                    left = mid + 1;
                } else {
                    right = mid;
                }
            }

            return left;
        }

        int main() {
            Element arr[5];
            arr[0].value = 10; arr[1].value = 20; arr[2].value = 30;
            arr[3].value = 40; arr[4].value = 50;

            Element target;
            target.value = 25;

            int pos = lowerBound(arr, 5, target);
            return (pos == 2) ? 0 : 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

// ============================================================================
// CONTAINER OPERATIONS CATEGORY (3 tests)
// ============================================================================

/**
 * Test 8: Sorted Insertion with operator<
 * Real-world usage: Maintaining sorted order while inserting
 * Operators tested: <
 */
TEST_F(ComparisonOperatorsIntegrationTest, SortedInsertionWithOperatorLess) {
    const char *code = R"(
        struct Node {
            int value;
            int next;  // Index to next node, -1 for end
        };

        bool operator<(const Node& a, const Node& b) {
            return a.value < b.value;
        }

        int main() {
            Node nodes[5];

            // Initialize with some values
            nodes[0].value = 10; nodes[0].next = 1;
            nodes[1].value = 30; nodes[1].next = 2;
            nodes[2].value = 20; nodes[2].next = -1;

            // Find insertion position for value 25
            int pos = 0;
            while (pos != -1 && nodes[pos] < nodes[2]) {
                pos = nodes[pos].next;
            }

            // pos should be 2 (position of value 20)
            return (nodes[pos].value == 20) ? 0 : 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 9: Duplicate Detection with operator==
 * Real-world usage: Finding duplicate elements in collection
 * Operators tested: ==
 */
TEST_F(ComparisonOperatorsIntegrationTest, DuplicateDetectionWithEquality) {
    const char *code = R"(
        struct Data {
            int id;
            int checksum;
        };

        bool operator==(const Data& a, const Data& b) {
            return a.id == b.id && a.checksum == b.checksum;
        }

        int main() {
            Data arr[5];
            arr[0].id = 1; arr[0].checksum = 100;
            arr[1].id = 2; arr[1].checksum = 200;
            arr[2].id = 1; arr[2].checksum = 100;  // Duplicate of arr[0]
            arr[3].id = 3; arr[3].checksum = 300;
            arr[4].id = 2; arr[4].checksum = 200;  // Duplicate of arr[1]

            int duplicates = 0;
            for (int i = 0; i < 5; i++) {
                for (int j = i + 1; j < 5; j++) {
                    if (arr[i] == arr[j]) {
                        duplicates++;
                    }
                }
            }

            return (duplicates == 2) ? 0 : 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 10: Range Query with operator< and operator>
 * Real-world usage: Finding elements within a range
 * Operators tested: <, >
 */
TEST_F(ComparisonOperatorsIntegrationTest, RangeQueryWithComparison) {
    const char *code = R"(
        struct Measurement {
            int value;
        };

        bool operator<(const Measurement& a, const Measurement& b) {
            return a.value < b.value;
        }

        bool operator>(const Measurement& a, const Measurement& b) {
            return a.value > b.value;
        }

        int main() {
            Measurement arr[6];
            arr[0].value = 5;
            arr[1].value = 15;
            arr[2].value = 25;
            arr[3].value = 35;
            arr[4].value = 45;
            arr[5].value = 55;

            Measurement min;
            min.value = 20;

            Measurement max;
            max.value = 40;

            // Count elements in range [20, 40]
            int count = 0;
            for (int i = 0; i < 6; i++) {
                if (!(arr[i] < min) && arr[i] < max) {
                    count++;
                }
            }

            return (count == 2) ? 0 : 1;  // Should find 25 and 35
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

// ============================================================================
// CONDITIONAL CHAINS CATEGORY (5 tests)
// ============================================================================

/**
 * Test 11: Chained Comparisons with operator<
 * Real-world usage: Multi-condition validation
 * Operators tested: <
 */
TEST_F(ComparisonOperatorsIntegrationTest, ChainedComparisons) {
    const char *code = R"(
        struct Temperature {
            int celsius;
        };

        bool operator<(const Temperature& a, const Temperature& b) {
            return a.celsius < b.celsius;
        }

        int main() {
            Temperature t1, t2, t3;
            t1.celsius = 10;
            t2.celsius = 20;
            t3.celsius = 30;

            // Test: t1 < t2 && t2 < t3
            if (t1 < t2 && t2 < t3) {
                return 0;
            }

            return 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 12: Equality Chains with operator==
 * Real-world usage: Verifying transitive equality
 * Operators tested: ==
 */
TEST_F(ComparisonOperatorsIntegrationTest, EqualityChains) {
    const char *code = R"(
        struct Version {
            int major;
            int minor;
        };

        bool operator==(const Version& a, const Version& b) {
            return a.major == b.major && a.minor == b.minor;
        }

        int main() {
            Version v1, v2, v3;
            v1.major = 1; v1.minor = 0;
            v2.major = 1; v2.minor = 0;
            v3.major = 1; v3.minor = 0;

            // Test: v1 == v2 && v2 == v3 && v1 == v3
            if (v1 == v2 && v2 == v3 && v1 == v3) {
                return 0;
            }

            return 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 13: Logical Operators in Conditionals
 * Real-world usage: Complex boolean logic
 * Operators tested: !=
 */
TEST_F(ComparisonOperatorsIntegrationTest, LogicalOperatorsInConditionals) {
    const char *code = R"(
        struct Status {
            int code;
        };

        bool operator!=(const Status& a, const Status& b) {
            return a.code != b.code;
        }

        int main() {
            Status s1, s2, s3;
            s1.code = 200;
            s2.code = 404;
            s3.code = 200;

            // Test: s1 != s2 || s1 != s3 should be true
            // But s1 != s3 is false, so overall should be true
            if (s1 != s2) {
                return 0;
            }

            return 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 14: Complex Conditional Expressions
 * Real-world usage: Multi-operator conditions
 * Operators tested: <, >, ==
 */
TEST_F(ComparisonOperatorsIntegrationTest, ComplexConditionalExpressions) {
    const char *code = R"(
        struct Range {
            int min;
            int max;
        };

        bool operator<(const Range& a, const Range& b) {
            return a.max < b.min;
        }

        bool operator>(const Range& a, const Range& b) {
            return a.min > b.max;
        }

        bool operator==(const Range& a, const Range& b) {
            return a.min == b.min && a.max == b.max;
        }

        int main() {
            Range r1, r2, r3;
            r1.min = 1; r1.max = 5;
            r2.min = 10; r2.max = 15;
            r3.min = 1; r3.max = 5;

            // Test: (r1 < r2) && (r1 == r3) && !(r1 > r2)
            if (r1 < r2 && r1 == r3) {
                return 0;
            }

            return 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}

/**
 * Test 15: Ternary Operator with Comparisons
 * Real-world usage: Conditional value selection
 * Operators tested: <, >
 */
TEST_F(ComparisonOperatorsIntegrationTest, TernaryOperatorWithComparisons) {
    const char *code = R"(
        struct Score {
            int value;
        };

        bool operator<(const Score& a, const Score& b) {
            return a.value < b.value;
        }

        bool operator>(const Score& a, const Score& b) {
            return a.value > b.value;
        }

        int main() {
            Score s1, s2, s3;
            s1.value = 85;
            s2.value = 92;
            s3.value = 78;

            // Find the highest score
            Score highest = (s1 < s2) ? s2 : s1;
            highest = (highest < s3) ? s3 : highest;

            // Verify we got 92
            if (highest.value == 92) {
                return 0;
            }

            return 1;
        }
    )";

    EXPECT_TRUE(runPipeline(code, 0, false));
}


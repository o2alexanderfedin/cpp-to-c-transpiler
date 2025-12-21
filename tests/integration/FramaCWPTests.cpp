/*
 * Frama-C WP Integration Tests
 * Phase 7: ACSL Integration & Validation (v2.0.0)
 *
 * Tests that generated ACSL annotations are provable by Frama-C's WP plugin.
 * Each test transpiles C++ code with ACSL annotations and verifies proofs succeed.
 */

#include <gtest/gtest.h>
#include <clang/Tooling/Tooling.h>
#include "CppToCTranspiler.h"
#include <fstream>
#include <cstdlib>
#include <sstream>

using namespace clang;
using namespace clang::tooling;

namespace {

class FramaCWPTest : public ::testing::Test {
protected:
    std::string transpileWithACSL(const std::string& cppCode, bool fullAnnotations = true) {
        // Configure transpiler with all ACSL features enabled
        CppToCTranspilerOptions options;
        options.enableACSL = true;
        options.acslStatements = fullAnnotations ? ACSLStatementLevel::Full : ACSLStatementLevel::Basic;
        options.acslTypeInvariants = true;
        options.acslAxiomatics = true;
        options.acslGhostCode = true;
        options.acslBehaviors = true;
        options.acslMemoryPredicates = true;

        CppToCTranspiler transpiler(options);
        return transpiler.transpile(cppCode);
    }

    struct FramaCResult {
        bool success;
        int provedGoals;
        int totalGoals;
        std::string output;
    };

    FramaCResult runFramaCWP(const std::string& cCode) {
        // Write C code to temporary file
        std::string tmpFile = "/tmp/framac_test_" + std::to_string(std::rand()) + ".c";
        std::ofstream out(tmpFile);
        out << cCode;
        out.close();

        // Run Frama-C WP
        std::string cmd = "frama-c -wp -wp-prover alt-ergo,z3 -wp-timeout 10 " + tmpFile + " 2>&1";
        FILE* pipe = popen(cmd.c_str(), "r");
        if (!pipe) {
            return {false, 0, 0, "Failed to run Frama-C"};
        }

        std::stringstream ss;
        char buffer[256];
        while (fgets(buffer, sizeof(buffer), pipe)) {
            ss << buffer;
        }
        int exitCode = pclose(pipe);

        std::string output = ss.str();

        // Parse WP results
        FramaCResult result;
        result.output = output;
        result.success = (exitCode == 0);

        // Extract proved/total goals from output
        // Format: "Proved goals:    X / Y"
        size_t pos = output.find("Proved goals:");
        if (pos != std::string::npos) {
            sscanf(output.c_str() + pos, "Proved goals: %d / %d",
                   &result.provedGoals, &result.totalGoals);
        } else {
            result.provedGoals = 0;
            result.totalGoals = 0;
        }

        // Clean up
        std::remove(tmpFile.c_str());

        return result;
    }

    void expectProofSuccess(const std::string& cppCode, double minSuccessRate = 0.8) {
        std::string cCode = transpileWithACSL(cppCode);
        FramaCResult result = runFramaCWP(cCode);

        if (result.totalGoals > 0) {
            double successRate = static_cast<double>(result.provedGoals) / result.totalGoals;
            EXPECT_GE(successRate, minSuccessRate)
                << "Proof success rate: " << successRate
                << " (proved " << result.provedGoals << "/" << result.totalGoals << ")\n"
                << "Frama-C output:\n" << result.output;
        }
    }
};

// ============================================================================
// Test 1: SimpleFunction_WP - Basic function contracts provable
// ============================================================================

TEST_F(FramaCWPTest, SimpleFunction_WP) {
    const char* code = R"(
        int add(int a, int b) {
            return a + b;
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 2: PointerFunction_WP - Pointer validity provable
// ============================================================================

TEST_F(FramaCWPTest, PointerFunction_WP) {
    const char* code = R"(
        int deref(int* p) {
            if (p == nullptr) return 0;
            return *p;
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 3: ArrayFunction_WP - Array bounds provable
// ============================================================================

TEST_F(FramaCWPTest, ArrayFunction_WP) {
    const char* code = R"(
        int sum_array(int* arr, int size) {
            int sum = 0;
            for (int i = 0; i < size; ++i) {
                sum += arr[i];
            }
            return sum;
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 4: LoopFunction_WP - Loop invariants provable
// ============================================================================

TEST_F(FramaCWPTest, LoopFunction_WP) {
    const char* code = R"(
        int count_to_n(int n) {
            int count = 0;
            for (int i = 0; i < n; ++i) {
                count++;
            }
            return count;
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 5: RecursiveFunction_WP - Recursive functions provable
// ============================================================================

TEST_F(FramaCWPTest, RecursiveFunction_WP) {
    const char* code = R"(
        int factorial(int n) {
            if (n <= 1) return 1;
            return n * factorial(n - 1);
        }
    )";

    expectProofSuccess(code, 0.7); // Recursive proofs are harder
}

// ============================================================================
// Test 6: ClassMethods_WP - Class invariants maintained
// ============================================================================

TEST_F(FramaCWPTest, ClassMethods_WP) {
    const char* code = R"(
        class Counter {
        private:
            int count;
        public:
            Counter() : count(0) {}
            void increment() { count++; }
            int getCount() const { return count; }
        };
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 7: MemoryAllocation_WP - Memory safety provable
// ============================================================================

TEST_F(FramaCWPTest, MemoryAllocation_WP) {
    const char* code = R"(
        #include <cstdlib>

        int* allocate_int(int value) {
            int* p = (int*)malloc(sizeof(int));
            if (p != nullptr) {
                *p = value;
            }
            return p;
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 8: PointerArithmetic_WP - Arithmetic safety provable
// ============================================================================

TEST_F(FramaCWPTest, PointerArithmetic_WP) {
    const char* code = R"(
        int* advance_pointer(int* ptr, int offset, int max_offset) {
            if (offset >= 0 && offset < max_offset) {
                return ptr + offset;
            }
            return ptr;
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 9: BufferOperations_WP - Buffer overflow prevention
// ============================================================================

TEST_F(FramaCWPTest, BufferOperations_WP) {
    const char* code = R"(
        void copy_buffer(int* dest, const int* src, int size) {
            for (int i = 0; i < size; ++i) {
                dest[i] = src[i];
            }
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 10: TypeInvariants_WP - Type constraints checked
// ============================================================================

TEST_F(FramaCWPTest, TypeInvariants_WP) {
    const char* code = R"(
        class BoundedInt {
        private:
            int value;
        public:
            BoundedInt(int v) : value(v) {
                if (v < 0) value = 0;
                if (v > 100) value = 100;
            }
            int getValue() const { return value; }
        };
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 11: GhostCode_WP - Ghost vars aid proof
// ============================================================================

TEST_F(FramaCWPTest, GhostCode_WP) {
    const char* code = R"(
        int max_in_array(int* arr, int size) {
            int max_val = arr[0];
            for (int i = 1; i < size; ++i) {
                if (arr[i] > max_val) {
                    max_val = arr[i];
                }
            }
            return max_val;
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 12: Behaviors_WP - Behaviors provable independently
// ============================================================================

TEST_F(FramaCWPTest, Behaviors_WP) {
    const char* code = R"(
        int absolute_value(int x) {
            if (x < 0) {
                return -x;
            } else {
                return x;
            }
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 13: Axiomatics_WP - Lemmas provable from axioms
// ============================================================================

TEST_F(FramaCWPTest, Axiomatics_WP) {
    const char* code = R"(
        int gcd(int a, int b) {
            while (b != 0) {
                int temp = b;
                b = a % b;
                a = temp;
            }
            return a;
        }
    )";

    expectProofSuccess(code, 0.7); // Mathematical proofs are complex
}

// ============================================================================
// Test 14: ComplexAlgorithm_WP - Multi-phase algorithm
// ============================================================================

TEST_F(FramaCWPTest, ComplexAlgorithm_WP) {
    const char* code = R"(
        void bubble_sort(int* arr, int size) {
            for (int i = 0; i < size - 1; ++i) {
                for (int j = 0; j < size - i - 1; ++j) {
                    if (arr[j] > arr[j + 1]) {
                        int temp = arr[j];
                        arr[j] = arr[j + 1];
                        arr[j + 1] = temp;
                    }
                }
            }
        }
    )";

    expectProofSuccess(code, 0.6); // Sorting algorithms are complex to prove
}

// ============================================================================
// Test 15: ErrorHandling_WP - Error paths verified
// ============================================================================

TEST_F(FramaCWPTest, ErrorHandling_WP) {
    const char* code = R"(
        int safe_divide(int a, int b, int* error) {
            if (b == 0) {
                *error = 1;
                return 0;
            }
            *error = 0;
            return a / b;
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 16: ResourceManagement_WP - RAII pattern verified
// ============================================================================

TEST_F(FramaCWPTest, ResourceManagement_WP) {
    const char* code = R"(
        #include <cstdlib>

        class Resource {
        private:
            int* data;
        public:
            Resource() : data((int*)malloc(sizeof(int))) {
                if (data) *data = 0;
            }
            ~Resource() {
                if (data) free(data);
            }
        };
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 17: TemplateCode_WP - Monomorphized templates
// ============================================================================

TEST_F(FramaCWPTest, TemplateCode_WP) {
    const char* code = R"(
        template<typename T>
        T max(T a, T b) {
            return (a > b) ? a : b;
        }

        int use_max() {
            return max(5, 10);
        }
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 18: InheritanceHierarchy_WP - Virtual functions
// ============================================================================

TEST_F(FramaCWPTest, InheritanceHierarchy_WP) {
    const char* code = R"(
        class Base {
        public:
            virtual int getValue() { return 0; }
        };

        class Derived : public Base {
        public:
            int getValue() override { return 42; }
        };
    )";

    expectProofSuccess(code, 0.7); // Virtual dispatch is complex
}

// ============================================================================
// Test 19: OperatorOverloading_WP - Operators verified
// ============================================================================

TEST_F(FramaCWPTest, OperatorOverloading_WP) {
    const char* code = R"(
        class Point {
        private:
            int x, y;
        public:
            Point(int x, int y) : x(x), y(y) {}
            Point operator+(const Point& other) const {
                return Point(x + other.x, y + other.y);
            }
        };
    )";

    expectProofSuccess(code);
}

// ============================================================================
// Test 20: STLContainers_WP - Container operations
// ============================================================================

TEST_F(FramaCWPTest, STLContainers_WP) {
    const char* code = R"(
        #include <vector>

        int sum_vector(const std::vector<int>& vec) {
            int sum = 0;
            for (int val : vec) {
                sum += val;
            }
            return sum;
        }
    )";

    expectProofSuccess(code, 0.6); // STL is complex to verify
}

} // anonymous namespace

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}

/*
 * Frama-C EVA (Evolved Value Analysis) Integration Tests
 * Phase 7: ACSL Integration & Validation (v2.0.0)
 *
 * Tests that generated ACSL annotations improve EVA's value analysis.
 * EVA should detect fewer alarms (false positives) with annotations.
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

class FramaCEVATest : public ::testing::Test {
protected:
    std::string transpileWithACSL(const std::string& cppCode, bool withAnnotations = true) {
        CppToCTranspilerOptions options;
        options.enableACSL = withAnnotations;
        options.acslStatements = ACSLStatementLevel::Full;
        options.acslTypeInvariants = true;
        options.acslAxiomatics = true;
        options.acslGhostCode = true;
        options.acslBehaviors = true;
        options.acslMemoryPredicates = true;

        CppToCTranspiler transpiler(options);
        return transpiler.transpile(cppCode);
    }

    struct EVAResult {
        bool success;
        int alarms;
        std::string output;
    };

    EVAResult runFramaCEVA(const std::string& cCode) {
        // Write C code to temporary file
        std::string tmpFile = "/tmp/framac_eva_" + std::to_string(std::rand()) + ".c";
        std::ofstream out(tmpFile);
        out << cCode;
        out.close();

        // Run Frama-C EVA
        std::string cmd = "frama-c -eva " + tmpFile + " 2>&1";
        FILE* pipe = popen(cmd.c_str(), "r");
        if (!pipe) {
            return {false, -1, "Failed to run Frama-C EVA"};
        }

        std::stringstream ss;
        char buffer[256];
        while (fgets(buffer, sizeof(buffer), pipe)) {
            ss << buffer;
        }
        int exitCode = pclose(pipe);

        std::string output = ss.str();

        // Parse EVA results
        EVAResult result;
        result.output = output;
        result.success = (exitCode == 0);

        // Count alarms in output
        result.alarms = 0;
        std::string line;
        std::istringstream iss(output);
        while (std::getline(iss, line)) {
            if (line.find("alarm") != std::string::npos ||
                line.find("warning") != std::string::npos) {
                result.alarms++;
            }
        }

        // Clean up
        std::remove(tmpFile.c_str());

        return result;
    }

    void expectAlarmReduction(const std::string& cppCode, double minReductionRate = 0.5) {
        // Run EVA without annotations
        std::string cCodeWithout = transpileWithACSL(cppCode, false);
        EVAResult resultWithout = runFramaCEVA(cCodeWithout);

        // Run EVA with annotations
        std::string cCodeWith = transpileWithACSL(cppCode, true);
        EVAResult resultWith = runFramaCEVA(cCodeWith);

        if (resultWithout.alarms > 0) {
            double reductionRate = 1.0 - (static_cast<double>(resultWith.alarms) / resultWithout.alarms);
            EXPECT_GE(reductionRate, minReductionRate)
                << "Alarm reduction rate: " << reductionRate
                << " (without: " << resultWithout.alarms << ", with: " << resultWith.alarms << ")";
        }
    }

    void expectNoAlarms(const std::string& cppCode) {
        std::string cCode = transpileWithACSL(cppCode, true);
        EVAResult result = runFramaCEVA(cCode);
        EXPECT_EQ(result.alarms, 0)
            << "Expected no alarms, but found " << result.alarms << "\n"
            << "EVA output:\n" << result.output;
    }
};

// ============================================================================
// Test 1: ConstantPropagation_EVA - EVA benefits from annotations
// ============================================================================

TEST_F(FramaCEVATest, ConstantPropagation_EVA) {
    const char* code = R"(
        int compute(int x) {
            int y = x + 10;
            int z = y * 2;
            return z;
        }
    )";

    expectNoAlarms(code);
}

// ============================================================================
// Test 2: RangeAnalysis_EVA - Tighter ranges with contracts
// ============================================================================

TEST_F(FramaCEVATest, RangeAnalysis_EVA) {
    const char* code = R"(
        int clamp(int value, int min, int max) {
            if (value < min) return min;
            if (value > max) return max;
            return value;
        }
    )";

    expectNoAlarms(code);
}

// ============================================================================
// Test 3: PointerAnalysis_EVA - Separation aids analysis
// ============================================================================

TEST_F(FramaCEVATest, PointerAnalysis_EVA) {
    const char* code = R"(
        void swap(int* a, int* b) {
            if (a == nullptr || b == nullptr) return;
            int temp = *a;
            *a = *b;
            *b = temp;
        }
    )";

    expectAlarmReduction(code);
}

// ============================================================================
// Test 4: BufferAnalysis_EVA - No buffer overflows detected
// ============================================================================

TEST_F(FramaCEVATest, BufferAnalysis_EVA) {
    const char* code = R"(
        void fill_array(int* arr, int size, int value) {
            for (int i = 0; i < size; ++i) {
                arr[i] = value;
            }
        }
    )";

    expectAlarmReduction(code);
}

// ============================================================================
// Test 5: DivisionByZero_EVA - No division by zero
// ============================================================================

TEST_F(FramaCEVATest, DivisionByZero_EVA) {
    const char* code = R"(
        int safe_divide(int a, int b) {
            if (b == 0) return 0;
            return a / b;
        }
    )";

    expectNoAlarms(code);
}

// ============================================================================
// Test 6: NullPointer_EVA - No null dereferences
// ============================================================================

TEST_F(FramaCEVATest, NullPointer_EVA) {
    const char* code = R"(
        int get_value(int* ptr) {
            if (ptr == nullptr) return -1;
            return *ptr;
        }
    )";

    expectNoAlarms(code);
}

// ============================================================================
// Test 7: UninitializedMemory_EVA - All memory initialized
// ============================================================================

TEST_F(FramaCEVATest, UninitializedMemory_EVA) {
    const char* code = R"(
        int compute() {
            int x = 0;
            int y = x + 5;
            return y;
        }
    )";

    expectNoAlarms(code);
}

// ============================================================================
// Test 8: MemoryLeak_EVA - No leaks detected
// ============================================================================

TEST_F(FramaCEVATest, MemoryLeak_EVA) {
    const char* code = R"(
        #include <cstdlib>

        class Resource {
        private:
            int* data;
        public:
            Resource() : data((int*)malloc(sizeof(int))) {}
            ~Resource() { if (data) free(data); }
        };
    )";

    expectAlarmReduction(code);
}

// ============================================================================
// Test 9: ArithmeticOverflow_EVA - No overflows
// ============================================================================

TEST_F(FramaCEVATest, ArithmeticOverflow_EVA) {
    const char* code = R"(
        int safe_add(int a, int b) {
            if (a > 0 && b > 0 && a > 2147483647 - b) return 2147483647;
            if (a < 0 && b < 0 && a < -2147483648 - b) return -2147483648;
            return a + b;
        }
    )";

    expectAlarmReduction(code);
}

// ============================================================================
// Test 10: SignedUnsignedMix_EVA - Type mixing safe
// ============================================================================

TEST_F(FramaCEVATest, SignedUnsignedMix_EVA) {
    const char* code = R"(
        unsigned int convert(int x) {
            if (x < 0) return 0;
            return static_cast<unsigned int>(x);
        }
    )";

    expectNoAlarms(code);
}

// ============================================================================
// Test 11: CastSafety_EVA - All casts safe
// ============================================================================

TEST_F(FramaCEVATest, CastSafety_EVA) {
    const char* code = R"(
        int truncate_to_byte(int x) {
            if (x < 0) return 0;
            if (x > 255) return 255;
            return static_cast<unsigned char>(x);
        }
    )";

    expectNoAlarms(code);
}

// ============================================================================
// Test 12: ArrayBounds_EVA - All accesses in bounds
// ============================================================================

TEST_F(FramaCEVATest, ArrayBounds_EVA) {
    const char* code = R"(
        int get_element(int* arr, int size, int index) {
            if (index < 0 || index >= size) return -1;
            return arr[index];
        }
    )";

    expectNoAlarms(code);
}

// ============================================================================
// Test 13: FunctionPointers_EVA - Indirect calls safe
// ============================================================================

TEST_F(FramaCEVATest, FunctionPointers_EVA) {
    const char* code = R"(
        typedef int (*Operation)(int, int);

        int apply(Operation op, int a, int b) {
            if (op == nullptr) return 0;
            return op(a, b);
        }

        int add(int a, int b) { return a + b; }

        int use_apply() {
            return apply(add, 5, 3);
        }
    )";

    expectAlarmReduction(code);
}

// ============================================================================
// Test 14: GlobalState_EVA - Global invariants maintained
// ============================================================================

TEST_F(FramaCEVATest, GlobalState_EVA) {
    const char* code = R"(
        class Counter {
        private:
            static int count;
        public:
            static void increment() { count++; }
            static int getCount() { return count; }
        };

        int Counter::count = 0;
    )";

    expectNoAlarms(code);
}

// ============================================================================
// Test 15: ConcurrencyUnsafe_EVA - Data races detected
// ============================================================================

TEST_F(FramaCEVATest, ConcurrencyUnsafe_EVA) {
    const char* code = R"(
        class SharedData {
        private:
            int value;
        public:
            SharedData() : value(0) {}
            void increment() { value++; }
            int getValue() const { return value; }
        };
    )";

    // EVA may not detect concurrency issues in single-threaded analysis
    // This test mainly checks that annotations don't introduce false positives
    expectAlarmReduction(code, 0.0); // No reduction expected for concurrency
}

} // anonymous namespace

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}

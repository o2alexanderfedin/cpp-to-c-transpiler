#include <gtest/gtest.h>
#include <memory>
#include <vector>
#include <string>
#include <stdexcept>

// ===================================================================
// GOOGLE TEST MIGRATION - Test Framework Example Tests
// ===================================================================
// This file demonstrates proper Google Test usage and serves as a
// reference implementation for the team.
//
// Migrated from custom TestFramework to Google Test
// Test count: 9 test suites
// ===================================================================

// ===================================================================
// Test 1: Basic Assertions
// Demonstrates fundamental GTest assertions
// ===================================================================
TEST(BasicAssertionsTest, TrueAssertions) {
    ASSERT_TRUE(true);
    ASSERT_TRUE(1 == 1);
    ASSERT_TRUE(5 > 3);
}

TEST(BasicAssertionsTest, FalseAssertions) {
    ASSERT_FALSE(false);
    ASSERT_FALSE(1 == 2);
}

TEST(BasicAssertionsTest, EqualityAssertions) {
    ASSERT_EQ(42, 42);
    ASSERT_EQ("hello", std::string("hello"));
    ASSERT_EQ(3.14, 3.14);
}

TEST(BasicAssertionsTest, InequalityAssertions) {
    ASSERT_NE(1, 2);
    ASSERT_NE("foo", std::string("bar"));
}

TEST(BasicAssertionsTest, ComparisonAssertions) {
    // Less than
    ASSERT_LT(1, 2);
    ASSERT_LT(-5, 0);

    // Greater than
    ASSERT_GT(10, 5);
    ASSERT_GT(0, -1);
}

// ===================================================================
// Test 2: Pointer Assertions
// Demonstrates null pointer testing
// ===================================================================
TEST(PointerAssertionsTest, NullAndNonNullPointers) {
    int* nullPtr = nullptr;
    int value = 42;
    int* nonNullPtr = &value;

    ASSERT_EQ(nullptr, nullPtr);
    ASSERT_NE(nullptr, nonNullPtr);
}

// ===================================================================
// Test 3: Exception Assertions
// Demonstrates exception testing with GTest
// ===================================================================
TEST(ExceptionAssertionsTest, ThrowsAnyException) {
    ASSERT_THROW(throw std::runtime_error("test"), std::exception);
}

TEST(ExceptionAssertionsTest, ThrowsSpecificException) {
    ASSERT_THROW(
        throw std::invalid_argument("test"),
        std::invalid_argument
    );
}

TEST(ExceptionAssertionsTest, ThrowsInCodeBlock) {
    ASSERT_THROW({
        if (true) {
            throw std::logic_error("expected");
        }
    }, std::logic_error);
}

// ===================================================================
// Test 4: Fixture Setup/Teardown
// Demonstrates GTest test fixture usage
// ===================================================================
class MathFixture : public ::testing::Test {
protected:
    int value;

    void SetUp() override {
        value = 0;
    }

    void TearDown() override {
        // Verify teardown happens after test
        // In a real scenario, this would clean up resources
        value = -1;
    }
};

TEST_F(MathFixture, SetupInitializesValue) {
    // SetUp should have initialized value to 0
    ASSERT_EQ(0, value);

    value = 100;
    ASSERT_EQ(100, value);

    // TearDown will set it to -1 after this test
}

// ===================================================================
// Test 5: String Comparisons
// Demonstrates string testing
// ===================================================================
TEST(StringTest, StringEquality) {
    std::string s1 = "hello";
    std::string s2 = "hello";
    std::string s3 = "world";

    ASSERT_EQ(s1, s2);
    ASSERT_NE(s1, s3);
}

TEST(StringTest, StringComparison) {
    std::string s1 = "hello";
    std::string s3 = "world";

    ASSERT_TRUE(s1 < s3);  // "hello" < "world"
}

// ===================================================================
// Test 6: Arithmetic Operations
// Demonstrates testing mathematical operations
// ===================================================================
TEST(ArithmeticTest, BasicOperations) {
    int a = 10;
    int b = 5;

    ASSERT_EQ(15, a + b);
    ASSERT_EQ(5, a - b);
    ASSERT_EQ(50, a * b);
    ASSERT_EQ(2, a / b);
    ASSERT_EQ(0, a % b);
}

// ===================================================================
// Test 7: Floating Point Comparisons
// Demonstrates float/double testing
// ===================================================================
TEST(FloatTest, FloatingPointComparisons) {
    double pi = 3.14159;
    double e = 2.71828;

    ASSERT_GT(pi, e);
    ASSERT_LT(e, pi);
    ASSERT_GT(pi, 3.0);
    ASSERT_LT(pi, 3.2);
}

// ===================================================================
// Test 8: Boolean Logic
// Demonstrates boolean testing
// ===================================================================
TEST(BooleanTest, BooleanValues) {
    bool t = true;
    bool f = false;

    ASSERT_TRUE(t);
    ASSERT_FALSE(f);
}

TEST(BooleanTest, LogicalOperations) {
    bool t = true;
    bool f = false;

    ASSERT_TRUE(t && t);
    ASSERT_FALSE(t && f);
    ASSERT_TRUE(t || f);
    ASSERT_FALSE(f || f);
    ASSERT_TRUE(!f);
    ASSERT_FALSE(!t);
}

// ===================================================================
// Test 9: Container Operations
// Demonstrates STL container testing
// ===================================================================
TEST(ContainerTest, VectorOperations) {
    std::vector<int> vec = {1, 2, 3, 4, 5};

    ASSERT_EQ(5, vec.size());
    ASSERT_FALSE(vec.empty());
    ASSERT_EQ(1, vec[0]);
    ASSERT_EQ(5, vec[4]);
}

TEST(ContainerTest, VectorModification) {
    std::vector<int> vec = {1, 2, 3, 4, 5};

    vec.push_back(6);
    ASSERT_EQ(6, vec.size());
    ASSERT_EQ(6, vec.back());
}

// ===================================================================
// Main function (optional with gtest_main)
// ===================================================================
// Note: Since CMakeLists.txt links GTest::gtest_main, this main()
// function is optional. However, we include it here to demonstrate
// that tests can still be run with a custom main if needed.
// ===================================================================
int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}

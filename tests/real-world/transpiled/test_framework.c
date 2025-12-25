// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/test-framework/tests/test_framework.cpp
// Implementation file

#include "test_framework.h"

int TEST(int, int) {
        <recovery-expr>(ASSERT_TRUE, true);
        <recovery-expr>(ASSERT_TRUE, 1 == 1);
        <recovery-expr>(ASSERT_TRUE, 5 > 3);
}

int TEST(int, int) {
        <recovery-expr>(ASSERT_FALSE, false);
        <recovery-expr>(ASSERT_FALSE, 1 == 2);
}

int TEST(int, int) {
        <recovery-expr>(ASSERT_EQ, 42, 42);
        <recovery-expr>(ASSERT_EQ, "hello");
        <recovery-expr>(ASSERT_EQ, 3.1400000000000001, 3.1400000000000001);
}

int TEST(int, int) {
        <recovery-expr>(ASSERT_NE, 1, 2);
        <recovery-expr>(ASSERT_NE, "foo");
}

int TEST(int, int) {
        <recovery-expr>(ASSERT_LT, 1, 2);
        <recovery-expr>(ASSERT_LT, -5, 0);
        <recovery-expr>(ASSERT_GT, 10, 5);
        <recovery-expr>(ASSERT_GT, 0, -1);
}

int TEST(int, int) {
        int *nullPtr = nullptr;
        int value = 42;
        int *nonNullPtr = &value;
        <recovery-expr>(ASSERT_EQ, nullptr, nullPtr);
        <recovery-expr>(ASSERT_NE, nullptr, nonNullPtr);
}

int TEST(int, int) {
        <recovery-expr>(ASSERT_THROW);
}

int TEST(int, int) {
        <recovery-expr>(ASSERT_THROW);
}

int TEST(int, int) {
        <recovery-expr>(ASSERT_THROW);
}

class MathFixture {
protected:
        int value;
        void SetUp() {
                this->value = 0;
        }
        void TearDown() {
                this->value = -1;
        }
};
int TEST_F(MathFixture, int) {
        <recovery-expr>(ASSERT_EQ, 0);
        <recovery-expr>(ASSERT_EQ, 100);
}

int TEST(int, int) {
        int s1 = <recovery-expr>("hello");
        int s2 = <recovery-expr>("hello");
        int s3 = <recovery-expr>("world");
        ASSERT_EQ(<recovery-expr>(), <recovery-expr>());
        ASSERT_NE(<recovery-expr>(), <recovery-expr>());
}

int TEST(int, int) {
        int s1 = <recovery-expr>("hello");
        int s3 = <recovery-expr>("world");
        ASSERT_TRUE(<recovery-expr>() < <recovery-expr>());
}

int TEST(int, int) {
        int a = 10;
        int b = 5;
        <recovery-expr>(ASSERT_EQ, 15, a + b);
        <recovery-expr>(ASSERT_EQ, 5, a - b);
        <recovery-expr>(ASSERT_EQ, 50, a * b);
        <recovery-expr>(ASSERT_EQ, 2, a / b);
        <recovery-expr>(ASSERT_EQ, 0, a % b);
}

int TEST(int, int) {
        double pi = 3.1415899999999999;
        double e = 2.71828;
        <recovery-expr>(ASSERT_GT, pi, e);
        <recovery-expr>(ASSERT_LT, e, pi);
        <recovery-expr>(ASSERT_GT, pi, 3.);
        <recovery-expr>(ASSERT_LT, pi, 3.2000000000000002);
}

int TEST(int, int) {
        bool t = true;
        bool f = false;
        <recovery-expr>(ASSERT_TRUE, t);
        <recovery-expr>(ASSERT_FALSE, f);
}

int TEST(int, int) {
        bool t = true;
        bool f = false;
        <recovery-expr>(ASSERT_TRUE, t && t);
        <recovery-expr>(ASSERT_FALSE, t && f);
        <recovery-expr>(ASSERT_TRUE, t || f);
        <recovery-expr>(ASSERT_FALSE, f || f);
        <recovery-expr>(ASSERT_TRUE, !f);
        <recovery-expr>(ASSERT_FALSE, !t);
}

int TEST(int, int) {
        <recovery-expr>(ASSERT_EQ, 5);
        <recovery-expr>(ASSERT_FALSE);
        <recovery-expr>(ASSERT_EQ, 1);
        <recovery-expr>(ASSERT_EQ, 5);
}

int TEST(int, int) {
        <recovery-expr>(ASSERT_EQ, 6);
        <recovery-expr>(ASSERT_EQ, 6);
}

int main(int argc, char **argv) {
        return <recovery-expr>(RUN_ALL_TESTS);
}

int TEST(int, int) {
        <recovery-expr>(ASSERT_TRUE, true);
        <recovery-expr>(ASSERT_TRUE, 1 == 1);
        <recovery-expr>(ASSERT_TRUE, 5 > 3);
}

int TEST_int_int(int, int) {
        <recovery-expr>(ASSERT_FALSE, false);
        <recovery-expr>(ASSERT_FALSE, 1 == 2);
}

int TEST_int_int_1(int, int) {
        <recovery-expr>(ASSERT_EQ, 42, 42);
        <recovery-expr>(ASSERT_EQ, "hello");
        <recovery-expr>(ASSERT_EQ, 3.1400000000000001, 3.1400000000000001);
}

int TEST_int_int_2(int, int) {
        <recovery-expr>(ASSERT_NE, 1, 2);
        <recovery-expr>(ASSERT_NE, "foo");
}

int TEST_int_int_3(int, int) {
        <recovery-expr>(ASSERT_LT, 1, 2);
        <recovery-expr>(ASSERT_LT, -5, 0);
        <recovery-expr>(ASSERT_GT, 10, 5);
        <recovery-expr>(ASSERT_GT, 0, -1);
}

int TEST_int_int_4(int, int) {
        int *nullPtr = nullptr;
        int value = 42;
        int *nonNullPtr = &value;
        <recovery-expr>(ASSERT_EQ, nullptr, nullPtr);
        <recovery-expr>(ASSERT_NE, nullptr, nonNullPtr);
}

int TEST_int_int_5(int, int) {
        <recovery-expr>(ASSERT_THROW);
}

int TEST_int_int_6(int, int) {
        <recovery-expr>(ASSERT_THROW);
}

int TEST_int_int_7(int, int) {
        <recovery-expr>(ASSERT_THROW);
}

struct MathFixture {
        int value;
};
void MathFixture__ctor_default(struct MathFixture *this) {
        this->value = 0;
}

void MathFixture__ctor_copy(struct MathFixture *this, const struct MathFixture *other) {
        this->value = other->value;
}

void MathFixture_SetUp(struct MathFixture *this) {
        this->value = 0;
}

void MathFixture_TearDown(struct MathFixture *this) {
        this->value = -1;
}

int TEST_F(MathFixture, int) {
        <recovery-expr>(ASSERT_EQ, 0);
        <recovery-expr>(ASSERT_EQ, 100);
}

int TEST_int_int_8(int, int) {
        int s1 = <recovery-expr>("hello");
        int s2 = <recovery-expr>("hello");
        int s3 = <recovery-expr>("world");
        ASSERT_EQ(<recovery-expr>(), <recovery-expr>());
        ASSERT_NE(<recovery-expr>(), <recovery-expr>());
}

int TEST_int_int_9(int, int) {
        int s1 = <recovery-expr>("hello");
        int s3 = <recovery-expr>("world");
        ASSERT_TRUE(<recovery-expr>() < <recovery-expr>());
}

int TEST_int_int_10(int, int) {
        int a = 10;
        int b = 5;
        <recovery-expr>(ASSERT_EQ, 15, a + b);
        <recovery-expr>(ASSERT_EQ, 5, a - b);
        <recovery-expr>(ASSERT_EQ, 50, a * b);
        <recovery-expr>(ASSERT_EQ, 2, a / b);
        <recovery-expr>(ASSERT_EQ, 0, a % b);
}

int TEST_int_int_11(int, int) {
        double pi = 3.1415899999999999;
        double e = 2.71828;
        <recovery-expr>(ASSERT_GT, pi, e);
        <recovery-expr>(ASSERT_LT, e, pi);
        <recovery-expr>(ASSERT_GT, pi, 3.);
        <recovery-expr>(ASSERT_LT, pi, 3.2000000000000002);
}

int TEST_int_int_12(int, int) {
        bool t = true;
        bool f = false;
        <recovery-expr>(ASSERT_TRUE, t);
        <recovery-expr>(ASSERT_FALSE, f);
}

int TEST_int_int_13(int, int) {
        bool t = true;
        bool f = false;
        <recovery-expr>(ASSERT_TRUE, t && t);
        <recovery-expr>(ASSERT_FALSE, t && f);
        <recovery-expr>(ASSERT_TRUE, t || f);
        <recovery-expr>(ASSERT_FALSE, f || f);
        <recovery-expr>(ASSERT_TRUE, !f);
        <recovery-expr>(ASSERT_FALSE, !t);
}

int TEST_int_int_14(int, int) {
        <recovery-expr>(ASSERT_EQ, 5);
        <recovery-expr>(ASSERT_FALSE);
        <recovery-expr>(ASSERT_EQ, 1);
        <recovery-expr>(ASSERT_EQ, 5);
}

int TEST_int_int_15(int, int) {
        <recovery-expr>(ASSERT_EQ, 6);
        <recovery-expr>(ASSERT_EQ, 6);
}

int main(int argc, char **argv) {
        return <recovery-expr>(RUN_ALL_TESTS);
}


// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/operators/OperatorOverloadingTest.cpp
// Implementation file

#include "OperatorOverloadingTest.h"

static void OperatorOverloadingTestBase__ctor_default(struct OperatorOverloadingTestBase * this) {
}

static void OperatorOverloadingTestBase__ctor_copy(struct OperatorOverloadingTestBase * this, const struct OperatorOverloadingTestBase * other) {
}

int OperatorOverloadingTestBase_buildAST_const_int_ptr(struct OperatorOverloadingTestBase * this, const char * code) {
}

static void ArithmeticOperatorTest__ctor_default(struct ArithmeticOperatorTest * this) {
}

static void ArithmeticOperatorTest__ctor_copy(struct ArithmeticOperatorTest * this, const struct ArithmeticOperatorTest * other) {
}

int TEST_F(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Vector2D {\n        public:\n            int x, y;\n            Vector2D operator+(const Vector2D& other) const;\n        };\n    ";
	auto * TU;
	int * opPlus;
}

int TEST_F_ArithmeticOperatorTest_int(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Complex {\n        public:\n            double real, imag;\n            Complex operator-(const Complex& other) const;\n        };\n    ";
	auto * TU;
	int * opMinus;
}

int TEST_F_ArithmeticOperatorTest_int_1(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Matrix {\n        public:\n            Matrix operator*(const Matrix& other) const;\n        };\n    ";
	auto * TU;
	int * opMul;
}

int TEST_F_ArithmeticOperatorTest_int_2(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Fraction {\n        public:\n            int numerator, denominator;\n            Fraction operator/(const Fraction& other) const;\n        };\n    ";
	auto * TU;
	int * opDiv;
}

int TEST_F_ArithmeticOperatorTest_int_3(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Integer {\n        public:\n            int value;\n            Integer operator%(const Integer& other) const;\n        };\n    ";
	auto * TU;
	int * opMod;
}

int TEST_F_ArithmeticOperatorTest_int_4(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Number {\n        public:\n            double value;\n            Number operator-() const;\n        };\n    ";
	auto * TU;
	int * opUnaryMinus;
}

int TEST_F_ArithmeticOperatorTest_int_5(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class SignedInt {\n        public:\n            int value;\n            SignedInt operator+() const;\n        };\n    ";
	auto * TU;
	int * opUnaryPlus;
}

int TEST_F_ArithmeticOperatorTest_int_6(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Counter {\n        public:\n            int count;\n            Counter& operator++();\n        };\n    ";
	auto * TU;
	int * opPrefixInc;
}

int TEST_F_ArithmeticOperatorTest_int_7(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Iterator {\n        public:\n            int position;\n            Iterator operator++(int);\n        };\n    ";
	auto * TU;
	int * opPostfixInc;
}

int TEST_F_ArithmeticOperatorTest_int_8(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Countdown {\n        public:\n            int value;\n            Countdown& operator--();\n        };\n    ";
	auto * TU;
	int * opPrefixDec;
}

int TEST_F_ArithmeticOperatorTest_int_9(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class ReverseIterator {\n        public:\n            int position;\n            ReverseIterator operator--(int);\n        };\n    ";
	auto * TU;
	int * opPostfixDec;
}

int TEST_F_ArithmeticOperatorTest_int_10(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Accumulator {\n        public:\n            int total;\n            Accumulator& operator+=(const Accumulator& other);\n        };\n    ";
	auto * TU;
	int * opPlusAssign;
}

int TEST_F_ArithmeticOperatorTest_int_11(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Balance {\n        public:\n            double amount;\n            Balance& operator-=(const Balance& other);\n        };\n    ";
	auto * TU;
	int * opMinusAssign;
}

int TEST_F_ArithmeticOperatorTest_int_12(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Scale {\n        public:\n            double factor;\n            Scale& operator*=(const Scale& other);\n        };\n    ";
	auto * TU;
	int * opMulAssign;
}

int TEST_F_ArithmeticOperatorTest_int_13(struct ArithmeticOperatorTest, int) {
	const char * code = "\n        class Ratio {\n        public:\n            double value;\n            Ratio& operator/=(const Ratio& other);\n        };\n    ";
	auto * TU;
	int * opDivAssign;
}

static void ComparisonOperatorTest__ctor_default(struct ComparisonOperatorTest * this) {
}

static void ComparisonOperatorTest__ctor_copy(struct ComparisonOperatorTest * this, const struct ComparisonOperatorTest * other) {
}

int TEST_F_ComparisonOperatorTest_int(struct ComparisonOperatorTest, int) {
	const char * code = "\n        class Point {\n        public:\n            int x, y;\n            bool operator==(const Point& other) const;\n        };\n    ";
	auto * TU;
	int * opEqual;
}

int TEST_F_ComparisonOperatorTest_int_1(struct ComparisonOperatorTest, int) {
	const char * code = "\n        class String {\n        public:\n            char* data;\n            bool operator!=(const String& other) const;\n        };\n    ";
	auto * TU;
	int * opNotEqual;
}

int TEST_F_ComparisonOperatorTest_int_2(struct ComparisonOperatorTest, int) {
	const char * code = "\n        class ComparableInt {\n        public:\n            int value;\n            bool operator<(const ComparableInt& other) const;\n        };\n    ";
	auto * TU;
	int * opLess;
}

int TEST_F_ComparisonOperatorTest_int_3(struct ComparisonOperatorTest, int) {
	const char * code = "\n        class Priority {\n        public:\n            int level;\n            bool operator>(const Priority& other) const;\n        };\n    ";
	auto * TU;
	int * opGreater;
}

int TEST_F_ComparisonOperatorTest_int_4(struct ComparisonOperatorTest, int) {
	const char * code = "\n        class Version {\n        public:\n            int major, minor;\n            bool operator<=(const Version& other) const;\n        };\n    ";
	auto * TU;
	int * opLessEqual;
}

int TEST_F_ComparisonOperatorTest_int_5(struct ComparisonOperatorTest, int) {
	const char * code = "\n        class Score {\n        public:\n            double points;\n            bool operator>=(const Score& other) const;\n        };\n    ";
	auto * TU;
	int * opGreaterEqual;
}

int TEST_F_ComparisonOperatorTest_int_6(struct ComparisonOperatorTest, int) {
	const char * code = "\n        class Comparable {\n        public:\n            int value;\n            bool operator==(const Comparable& other) const;\n            bool operator!=(const Comparable& other) const;\n            bool operator<(const Comparable& other) const;\n            bool operator>(const Comparable& other) const;\n        };\n    ";
	auto * TU;
	int operatorCount = 0;
}

int TEST_F_ComparisonOperatorTest_int_7(struct ComparisonOperatorTest, int) {
	const char * code = "\n        class Mixed {\n        public:\n            int value;\n            bool operator==(int other) const;\n            bool operator==(const Mixed& other) const;\n        };\n    ";
	auto * TU;
	int * opEqualInt;
	int * opEqualMixed;
}

int TEST_F_ComparisonOperatorTest_int_8(struct ComparisonOperatorTest, int) {
	const char * code = "\n        class Value {\n        public:\n            int data;\n            friend bool operator==(const Value& a, const Value& b);\n        };\n        bool operator==(const Value& a, const Value& b);\n    ";
	auto * TU;
	int * friendOp;
}

int TEST_F_ComparisonOperatorTest_int_9(struct ComparisonOperatorTest, int) {
	const char * code = "\n        class ConstTest {\n        public:\n            int value;\n            bool operator<(const ConstTest& other) const;\n        };\n    ";
	auto * TU;
	int * opLess;
	int paramType;
}

static void SubscriptCallOperatorTest__ctor_default(struct SubscriptCallOperatorTest * this) {
}

static void SubscriptCallOperatorTest__ctor_copy(struct SubscriptCallOperatorTest * this, const struct SubscriptCallOperatorTest * other) {
}

int TEST_F_SubscriptCallOperatorTest_int(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class Array {\n        public:\n            int* data;\n            int& operator[](int index);\n        };\n    ";
	auto * TU;
	int * opSubscript;
}

int TEST_F_SubscriptCallOperatorTest_int_1(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class ConstArray {\n        public:\n            int* data;\n            const int& operator[](int index) const;\n        };\n    ";
	auto * TU;
	int * opSubscript;
}

int TEST_F_SubscriptCallOperatorTest_int_2(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class StringKey {\n        public:\n            int value;\n        };\n        class Map {\n        public:\n            int& operator[](const StringKey& key);\n        };\n    ";
	auto * TU;
	int * opSubscript;
	int paramType;
}

int TEST_F_SubscriptCallOperatorTest_int_3(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class MultiArray {\n        public:\n            int& operator[](int index);\n            int& operator[](unsigned int index);\n        };\n    ";
	auto * TU;
	int subscriptOpCount = 0;
}

int TEST_F_SubscriptCallOperatorTest_int_4(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class Functor {\n        public:\n            int operator()();\n        };\n    ";
	auto * TU;
	int * opCall;
}

int TEST_F_SubscriptCallOperatorTest_int_5(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class UnaryFunction {\n        public:\n            int operator()(int x);\n        };\n    ";
	auto * TU;
	int * opCall;
}

int TEST_F_SubscriptCallOperatorTest_int_6(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class BinaryFunction {\n        public:\n            int operator()(int x, int y);\n        };\n    ";
	auto * TU;
	int * opCall;
}

int TEST_F_SubscriptCallOperatorTest_int_7(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class PolyFunction {\n        public:\n            int operator()(int x);\n            double operator()(double x);\n            int operator()(int x, int y);\n        };\n    ";
	auto * TU;
	int callOpCount = 0;
}

int TEST_F_SubscriptCallOperatorTest_int_8(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class ConstFunctor {\n        public:\n            int operator()(int x) const;\n        };\n    ";
	auto * TU;
	int * opCall;
}

int TEST_F_SubscriptCallOperatorTest_int_9(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class Lambda {\n        private:\n            int captured;\n        public:\n            Lambda(int x) : captured(x) {}\n            int operator()(int y) const { return captured + y; }\n        };\n    ";
	auto * TU;
	int * opCall;
}

int TEST_F_SubscriptCallOperatorTest_int_10(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class RefReturner {\n        public:\n            int data;\n            int& operator()();\n        };\n    ";
	auto * TU;
	int * opCall;
}

int TEST_F_SubscriptCallOperatorTest_int_11(struct SubscriptCallOperatorTest, int) {
	const char * code = "\n        class DualOperator {\n        public:\n            int& operator[](int index);\n            int operator()(int x, int y);\n        };\n    ";
	auto * TU;
	int * opSubscript;
	int * opCall;
}

static void SpecialOperatorTest__ctor_default(struct SpecialOperatorTest * this) {
}

static void SpecialOperatorTest__ctor_copy(struct SpecialOperatorTest * this, const struct SpecialOperatorTest * other) {
}

int TEST_F_SpecialOperatorTest_int(struct SpecialOperatorTest, int) {
	const char * code = "\n        class Inner {\n        public:\n            int value;\n        };\n        class SmartPointer {\n        public:\n            Inner* ptr;\n            Inner* operator->();\n        };\n    ";
	auto * TU;
	int * opArrow;
}

int TEST_F_SpecialOperatorTest_int_1(struct SpecialOperatorTest, int) {
	const char * code = "\n        class Data {\n        public:\n            int value;\n        };\n        class ConstSmartPointer {\n        public:\n            Data* ptr;\n            const Data* operator->() const;\n        };\n    ";
	auto * TU;
	int * opArrow;
}

int TEST_F_SpecialOperatorTest_int_2(struct SpecialOperatorTest, int) {
	const char * code = "\n        class Value {\n        public:\n            int data;\n        };\n        class Wrapper {\n        public:\n            Value* ptr;\n            Value& operator*();\n        };\n    ";
	auto * TU;
	int * opDeref;
}

int TEST_F_SpecialOperatorTest_int_3(struct SpecialOperatorTest, int) {
	const char * code = "\n        class Element {\n        public:\n            int value;\n        };\n        class ConstWrapper {\n        public:\n            Element* ptr;\n            const Element& operator*() const;\n        };\n    ";
	auto * TU;
	int * opDeref;
}

int TEST_F_SpecialOperatorTest_int_4(struct SpecialOperatorTest, int) {
	const char * code = "\n        class Object {\n        public:\n            int value;\n        };\n        class UniquePtr {\n        public:\n            Object* ptr;\n            Object* operator->();\n            Object& operator*();\n        };\n    ";
	auto * TU;
	int * opArrow;
	int * opDeref;
}

int TEST_F_SpecialOperatorTest_int_5(struct SpecialOperatorTest, int) {
	const char * code = "\n        class AddressWrapper {\n        public:\n            int* data;\n            AddressWrapper* operator&();\n        };\n    ";
	auto * TU;
	int * opAddress;
}

int TEST_F_SpecialOperatorTest_int_6(struct SpecialOperatorTest, int) {
	const char * code = "\n        class Sequence {\n        public:\n            int value;\n            Sequence operator,(const Sequence& other);\n        };\n    ";
	auto * TU;
	int * opComma;
}

int TEST_F_SpecialOperatorTest_int_7(struct SpecialOperatorTest, int) {
	const char * code = "\n        class Bits {\n        public:\n            unsigned int value;\n            Bits operator~() const;\n            Bits operator&(const Bits& other) const;\n            Bits operator|(const Bits& other) const;\n            Bits operator^(const Bits& other) const;\n        };\n    ";
	auto * TU;
	int bitwiseOpCount = 0;
}

int TEST_F_SpecialOperatorTest_int_8(struct SpecialOperatorTest, int) {
	const char * code = "\n        class ShiftValue {\n        public:\n            unsigned int value;\n            ShiftValue operator<<(int shift) const;\n            ShiftValue operator>>(int shift) const;\n        };\n    ";
	auto * TU;
	int * opLeftShift;
	int * opRightShift;
}

int TEST_F_SpecialOperatorTest_int_9(struct SpecialOperatorTest, int) {
	const char * code = "\n        class Bool {\n        public:\n            bool value;\n            bool operator!() const;\n            bool operator&&(const Bool& other) const;\n            bool operator||(const Bool& other) const;\n        };\n    ";
	auto * TU;
	int logicalOpCount = 0;
}

int TEST_F_SpecialOperatorTest_int_10(struct SpecialOperatorTest, int) {
	const char * code = "\n        class Assignable {\n        public:\n            int value;\n            Assignable& operator=(const Assignable& other);\n        };\n    ";
	auto * TU;
	int * opAssign;
}

int TEST_F_SpecialOperatorTest_int_11(struct SpecialOperatorTest, int) {
	const char * code = "\n        class Movable {\n        public:\n            int* data;\n            Movable& operator=(Movable&& other);\n        };\n    ";
	auto * TU;
	int * opMoveAssign;
}

static void ConversionOperatorTest__ctor_default(struct ConversionOperatorTest * this) {
}

static void ConversionOperatorTest__ctor_copy(struct ConversionOperatorTest * this, const struct ConversionOperatorTest * other) {
}

int TEST_F_ConversionOperatorTest_int(struct ConversionOperatorTest, int) {
	const char * code = "\n        class Wrapper {\n        public:\n            int value;\n            operator int() const;\n        };\n    ";
	auto * TU;
	int * convOp;
}

int TEST_F_ConversionOperatorTest_int_1(struct ConversionOperatorTest, int) {
	const char * code = "\n        class SafeWrapper {\n        public:\n            int value;\n            explicit operator int() const;\n        };\n    ";
	auto * TU;
	int * convOp;
}

int TEST_F_ConversionOperatorTest_int_2(struct ConversionOperatorTest, int) {
	const char * code = "\n        class BoolConvertible {\n        public:\n            bool valid;\n            explicit operator bool() const;\n        };\n    ";
	auto * TU;
	int * convOp;
}

int TEST_F_ConversionOperatorTest_int_3(struct ConversionOperatorTest, int) {
	const char * code = "\n        class PointerWrapper {\n        public:\n            int* data;\n            operator int*() const;\n        };\n    ";
	auto * TU;
	int * convOp;
}

int TEST_F_ConversionOperatorTest_int_4(struct ConversionOperatorTest, int) {
	const char * code = "\n        class RefWrapper {\n        public:\n            int data;\n            operator int&();\n        };\n    ";
	auto * TU;
	int * convOp;
}

int TEST_F_ConversionOperatorTest_int_5(struct ConversionOperatorTest, int) {
	const char * code = "\n        class Target {\n        public:\n            int value;\n        };\n        class Source {\n        public:\n            int data;\n            operator Target() const;\n        };\n    ";
	auto * TU;
	int * convOp;
}

int TEST_F_ConversionOperatorTest_int_6(struct ConversionOperatorTest, int) {
	const char * code = "\n        class MultiConvert {\n        public:\n            int value;\n            operator int() const;\n            operator double() const;\n            explicit operator bool() const;\n        };\n    ";
	auto * TU;
	int convOpCount = 0;
}

int TEST_F_ConversionOperatorTest_int_7(struct ConversionOperatorTest, int) {
	const char * code = "\n        class ConstConvert {\n        public:\n            int value;\n            operator int() const;\n        };\n    ";
	auto * TU;
	int * convOp;
}

int TEST_F_ConversionOperatorTest_int_8(struct ConversionOperatorTest, int) {
	const char * code = "\n        class ConstTypeConvert {\n        public:\n            int* data;\n            operator const int*() const;\n        };\n    ";
	auto * TU;
	int * convOp;
	int convType;
}

int TEST_F_ConversionOperatorTest_int_9(struct ConversionOperatorTest, int) {
	const char * code = "\n        class ComputedConversion {\n        public:\n            int value;\n            operator int() const { return value * 2; }\n        };\n    ";
	auto * TU;
	int * convOp;
}

static void StreamOperatorTest__ctor_default(struct StreamOperatorTest * this) {
}

static void StreamOperatorTest__ctor_copy(struct StreamOperatorTest * this, const struct StreamOperatorTest * other) {
}

int TEST_F_StreamOperatorTest_int(struct StreamOperatorTest, int) {
	const char * code = "\n        class OStream {\n        public:\n            OStream& operator<<(int value);\n        };\n    ";
	auto * TU;
	int * opOutput;
}

int TEST_F_StreamOperatorTest_int_1(struct StreamOperatorTest, int) {
	const char * code = "\n        class IStream {\n        public:\n            IStream& operator>>(int& value);\n        };\n    ";
	auto * TU;
	int * opInput;
}

int TEST_F_StreamOperatorTest_int_2(struct StreamOperatorTest, int) {
	const char * code = "\n        class OStream {\n        public:\n            OStream& write(const char* s);\n        };\n        class Printable {\n        public:\n            int value;\n            friend OStream& operator<<(OStream& os, const Printable& p);\n        };\n        OStream& operator<<(OStream& os, const Printable& p);\n    ";
	auto * TU;
	int * friendOp;
}


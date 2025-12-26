// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/type_traits/TypeTraitsTest.cpp
// Implementation file

#include "TypeTraitsTest.h"

static void TypeTraitsTest__ctor_default(struct TypeTraitsTest * this) {
}

static void TypeTraitsTest__ctor_copy(struct TypeTraitsTest * this, const struct TypeTraitsTest * other) {
}

int TypeTraitsTest_buildAST(struct TypeTraitsTest * this, const char * code) {
}

int * TypeTraitsTest_findFunction(struct TypeTraitsTest * this, int * Context, const int * name) {
	int *TU;

	return nullptr;
;
}

int TEST_F(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        constexpr bool check_integral() {\n            return std::is_integral<T>::value;\n        }\n\n        void test() {\n            static_assert(check_integral<int>(), \"int should be integral\");\n            static_assert(check_integral<long>(), \"long should be integral\");\n            static_assert(!check_integral<float>(), \"float should not be integral\");\n            static_assert(!check_integral<double>(), \"double should not be integral\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        constexpr bool check_pointer() {\n            return std::is_pointer<T>::value;\n        }\n\n        void test() {\n            static_assert(check_pointer<int*>(), \"int* should be pointer\");\n            static_assert(check_pointer<void*>(), \"void* should be pointer\");\n            static_assert(!check_pointer<int>(), \"int should not be pointer\");\n            static_assert(!check_pointer<int&>(), \"int& should not be pointer\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_1(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        constexpr bool check_const() {\n            return std::is_const<T>::value;\n        }\n\n        void test() {\n            static_assert(check_const<const int>(), \"const int should be const\");\n            static_assert(!check_const<int>(), \"int should not be const\");\n            static_assert(check_const<const int*>(), \"const int* should be const pointer\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_2(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        constexpr bool check_reference() {\n            return std::is_reference<T>::value;\n        }\n\n        void test() {\n            static_assert(check_reference<int&>(), \"int& should be reference\");\n            static_assert(check_reference<int&&>(), \"int&& should be reference\");\n            static_assert(!check_reference<int>(), \"int should not be reference\");\n            static_assert(!check_reference<int*>(), \"int* should not be reference\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_3(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        constexpr bool check_floating() {\n            return std::is_floating_point<T>::value;\n        }\n\n        void test() {\n            static_assert(check_floating<float>(), \"float should be floating point\");\n            static_assert(check_floating<double>(), \"double should be floating point\");\n            static_assert(!check_floating<int>(), \"int should not be floating point\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_4(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        constexpr bool check_array() {\n            return std::is_array<T>::value;\n        }\n\n        void test() {\n            static_assert(check_array<int[5]>(), \"int[5] should be array\");\n            static_assert(check_array<int[]>(), \"int[] should be array\");\n            static_assert(!check_array<int*>(), \"int* should not be array\");\n            static_assert(!check_array<int>(), \"int should not be array\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_5(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        void func() {}\n\n        template<typename T>\n        constexpr bool check_function() {\n            return std::is_function<T>::value;\n        }\n\n        void test() {\n            static_assert(check_function<void()>(), \"void() should be function\");\n            static_assert(check_function<int(double)>(), \"int(double) should be function\");\n            static_assert(!check_function<void(*)()>(), \"void(*)() should not be function\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_6(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        constexpr bool check_void() {\n            return std::is_void<T>::value;\n        }\n\n        void test() {\n            static_assert(check_void<void>(), \"void should be void\");\n            static_assert(!check_void<int>(), \"int should not be void\");\n            static_assert(!check_void<void*>(), \"void* should not be void\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_7(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        class MyClass {};\n        struct MyStruct {};\n\n        template<typename T>\n        constexpr bool check_class() {\n            return std::is_class<T>::value;\n        }\n\n        void test() {\n            static_assert(check_class<MyClass>(), \"MyClass should be class\");\n            static_assert(check_class<MyStruct>(), \"MyStruct should be class\");\n            static_assert(!check_class<int>(), \"int should not be class\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_8(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        enum MyEnum { A, B, C };\n        enum class MyEnumClass { X, Y, Z };\n\n        template<typename T>\n        constexpr bool check_enum() {\n            return std::is_enum<T>::value;\n        }\n\n        void test() {\n            static_assert(check_enum<MyEnum>(), \"MyEnum should be enum\");\n            static_assert(check_enum<MyEnumClass>(), \"MyEnumClass should be enum\");\n            static_assert(!check_enum<int>(), \"int should not be enum\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_9(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        using RemoveConstType = typename std::remove_const<T>::type;\n\n        void test() {\n            static_assert(std::is_same<RemoveConstType<const int>, int>::value,\n                          \"remove_const<const int> should be int\");\n            static_assert(std::is_same<RemoveConstType<int>, int>::value,\n                          \"remove_const<int> should be int\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_10(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        using AddPointerType = typename std::add_pointer<T>::type;\n\n        void test() {\n            static_assert(std::is_same<AddPointerType<int>, int*>::value,\n                          \"add_pointer<int> should be int*\");\n            static_assert(std::is_same<AddPointerType<int*>, int**>::value,\n                          \"add_pointer<int*> should be int**\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_11(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        using RemovePointerType = typename std::remove_pointer<T>::type;\n\n        void test() {\n            static_assert(std::is_same<RemovePointerType<int*>, int>::value,\n                          \"remove_pointer<int*> should be int\");\n            static_assert(std::is_same<RemovePointerType<int**>, int*>::value,\n                          \"remove_pointer<int**> should be int*\");\n            static_assert(std::is_same<RemovePointerType<int>, int>::value,\n                          \"remove_pointer<int> should be int\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_12(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        using AddConstType = typename std::add_const<T>::type;\n\n        void test() {\n            static_assert(std::is_same<AddConstType<int>, const int>::value,\n                          \"add_const<int> should be const int\");\n            static_assert(std::is_same<AddConstType<const int>, const int>::value,\n                          \"add_const<const int> should be const int\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_13(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        using RemoveRefType = typename std::remove_reference<T>::type;\n\n        void test() {\n            static_assert(std::is_same<RemoveRefType<int&>, int>::value,\n                          \"remove_reference<int&> should be int\");\n            static_assert(std::is_same<RemoveRefType<int&&>, int>::value,\n                          \"remove_reference<int&&> should be int\");\n            static_assert(std::is_same<RemoveRefType<int>, int>::value,\n                          \"remove_reference<int> should be int\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_14(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        using DecayType = typename std::decay<T>::type;\n\n        void test() {\n            static_assert(std::is_same<DecayType<int&>, int>::value,\n                          \"decay<int&> should be int\");\n            static_assert(std::is_same<DecayType<const int>, int>::value,\n                          \"decay<const int> should be int\");\n            static_assert(std::is_same<DecayType<int[5]>, int*>::value,\n                          \"decay<int[5]> should be int*\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_15(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<bool B, typename T, typename F>\n        using ConditionalType = typename std::conditional<B, T, F>::type;\n\n        void test() {\n            static_assert(std::is_same<ConditionalType<true, int, double>, int>::value,\n                          \"conditional<true, int, double> should be int\");\n            static_assert(std::is_same<ConditionalType<false, int, double>, double>::value,\n                          \"conditional<false, int, double> should be double\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_16(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        enum MyEnum : short { A, B, C };\n\n        template<typename T>\n        using UnderlyingType = typename std::underlying_type<T>::type;\n\n        void test() {\n            static_assert(std::is_same<UnderlyingType<MyEnum>, short>::value,\n                          \"underlying_type<MyEnum> should be short\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_17(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        using MakeSignedType = typename std::make_signed<T>::type;\n\n        void test() {\n            static_assert(std::is_same<MakeSignedType<unsigned int>, int>::value,\n                          \"make_signed<unsigned int> should be int\");\n            static_assert(std::is_same<MakeSignedType<int>, int>::value,\n                          \"make_signed<int> should be int\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_18(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        using MakeUnsignedType = typename std::make_unsigned<T>::type;\n\n        void test() {\n            static_assert(std::is_same<MakeUnsignedType<int>, unsigned int>::value,\n                          \"make_unsigned<int> should be unsigned int\");\n            static_assert(std::is_same<MakeUnsignedType<unsigned int>, unsigned int>::value,\n                          \"make_unsigned<unsigned int> should be unsigned int\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_19(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        typename std::enable_if<std::is_integral<T>::value, T>::type\n        process(T value) {\n            return value * 2;\n        }\n\n        void test() {\n            int x = process(5);  // Should compile for integral types\n            // process(3.14);    // Would not compile for floating point\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_20(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        typename std::enable_if<std::is_pointer<T>::value, bool>::type\n        isNull(T ptr) {\n            return ptr == nullptr;\n        }\n\n        void test() {\n            int* p = nullptr;\n            bool result = isNull(p);  // Should compile for pointer types\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_21(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T,\n                 typename = typename std::enable_if<std::is_arithmetic<T>::value>::type>\n        T add(T a, T b) {\n            return a + b;\n        }\n\n        void test() {\n            int x = add(1, 2);\n            double y = add(1.5, 2.5);\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_22(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        // Overload for integral types\n        template<typename T>\n        typename std::enable_if<std::is_integral<T>::value, int>::type\n        getValue(T) {\n            return 1;\n        }\n\n        // Overload for floating point types\n        template<typename T>\n        typename std::enable_if<std::is_floating_point<T>::value, int>::type\n        getValue(T) {\n            return 2;\n        }\n\n        void test() {\n            int r1 = getValue(42);      // Should call integral version\n            int r2 = getValue(3.14);    // Should call floating point version\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_23(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        std::enable_if_t<std::is_integral<T>::value, T>\n        square(T value) {\n            return value * value;\n        }\n\n        void test() {\n            int x = square(5);\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_24(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T, typename Enable = void>\n        struct TypeHandler {\n            static constexpr int value = 0;\n        };\n\n        template<typename T>\n        struct TypeHandler<T, typename std::enable_if<std::is_integral<T>::value>::type> {\n            static constexpr int value = 1;\n        };\n\n        template<typename T>\n        struct TypeHandler<T, typename std::enable_if<std::is_floating_point<T>::value>::type> {\n            static constexpr int value = 2;\n        };\n\n        void test() {\n            static_assert(TypeHandler<int>::value == 1, \"int handler\");\n            static_assert(TypeHandler<double>::value == 2, \"double handler\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_25(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        typename std::enable_if<\n            std::is_integral<T>::value && !std::is_same<T, bool>::value,\n            T\n        >::type\n        increment(T value) {\n            return value + 1;\n        }\n\n        void test() {\n            int x = increment(5);\n            // bool b = increment(true);  // Would not compile\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_26(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        typename std::enable_if<\n            std::is_arithmetic<T>::value &&\n            sizeof(T) <= sizeof(long),\n            T\n        >::type\n        convert(T value) {\n            return value;\n        }\n\n        void test() {\n            int x = convert(42);\n            double y = convert(3.14);\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_27(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename, typename = void>\n        struct HasTypeMember : std::false_type {};\n\n        template<typename T>\n        struct HasTypeMember<T, std::void_t<typename T::type>> : std::true_type {};\n\n        struct WithType { using type = int; };\n        struct WithoutType {};\n\n        void test() {\n            static_assert(HasTypeMember<WithType>::value, \"WithType has type member\");\n            static_assert(!HasTypeMember<WithoutType>::value, \"WithoutType lacks type member\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_28(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        typename std::enable_if<\n            std::is_integral<typename std::decay<T>::type>::value,\n            typename std::decay<T>::type\n        >::type\n        process(T value) {\n            return value;\n        }\n\n        void test() {\n            const int& x = 42;\n            int result = process(x);\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_29(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        void test() {\n            static_assert(std::is_same<int, int>::value, \"int should be same as int\");\n            static_assert(!std::is_same<int, long>::value, \"int should not be same as long\");\n            static_assert(std::is_same<const int, const int>::value, \"const int same\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_30(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        class Base {};\n        class Derived : public Base {};\n        class Unrelated {};\n\n        void test() {\n            static_assert(std::is_base_of<Base, Derived>::value, \"Base is base of Derived\");\n            static_assert(!std::is_base_of<Derived, Base>::value, \"Derived not base of Base\");\n            static_assert(!std::is_base_of<Base, Unrelated>::value, \"Base not base of Unrelated\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_31(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        class Base {};\n        class Derived : public Base {};\n\n        void test() {\n            static_assert(std::is_convertible<Derived*, Base*>::value,\n                          \"Derived* convertible to Base*\");\n            static_assert(std::is_convertible<int, double>::value,\n                          \"int convertible to double\");\n            static_assert(!std::is_convertible<int*, double*>::value,\n                          \"int* not convertible to double*\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_32(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        struct Foo {\n            Foo(int) {}\n        };\n\n        void test() {\n            static_assert(std::is_constructible<Foo, int>::value,\n                          \"Foo is constructible from int\");\n            static_assert(!std::is_constructible<Foo, double>::value,\n                          \"Foo not constructible from double\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_33(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        void test() {\n            constexpr size_t intAlign = std::alignment_of<int>::value;\n            constexpr size_t doubleAlign = std::alignment_of<double>::value;\n            static_assert(intAlign > 0, \"int has non-zero alignment\");\n            static_assert(doubleAlign > 0, \"double has non-zero alignment\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_34(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        void test() {\n            static_assert(std::rank<int>::value == 0, \"int has rank 0\");\n            static_assert(std::rank<int[5]>::value == 1, \"int[5] has rank 1\");\n            static_assert(std::rank<int[5][10]>::value == 2, \"int[5][10] has rank 2\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_35(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        void test() {\n            static_assert(std::extent<int[5]>::value == 5, \"int[5] extent is 5\");\n            static_assert(std::extent<int[5][10], 0>::value == 5, \"int[5][10] first dimension\");\n            static_assert(std::extent<int[5][10], 1>::value == 10, \"int[5][10] second dimension\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_36(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T1, typename T2>\n        using CommonType = typename std::common_type<T1, T2>::type;\n\n        void test() {\n            static_assert(std::is_same<CommonType<int, int>, int>::value,\n                          \"common_type<int, int> is int\");\n            static_assert(std::is_same<CommonType<int, double>, double>::value,\n                          \"common_type<int, double> is double\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_37(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        struct SelectType {\n            using type = typename std::conditional<\n                std::is_integral<T>::value,\n                long long,\n                double\n            >::type;\n        };\n\n        void test() {\n            static_assert(std::is_same<SelectType<int>::type, long long>::value,\n                          \"int selects long long\");\n            static_assert(std::is_same<SelectType<float>::type, double>::value,\n                          \"float selects double\");\n        }\n    ";

	auto AST;

}

int TEST_F_TypeTraitsTest_int_38(struct TypeTraitsTest, int) {
	const char *code = "\n        #include <type_traits>\n\n        template<typename T>\n        struct IsIntegralPointer {\n            static constexpr bool value =\n                std::is_pointer<T>::value &&\n                std::is_integral<typename std::remove_pointer<T>::type>::value;\n        };\n\n        void test() {\n            static_assert(IsIntegralPointer<int*>::value, \"int* is integral pointer\");\n            static_assert(!IsIntegralPointer<double*>::value, \"double* not integral pointer\");\n            static_assert(!IsIntegralPointer<int>::value, \"int not integral pointer\");\n        }\n    ";

	auto AST;

}


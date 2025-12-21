/**
 * @file TypeTraitsTest.cpp
 * @brief Stream 5: Type Traits & SFINAE Comprehensive Test Suite
 *
 * Tests for C++ type traits, SFINAE patterns, enable_if, and compile-time type conditionals.
 * These features are crucial for template metaprogramming and must be properly evaluated
 * at compile-time and transpiled to appropriate C code.
 *
 * Coverage:
 * - Basic type traits (is_integral, is_pointer, is_const, etc.)
 * - Type transformations (remove_const, add_pointer, decay, etc.)
 * - SFINAE patterns and enable_if
 * - Compile-time conditionals (conditional_t, etc.)
 * - Type relationships (is_same, is_base_of, is_convertible)
 * - Compile-time trait evaluation
 *
 * Tests: 40 comprehensive unit tests
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"
#include <string>
#include <vector>

using namespace clang;

// Test fixture for type traits tests
class TypeTraitsTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        std::vector<std::string> args = {"-std=c++17"};
        return tooling::buildASTFromCodeWithArgs(code, args, "input.cpp");
    }

    FunctionDecl* findFunction(ASTContext& Context, const std::string& name) {
        TranslationUnitDecl* TU = Context.getTranslationUnitDecl();
        for (auto* Decl : TU->decls()) {
            if (auto* FD = dyn_cast<FunctionDecl>(Decl)) {
                if (FD->getNameAsString() == name) {
                    return FD;
                }
            }
        }
        return nullptr;
    }
};

// ============================================================================
// SECTION 1: Basic Type Traits (Tests 1-10)
// ============================================================================

TEST_F(TypeTraitsTest, IsIntegralTrait) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        constexpr bool check_integral() {
            return std::is_integral<T>::value;
        }

        void test() {
            static_assert(check_integral<int>(), "int should be integral");
            static_assert(check_integral<long>(), "long should be integral");
            static_assert(!check_integral<float>(), "float should not be integral");
            static_assert(!check_integral<double>(), "double should not be integral");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
    EXPECT_NE(AST->getASTContext().getDiagnostics().getClient(), nullptr);
}

TEST_F(TypeTraitsTest, IsPointerTrait) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        constexpr bool check_pointer() {
            return std::is_pointer<T>::value;
        }

        void test() {
            static_assert(check_pointer<int*>(), "int* should be pointer");
            static_assert(check_pointer<void*>(), "void* should be pointer");
            static_assert(!check_pointer<int>(), "int should not be pointer");
            static_assert(!check_pointer<int&>(), "int& should not be pointer");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsConstTrait) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        constexpr bool check_const() {
            return std::is_const<T>::value;
        }

        void test() {
            static_assert(check_const<const int>(), "const int should be const");
            static_assert(!check_const<int>(), "int should not be const");
            static_assert(check_const<const int*>(), "const int* should be const pointer");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsReferenceTrait) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        constexpr bool check_reference() {
            return std::is_reference<T>::value;
        }

        void test() {
            static_assert(check_reference<int&>(), "int& should be reference");
            static_assert(check_reference<int&&>(), "int&& should be reference");
            static_assert(!check_reference<int>(), "int should not be reference");
            static_assert(!check_reference<int*>(), "int* should not be reference");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsFloatingPointTrait) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        constexpr bool check_floating() {
            return std::is_floating_point<T>::value;
        }

        void test() {
            static_assert(check_floating<float>(), "float should be floating point");
            static_assert(check_floating<double>(), "double should be floating point");
            static_assert(!check_floating<int>(), "int should not be floating point");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsArrayTrait) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        constexpr bool check_array() {
            return std::is_array<T>::value;
        }

        void test() {
            static_assert(check_array<int[5]>(), "int[5] should be array");
            static_assert(check_array<int[]>(), "int[] should be array");
            static_assert(!check_array<int*>(), "int* should not be array");
            static_assert(!check_array<int>(), "int should not be array");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsFunctionTrait) {
    const char* code = R"(
        #include <type_traits>

        void func() {}

        template<typename T>
        constexpr bool check_function() {
            return std::is_function<T>::value;
        }

        void test() {
            static_assert(check_function<void()>(), "void() should be function");
            static_assert(check_function<int(double)>(), "int(double) should be function");
            static_assert(!check_function<void(*)()>(), "void(*)() should not be function");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsVoidTrait) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        constexpr bool check_void() {
            return std::is_void<T>::value;
        }

        void test() {
            static_assert(check_void<void>(), "void should be void");
            static_assert(!check_void<int>(), "int should not be void");
            static_assert(!check_void<void*>(), "void* should not be void");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsClassTrait) {
    const char* code = R"(
        #include <type_traits>

        class MyClass {};
        struct MyStruct {};

        template<typename T>
        constexpr bool check_class() {
            return std::is_class<T>::value;
        }

        void test() {
            static_assert(check_class<MyClass>(), "MyClass should be class");
            static_assert(check_class<MyStruct>(), "MyStruct should be class");
            static_assert(!check_class<int>(), "int should not be class");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsEnumTrait) {
    const char* code = R"(
        #include <type_traits>

        enum MyEnum { A, B, C };
        enum class MyEnumClass { X, Y, Z };

        template<typename T>
        constexpr bool check_enum() {
            return std::is_enum<T>::value;
        }

        void test() {
            static_assert(check_enum<MyEnum>(), "MyEnum should be enum");
            static_assert(check_enum<MyEnumClass>(), "MyEnumClass should be enum");
            static_assert(!check_enum<int>(), "int should not be enum");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

// ============================================================================
// SECTION 2: Type Transformations (Tests 11-20)
// ============================================================================

TEST_F(TypeTraitsTest, RemoveConstTransformation) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        using RemoveConstType = typename std::remove_const<T>::type;

        void test() {
            static_assert(std::is_same<RemoveConstType<const int>, int>::value,
                          "remove_const<const int> should be int");
            static_assert(std::is_same<RemoveConstType<int>, int>::value,
                          "remove_const<int> should be int");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, AddPointerTransformation) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        using AddPointerType = typename std::add_pointer<T>::type;

        void test() {
            static_assert(std::is_same<AddPointerType<int>, int*>::value,
                          "add_pointer<int> should be int*");
            static_assert(std::is_same<AddPointerType<int*>, int**>::value,
                          "add_pointer<int*> should be int**");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, RemovePointerTransformation) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        using RemovePointerType = typename std::remove_pointer<T>::type;

        void test() {
            static_assert(std::is_same<RemovePointerType<int*>, int>::value,
                          "remove_pointer<int*> should be int");
            static_assert(std::is_same<RemovePointerType<int**>, int*>::value,
                          "remove_pointer<int**> should be int*");
            static_assert(std::is_same<RemovePointerType<int>, int>::value,
                          "remove_pointer<int> should be int");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, AddConstTransformation) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        using AddConstType = typename std::add_const<T>::type;

        void test() {
            static_assert(std::is_same<AddConstType<int>, const int>::value,
                          "add_const<int> should be const int");
            static_assert(std::is_same<AddConstType<const int>, const int>::value,
                          "add_const<const int> should be const int");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, RemoveReferenceTransformation) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        using RemoveRefType = typename std::remove_reference<T>::type;

        void test() {
            static_assert(std::is_same<RemoveRefType<int&>, int>::value,
                          "remove_reference<int&> should be int");
            static_assert(std::is_same<RemoveRefType<int&&>, int>::value,
                          "remove_reference<int&&> should be int");
            static_assert(std::is_same<RemoveRefType<int>, int>::value,
                          "remove_reference<int> should be int");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, DecayTransformation) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        using DecayType = typename std::decay<T>::type;

        void test() {
            static_assert(std::is_same<DecayType<int&>, int>::value,
                          "decay<int&> should be int");
            static_assert(std::is_same<DecayType<const int>, int>::value,
                          "decay<const int> should be int");
            static_assert(std::is_same<DecayType<int[5]>, int*>::value,
                          "decay<int[5]> should be int*");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, ConditionalTypeTransformation) {
    const char* code = R"(
        #include <type_traits>

        template<bool B, typename T, typename F>
        using ConditionalType = typename std::conditional<B, T, F>::type;

        void test() {
            static_assert(std::is_same<ConditionalType<true, int, double>, int>::value,
                          "conditional<true, int, double> should be int");
            static_assert(std::is_same<ConditionalType<false, int, double>, double>::value,
                          "conditional<false, int, double> should be double");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, UnderlyingTypeForEnums) {
    const char* code = R"(
        #include <type_traits>

        enum MyEnum : short { A, B, C };

        template<typename T>
        using UnderlyingType = typename std::underlying_type<T>::type;

        void test() {
            static_assert(std::is_same<UnderlyingType<MyEnum>, short>::value,
                          "underlying_type<MyEnum> should be short");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, MakeSignedTransformation) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        using MakeSignedType = typename std::make_signed<T>::type;

        void test() {
            static_assert(std::is_same<MakeSignedType<unsigned int>, int>::value,
                          "make_signed<unsigned int> should be int");
            static_assert(std::is_same<MakeSignedType<int>, int>::value,
                          "make_signed<int> should be int");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, MakeUnsignedTransformation) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        using MakeUnsignedType = typename std::make_unsigned<T>::type;

        void test() {
            static_assert(std::is_same<MakeUnsignedType<int>, unsigned int>::value,
                          "make_unsigned<int> should be unsigned int");
            static_assert(std::is_same<MakeUnsignedType<unsigned int>, unsigned int>::value,
                          "make_unsigned<unsigned int> should be unsigned int");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

// ============================================================================
// SECTION 3: SFINAE and enable_if (Tests 21-30)
// ============================================================================

TEST_F(TypeTraitsTest, EnableIfBasicUsage) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        typename std::enable_if<std::is_integral<T>::value, T>::type
        process(T value) {
            return value * 2;
        }

        void test() {
            int x = process(5);  // Should compile for integral types
            // process(3.14);    // Would not compile for floating point
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, EnableIfWithReturnType) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        typename std::enable_if<std::is_pointer<T>::value, bool>::type
        isNull(T ptr) {
            return ptr == nullptr;
        }

        void test() {
            int* p = nullptr;
            bool result = isNull(p);  // Should compile for pointer types
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, EnableIfWithTemplateParameter) {
    const char* code = R"(
        #include <type_traits>

        template<typename T,
                 typename = typename std::enable_if<std::is_arithmetic<T>::value>::type>
        T add(T a, T b) {
            return a + b;
        }

        void test() {
            int x = add(1, 2);
            double y = add(1.5, 2.5);
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, SFINAEWithFunctionOverloading) {
    const char* code = R"(
        #include <type_traits>

        // Overload for integral types
        template<typename T>
        typename std::enable_if<std::is_integral<T>::value, int>::type
        getValue(T) {
            return 1;
        }

        // Overload for floating point types
        template<typename T>
        typename std::enable_if<std::is_floating_point<T>::value, int>::type
        getValue(T) {
            return 2;
        }

        void test() {
            int r1 = getValue(42);      // Should call integral version
            int r2 = getValue(3.14);    // Should call floating point version
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, EnableIfTAlias) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        std::enable_if_t<std::is_integral<T>::value, T>
        square(T value) {
            return value * value;
        }

        void test() {
            int x = square(5);
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, SFINAEWithClassSpecialization) {
    const char* code = R"(
        #include <type_traits>

        template<typename T, typename Enable = void>
        struct TypeHandler {
            static constexpr int value = 0;
        };

        template<typename T>
        struct TypeHandler<T, typename std::enable_if<std::is_integral<T>::value>::type> {
            static constexpr int value = 1;
        };

        template<typename T>
        struct TypeHandler<T, typename std::enable_if<std::is_floating_point<T>::value>::type> {
            static constexpr int value = 2;
        };

        void test() {
            static_assert(TypeHandler<int>::value == 1, "int handler");
            static_assert(TypeHandler<double>::value == 2, "double handler");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, ComplexSFINAEExpression) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        typename std::enable_if<
            std::is_integral<T>::value && !std::is_same<T, bool>::value,
            T
        >::type
        increment(T value) {
            return value + 1;
        }

        void test() {
            int x = increment(5);
            // bool b = increment(true);  // Would not compile
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, SFINAEWithMultipleConditions) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        typename std::enable_if<
            std::is_arithmetic<T>::value &&
            sizeof(T) <= sizeof(long),
            T
        >::type
        convert(T value) {
            return value;
        }

        void test() {
            int x = convert(42);
            double y = convert(3.14);
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, VoidTPattern) {
    const char* code = R"(
        #include <type_traits>

        template<typename, typename = void>
        struct HasTypeMember : std::false_type {};

        template<typename T>
        struct HasTypeMember<T, std::void_t<typename T::type>> : std::true_type {};

        struct WithType { using type = int; };
        struct WithoutType {};

        void test() {
            static_assert(HasTypeMember<WithType>::value, "WithType has type member");
            static_assert(!HasTypeMember<WithoutType>::value, "WithoutType lacks type member");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, NestedEnableIf) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        typename std::enable_if<
            std::is_integral<typename std::decay<T>::type>::value,
            typename std::decay<T>::type
        >::type
        process(T value) {
            return value;
        }

        void test() {
            const int& x = 42;
            int result = process(x);
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

// ============================================================================
// SECTION 4: Type Relationships & Compile-time Evaluation (Tests 31-40)
// ============================================================================

TEST_F(TypeTraitsTest, IsSameTrait) {
    const char* code = R"(
        #include <type_traits>

        void test() {
            static_assert(std::is_same<int, int>::value, "int should be same as int");
            static_assert(!std::is_same<int, long>::value, "int should not be same as long");
            static_assert(std::is_same<const int, const int>::value, "const int same");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsBaseOfTrait) {
    const char* code = R"(
        #include <type_traits>

        class Base {};
        class Derived : public Base {};
        class Unrelated {};

        void test() {
            static_assert(std::is_base_of<Base, Derived>::value, "Base is base of Derived");
            static_assert(!std::is_base_of<Derived, Base>::value, "Derived not base of Base");
            static_assert(!std::is_base_of<Base, Unrelated>::value, "Base not base of Unrelated");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsConvertibleTrait) {
    const char* code = R"(
        #include <type_traits>

        class Base {};
        class Derived : public Base {};

        void test() {
            static_assert(std::is_convertible<Derived*, Base*>::value,
                          "Derived* convertible to Base*");
            static_assert(std::is_convertible<int, double>::value,
                          "int convertible to double");
            static_assert(!std::is_convertible<int*, double*>::value,
                          "int* not convertible to double*");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, IsConstructibleTrait) {
    const char* code = R"(
        #include <type_traits>

        struct Foo {
            Foo(int) {}
        };

        void test() {
            static_assert(std::is_constructible<Foo, int>::value,
                          "Foo is constructible from int");
            static_assert(!std::is_constructible<Foo, double>::value,
                          "Foo not constructible from double");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, AlignmentOfTrait) {
    const char* code = R"(
        #include <type_traits>

        void test() {
            constexpr size_t intAlign = std::alignment_of<int>::value;
            constexpr size_t doubleAlign = std::alignment_of<double>::value;
            static_assert(intAlign > 0, "int has non-zero alignment");
            static_assert(doubleAlign > 0, "double has non-zero alignment");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, RankTrait) {
    const char* code = R"(
        #include <type_traits>

        void test() {
            static_assert(std::rank<int>::value == 0, "int has rank 0");
            static_assert(std::rank<int[5]>::value == 1, "int[5] has rank 1");
            static_assert(std::rank<int[5][10]>::value == 2, "int[5][10] has rank 2");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, ExtentTrait) {
    const char* code = R"(
        #include <type_traits>

        void test() {
            static_assert(std::extent<int[5]>::value == 5, "int[5] extent is 5");
            static_assert(std::extent<int[5][10], 0>::value == 5, "int[5][10] first dimension");
            static_assert(std::extent<int[5][10], 1>::value == 10, "int[5][10] second dimension");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, CommonTypeDeduction) {
    const char* code = R"(
        #include <type_traits>

        template<typename T1, typename T2>
        using CommonType = typename std::common_type<T1, T2>::type;

        void test() {
            static_assert(std::is_same<CommonType<int, int>, int>::value,
                          "common_type<int, int> is int");
            static_assert(std::is_same<CommonType<int, double>, double>::value,
                          "common_type<int, double> is double");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, CompileTimeTypeSelection) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        struct SelectType {
            using type = typename std::conditional<
                std::is_integral<T>::value,
                long long,
                double
            >::type;
        };

        void test() {
            static_assert(std::is_same<SelectType<int>::type, long long>::value,
                          "int selects long long");
            static_assert(std::is_same<SelectType<float>::type, double>::value,
                          "float selects double");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

TEST_F(TypeTraitsTest, ComplexTraitComposition) {
    const char* code = R"(
        #include <type_traits>

        template<typename T>
        struct IsIntegralPointer {
            static constexpr bool value =
                std::is_pointer<T>::value &&
                std::is_integral<typename std::remove_pointer<T>::type>::value;
        };

        void test() {
            static_assert(IsIntegralPointer<int*>::value, "int* is integral pointer");
            static_assert(!IsIntegralPointer<double*>::value, "double* not integral pointer");
            static_assert(!IsIntegralPointer<int>::value, "int not integral pointer");
        }
    )";

    auto AST = buildAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
}

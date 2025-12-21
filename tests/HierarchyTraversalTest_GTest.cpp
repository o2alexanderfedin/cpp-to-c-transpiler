// tests/HierarchyTraversalTest_GTest.cpp
// Migrated from HierarchyTraversalTest.cpp to Google Test framework
// Test suite for Story #86: Hierarchy Traversal Algorithm

#include <gtest/gtest.h>
#include <cstddef>
#include <cstring>

// Forward declarations of runtime functions
extern "C" {
// Type info structures (Itanium ABI)
struct __class_type_info {
  const void *vtable_ptr;
  const char *type_name;
};

struct __si_class_type_info {
  const void *vtable_ptr;
  const char *type_name;
  const struct __class_type_info *base_type;
};

struct __base_class_type_info {
  const struct __class_type_info *base_type;
  long offset_flags;
};

struct __vmi_class_type_info {
  const void *vtable_ptr;
  const char *type_name;
  unsigned int flags;
  unsigned int base_count;
  struct __base_class_type_info base_info[1];
};

// External vtable pointers (mock for testing)
extern const void *__vt_class_type_info;
extern const void *__vt_si_class_type_info;
extern const void *__vt_vmi_class_type_info;

// Hierarchy traversal function to be implemented
void *traverse_hierarchy(const void *ptr, const struct __class_type_info *src,
                         const struct __class_type_info *dst);
}

// Mock vtable pointers for testing
const void *__vt_class_type_info = (const void *)0x1000;
const void *__vt_si_class_type_info = (const void *)0x2000;
const void *__vt_vmi_class_type_info = (const void *)0x3000;

// Test fixture for Hierarchy Traversal tests
class HierarchyTraversalTestFixture : public ::testing::Test {
protected:
    // No specific setup needed for these tests
};

// Test 1: Single inheritance traversal - direct base match
TEST_F(HierarchyTraversalTestFixture, SingleInheritanceDirectBase) {
    const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                              .type_name = "4Base"};

    const struct __si_class_type_info ti_Derived = {.vtable_ptr =
                                                        __vt_si_class_type_info,
                                                    .type_name = "7Derived",
                                                    .base_type = &ti_Base};

    int dummy_object = 42;
    void *ptr = &dummy_object;

    void *result = traverse_hierarchy(
        ptr, (const struct __class_type_info *)&ti_Derived, &ti_Base);

    EXPECT_EQ(result, ptr) << "Direct base should return original pointer";
}

// Test 2: Single inheritance traversal - multi-level chain
TEST_F(HierarchyTraversalTestFixture, SingleInheritanceMultiLevel) {
    const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                              .type_name = "4Base"};

    const struct __si_class_type_info ti_Derived1 = {.vtable_ptr =
                                                         __vt_si_class_type_info,
                                                     .type_name = "8Derived1",
                                                     .base_type = &ti_Base};

    const struct __si_class_type_info ti_Derived2 = {
        .vtable_ptr = __vt_si_class_type_info,
        .type_name = "8Derived2",
        .base_type = (const struct __class_type_info *)&ti_Derived1};

    int dummy_object = 42;
    void *ptr = &dummy_object;

    void *result = traverse_hierarchy(
        ptr, (const struct __class_type_info *)&ti_Derived2, &ti_Base);

    EXPECT_EQ(result, ptr) << "Multi-level traversal should find Base";
}

// Test 3: Single inheritance - type not found
TEST_F(HierarchyTraversalTestFixture, SingleInheritanceNotFound) {
    const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                              .type_name = "4Base"};

    const struct __si_class_type_info ti_Derived = {.vtable_ptr =
                                                        __vt_si_class_type_info,
                                                    .type_name = "7Derived",
                                                    .base_type = &ti_Base};

    const struct __class_type_info ti_Unrelated = {
        .vtable_ptr = __vt_class_type_info, .type_name = "9Unrelated"};

    int dummy_object = 42;
    void *ptr = &dummy_object;

    void *result = traverse_hierarchy(
        ptr, (const struct __class_type_info *)&ti_Derived, &ti_Unrelated);

    EXPECT_EQ(result, nullptr) << "Unrelated type should return NULL";
}

// Test 4: Multiple inheritance - first base match
TEST_F(HierarchyTraversalTestFixture, MultipleInheritanceFirstBase) {
    const struct __class_type_info ti_Base1 = {.vtable_ptr = __vt_class_type_info,
                                               .type_name = "5Base1"};

    const struct __class_type_info ti_Base2 = {.vtable_ptr = __vt_class_type_info,
                                               .type_name = "5Base2"};

    struct {
        const void *vtable_ptr;
        const char *type_name;
        unsigned int flags;
        unsigned int base_count;
        struct __base_class_type_info base_info[2];
    } ti_Diamond = {
        .vtable_ptr = __vt_vmi_class_type_info,
        .type_name = "7Diamond",
        .flags = 0,
        .base_count = 2,
        .base_info = {
            {.base_type = &ti_Base1, .offset_flags = 0 << 8},
            {.base_type = &ti_Base2, .offset_flags = 8 << 8}
        }};

    int dummy_object = 42;
    void *ptr = &dummy_object;

    void *result = traverse_hierarchy(
        ptr, (const struct __class_type_info *)&ti_Diamond, &ti_Base1);

    EXPECT_EQ(result, ptr) << "First base should return pointer with offset 0";
}

// Test 5: Multiple inheritance - second base match with offset
TEST_F(HierarchyTraversalTestFixture, MultipleInheritanceSecondBase) {
    const struct __class_type_info ti_Base1 = {.vtable_ptr = __vt_class_type_info,
                                               .type_name = "5Base1"};

    const struct __class_type_info ti_Base2 = {.vtable_ptr = __vt_class_type_info,
                                               .type_name = "5Base2"};

    struct {
        const void *vtable_ptr;
        const char *type_name;
        unsigned int flags;
        unsigned int base_count;
        struct __base_class_type_info base_info[2];
    } ti_Diamond = {
        .vtable_ptr = __vt_vmi_class_type_info,
        .type_name = "7Diamond",
        .flags = 0,
        .base_count = 2,
        .base_info = {
            {.base_type = &ti_Base1, .offset_flags = 0 << 8},
            {.base_type = &ti_Base2, .offset_flags = 8 << 8}
        }};

    char dummy_object[16] = {0};
    void *ptr = dummy_object;

    void *result = traverse_hierarchy(
        ptr, (const struct __class_type_info *)&ti_Diamond, &ti_Base2);

    EXPECT_EQ(result, (char *)ptr + 8)
        << "Second base should return pointer with offset 8";
}

// Test 6: Multiple inheritance - recursive search
TEST_F(HierarchyTraversalTestFixture, MultipleInheritanceRecursive) {
    const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                              .type_name = "4Base"};

    const struct __si_class_type_info ti_Derived1 = {.vtable_ptr =
                                                         __vt_si_class_type_info,
                                                     .type_name = "8Derived1",
                                                     .base_type = &ti_Base};

    const struct __class_type_info ti_Derived2 = {
        .vtable_ptr = __vt_class_type_info, .type_name = "8Derived2"};

    struct {
        const void *vtable_ptr;
        const char *type_name;
        unsigned int flags;
        unsigned int base_count;
        struct __base_class_type_info base_info[2];
    } ti_Complex = {
        .vtable_ptr = __vt_vmi_class_type_info,
        .type_name = "7Complex",
        .flags = 0,
        .base_count = 2,
        .base_info = {
            {.base_type = (const struct __class_type_info *)&ti_Derived1,
             .offset_flags = 0 << 8},
            {.base_type = &ti_Derived2, .offset_flags = 16 << 8}}};

    char dummy_object[32] = {0};
    void *ptr = dummy_object;

    void *result = traverse_hierarchy(
        ptr, (const struct __class_type_info *)&ti_Complex, &ti_Base);

    EXPECT_EQ(result, ptr) << "Recursive search should find Base through Derived1";
}

// Test 7: NULL pointer handling
TEST_F(HierarchyTraversalTestFixture, NullPointerHandling) {
    const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                              .type_name = "4Base"};

    const struct __si_class_type_info ti_Derived = {.vtable_ptr =
                                                        __vt_si_class_type_info,
                                                    .type_name = "7Derived",
                                                    .base_type = &ti_Base};

    void *result = traverse_hierarchy(
        nullptr, (const struct __class_type_info *)&ti_Derived, &ti_Base);

    EXPECT_EQ(result, nullptr) << "NULL pointer should return NULL";
}

// Test 8: Same type optimization
TEST_F(HierarchyTraversalTestFixture, SameTypeOptimization) {
    const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                              .type_name = "4Base"};

    int dummy_object = 42;
    void *ptr = &dummy_object;

    void *result = traverse_hierarchy(ptr, &ti_Base, &ti_Base);

    EXPECT_EQ(result, ptr) << "Same type should return original pointer";
}

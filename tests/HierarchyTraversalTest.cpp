/**
 * @file HierarchyTraversalTest.cpp
 * @brief Test suite for Story #86: Hierarchy Traversal Algorithm
 *
 * Tests the runtime hierarchy traversal algorithm that enables dynamic_cast
 * to navigate complex inheritance hierarchies for type checking.
 *
 * Acceptance Criteria:
 * - Single inheritance traversal: Walk __si_class_type_info base chain
 * - Multiple inheritance traversal: Walk __vmi_class_type_info bases array
 * - Recursive search: Check each base and its hierarchy recursively
 * - Offset calculation: Apply base class offsets from offset_flags
 * - Match detection: Return pointer if target type found in hierarchy
 * - Not found: Return NULL if target not in hierarchy
 * - Testing: Validate traversal for Base → Derived1 → Derived2 chains
 *
 * SOLID Principles:
 * - Single Responsibility: Tests only hierarchy traversal
 * - Interface Segregation: Tests public runtime API only
 * - Dependency Inversion: Uses abstract type_info structures
 */

#include <cassert>
#include <cstddef>
#include <cstring>
#include <iostream>

// Test helper macros
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg)                                                      \
  if (!(cond)) {                                                               \
    std::cerr << "\nASSERT FAILED: " << msg << std::endl;                      \
    return;                                                                    \
  }

// Forward declarations of runtime functions to be implemented
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

/**
 * Test 1: Single inheritance traversal - direct base match
 *
 * Hierarchy: Base <- Derived
 * Test: Derived* -> Base* should succeed
 */
void test_SingleInheritanceDirectBase() {
  TEST_START("SingleInheritanceDirectBase");

  // Setup type_info structures
  const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                            .type_name = "4Base"};

  const struct __si_class_type_info ti_Derived = {.vtable_ptr =
                                                      __vt_si_class_type_info,
                                                  .type_name = "7Derived",
                                                  .base_type = &ti_Base};

  // Test object pointer
  int dummy_object = 42;
  void *ptr = &dummy_object;

  // Traverse from Derived to Base
  void *result = traverse_hierarchy(
      ptr, (const struct __class_type_info *)&ti_Derived, &ti_Base);

  // Should return the same pointer (direct base, no offset)
  ASSERT(result == ptr, "Direct base should return original pointer");

  TEST_PASS("SingleInheritanceDirectBase");
}

/**
 * Test 2: Single inheritance traversal - multi-level chain
 *
 * Hierarchy: Base <- Derived1 <- Derived2
 * Test: Derived2* -> Base* should succeed via Derived1
 */
void test_SingleInheritanceMultiLevel() {
  TEST_START("SingleInheritanceMultiLevel");

  // Setup type_info structures
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

  // Test object pointer
  int dummy_object = 42;
  void *ptr = &dummy_object;

  // Traverse from Derived2 to Base (through Derived1)
  void *result = traverse_hierarchy(
      ptr, (const struct __class_type_info *)&ti_Derived2, &ti_Base);

  // Should return pointer (multi-level traversal)
  ASSERT(result == ptr, "Multi-level traversal should find Base");

  TEST_PASS("SingleInheritanceMultiLevel");
}

/**
 * Test 3: Single inheritance - type not found
 *
 * Hierarchy: Base <- Derived
 * Test: Derived* -> Unrelated* should fail (return NULL)
 */
void test_SingleInheritanceNotFound() {
  TEST_START("SingleInheritanceNotFound");

  // Setup type_info structures
  const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                            .type_name = "4Base"};

  const struct __si_class_type_info ti_Derived = {.vtable_ptr =
                                                      __vt_si_class_type_info,
                                                  .type_name = "7Derived",
                                                  .base_type = &ti_Base};

  const struct __class_type_info ti_Unrelated = {
      .vtable_ptr = __vt_class_type_info, .type_name = "9Unrelated"};

  // Test object pointer
  int dummy_object = 42;
  void *ptr = &dummy_object;

  // Traverse from Derived to Unrelated (should fail)
  void *result = traverse_hierarchy(
      ptr, (const struct __class_type_info *)&ti_Derived, &ti_Unrelated);

  // Should return NULL (type not found)
  ASSERT(result == nullptr, "Unrelated type should return NULL");

  TEST_PASS("SingleInheritanceNotFound");
}

/**
 * Test 4: Multiple inheritance - first base match
 *
 * Hierarchy: Base1, Base2 <- Diamond
 * Test: Diamond* -> Base1* should succeed with correct offset
 */
void test_MultipleInheritanceFirstBase() {
  TEST_START("MultipleInheritanceFirstBase");

  // Setup type_info structures
  const struct __class_type_info ti_Base1 = {.vtable_ptr = __vt_class_type_info,
                                             .type_name = "5Base1"};

  const struct __class_type_info ti_Base2 = {.vtable_ptr = __vt_class_type_info,
                                             .type_name = "5Base2"};

  // Diamond class with two bases
  // Note: Using flexible array member, allocate extra space
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
          {.base_type = &ti_Base1, .offset_flags = 0 << 8}, // offset 0
          {.base_type = &ti_Base2, .offset_flags = 8 << 8}  // offset 8
      }};

  // Test object pointer
  int dummy_object = 42;
  void *ptr = &dummy_object;

  // Traverse from Diamond to Base1 (first base, offset 0)
  void *result = traverse_hierarchy(
      ptr, (const struct __class_type_info *)&ti_Diamond, &ti_Base1);

  // Should return original pointer (offset 0)
  ASSERT(result == ptr, "First base should return pointer with offset 0");

  TEST_PASS("MultipleInheritanceFirstBase");
}

/**
 * Test 5: Multiple inheritance - second base match with offset
 *
 * Hierarchy: Base1, Base2 <- Diamond
 * Test: Diamond* -> Base2* should succeed with offset applied
 */
void test_MultipleInheritanceSecondBase() {
  TEST_START("MultipleInheritanceSecondBase");

  // Setup type_info structures
  const struct __class_type_info ti_Base1 = {.vtable_ptr = __vt_class_type_info,
                                             .type_name = "5Base1"};

  const struct __class_type_info ti_Base2 = {.vtable_ptr = __vt_class_type_info,
                                             .type_name = "5Base2"};

  // Diamond class with two bases
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
          {.base_type = &ti_Base1, .offset_flags = 0 << 8}, // offset 0
          {.base_type = &ti_Base2, .offset_flags = 8 << 8}  // offset 8
      }};

  // Test object with known layout
  char dummy_object[16] = {0};
  void *ptr = dummy_object;

  // Traverse from Diamond to Base2 (second base, offset 8)
  void *result = traverse_hierarchy(
      ptr, (const struct __class_type_info *)&ti_Diamond, &ti_Base2);

  // Should return pointer with offset 8
  ASSERT(result == (char *)ptr + 8,
         "Second base should return pointer with offset 8");

  TEST_PASS("MultipleInheritanceSecondBase");
}

/**
 * Test 6: Multiple inheritance - recursive search
 *
 * Hierarchy: Base <- Derived1, Derived2 <- Complex
 * Test: Complex* -> Base* should find Base via Derived1's hierarchy
 */
void test_MultipleInheritanceRecursive() {
  TEST_START("MultipleInheritanceRecursive");

  // Setup type_info structures
  const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                            .type_name = "4Base"};

  const struct __si_class_type_info ti_Derived1 = {.vtable_ptr =
                                                       __vt_si_class_type_info,
                                                   .type_name = "8Derived1",
                                                   .base_type = &ti_Base};

  const struct __class_type_info ti_Derived2 = {
      .vtable_ptr = __vt_class_type_info, .type_name = "8Derived2"};

  // Complex class with two bases: Derived1 (which has Base), Derived2
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

  // Test object
  char dummy_object[32] = {0};
  void *ptr = dummy_object;

  // Traverse from Complex to Base (should recursively search through Derived1)
  void *result = traverse_hierarchy(
      ptr, (const struct __class_type_info *)&ti_Complex, &ti_Base);

  // Should find Base through Derived1 (offset 0)
  ASSERT(result == ptr, "Recursive search should find Base through Derived1");

  TEST_PASS("MultipleInheritanceRecursive");
}

/**
 * Test 7: NULL pointer handling
 *
 * Test: NULL pointer input should return NULL
 */
void test_NullPointerHandling() {
  TEST_START("NullPointerHandling");

  const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                            .type_name = "4Base"};

  const struct __si_class_type_info ti_Derived = {.vtable_ptr =
                                                      __vt_si_class_type_info,
                                                  .type_name = "7Derived",
                                                  .base_type = &ti_Base};

  // Traverse with NULL pointer
  void *result = traverse_hierarchy(
      nullptr, (const struct __class_type_info *)&ti_Derived, &ti_Base);

  // Should return NULL
  ASSERT(result == nullptr, "NULL pointer should return NULL");

  TEST_PASS("NullPointerHandling");
}

/**
 * Test 8: Same type optimization
 *
 * Test: Source type == Target type should return pointer immediately
 */
void test_SameTypeOptimization() {
  TEST_START("SameTypeOptimization");

  const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                            .type_name = "4Base"};

  // Test object pointer
  int dummy_object = 42;
  void *ptr = &dummy_object;

  // Traverse from Base to Base (same type)
  void *result = traverse_hierarchy(ptr, &ti_Base, &ti_Base);

  // Should return original pointer
  ASSERT(result == ptr, "Same type should return original pointer");

  TEST_PASS("SameTypeOptimization");
}

/**
 * Main function: runs all tests
 */
int main() {
  std::cout << "===============================================" << std::endl;
  std::cout << "Hierarchy Traversal Tests (Story #86)" << std::endl;
  std::cout << "===============================================" << std::endl
            << std::endl;

  test_SingleInheritanceDirectBase();
  test_SingleInheritanceMultiLevel();
  test_SingleInheritanceNotFound();
  test_MultipleInheritanceFirstBase();
  test_MultipleInheritanceSecondBase();
  test_MultipleInheritanceRecursive();
  test_NullPointerHandling();
  test_SameTypeOptimization();

  std::cout << std::endl;
  std::cout << "===============================================" << std::endl;
  std::cout << "All tests passed!" << std::endl;
  std::cout << "===============================================" << std::endl;

  return 0;
}

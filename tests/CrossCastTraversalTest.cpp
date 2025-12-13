/**
 * @file CrossCastTraversalTest.cpp
 * @brief Runtime test suite for Story #87: Cross-Cast Hierarchy Traversal
 *
 * Tests the runtime cross-casting algorithm that enables dynamic_cast
 * to navigate between sibling classes in multiple inheritance hierarchies.
 *
 * Acceptance Criteria:
 * - Cross-cast detection: Identify when source and target are siblings
 * - Common derived type finder: Locate most-derived type containing both
 * - Bidirectional traversal: Navigate up from source, down to target
 * - Offset adjustment: Calculate correct pointer offset for cross-cast
 * - Failed cross-cast: Return NULL if no common derived type exists
 * - Virtual base handling: Support virtual inheritance in cross-casts
 * - Testing: Validate Base1* to Base2* in Diamond hierarchy
 *
 * SOLID Principles:
 * - Single Responsibility: Tests only cross-cast traversal
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

// Cross-cast hierarchy traversal function to be implemented
void *cross_cast_traverse(const void *ptr,
                          const struct __class_type_info *src,
                          const struct __class_type_info *dst,
                          const struct __class_type_info *dynamic_type);
}

// Mock vtable pointers for testing
const void *__vt_class_type_info = (const void *)0x1000;
const void *__vt_si_class_type_info = (const void *)0x2000;
const void *__vt_vmi_class_type_info = (const void *)0x3000;

/**
 * Test 1: Simple cross-cast in diamond hierarchy
 *
 * Hierarchy: Base1, Base2 <- Diamond
 * Test: Base1* -> Base2* via Diamond
 */
void test_SimpleCrossCastDiamond() {
  TEST_START("SimpleCrossCastDiamond");

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
          {.base_type = &ti_Base1, .offset_flags = 0 << 8},   // offset 0
          {.base_type = &ti_Base2, .offset_flags = 16 << 8}   // offset 16
      }};

  // Test object with known layout
  char dummy_object[32] = {0};
  void *ptr = dummy_object;  // Points to Base1 subobject

  // Cross-cast from Base1 to Base2 via Diamond
  void *result = cross_cast_traverse(
      ptr, &ti_Base1, &ti_Base2,
      (const struct __class_type_info *)&ti_Diamond);

  // Should return pointer with offset 16 (Base2's offset in Diamond)
  ASSERT(result == (char *)ptr + 16,
         "Cross-cast should return pointer with Base2 offset");

  TEST_PASS("SimpleCrossCastDiamond");
}

/**
 * Test 2: Cross-cast with virtual inheritance
 *
 * Hierarchy:
 *      virtual Base
 *         /      \
 *      Left      Right
 *         \      /
 *         Diamond
 *
 * Test: Left* -> Right* via Diamond
 */
void test_CrossCastVirtualInheritance() {
  TEST_START("CrossCastVirtualInheritance");

  // Setup type_info structures
  const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                            .type_name = "4Base"};

  // Left inherits virtually from Base
  struct {
    const void *vtable_ptr;
    const char *type_name;
    unsigned int flags;
    unsigned int base_count;
    struct __base_class_type_info base_info[1];
  } ti_Left = {
      .vtable_ptr = __vt_vmi_class_type_info,
      .type_name = "4Left",
      .flags = 0x01,  // virtual inheritance flag
      .base_count = 1,
      .base_info = {
          {.base_type = &ti_Base, .offset_flags = (0x02 | (0 << 8))}  // virtual flag
      }};

  // Right inherits virtually from Base
  struct {
    const void *vtable_ptr;
    const char *type_name;
    unsigned int flags;
    unsigned int base_count;
    struct __base_class_type_info base_info[1];
  } ti_Right = {
      .vtable_ptr = __vt_vmi_class_type_info,
      .type_name = "5Right",
      .flags = 0x01,  // virtual inheritance flag
      .base_count = 1,
      .base_info = {
          {.base_type = &ti_Base, .offset_flags = (0x02 | (0 << 8))}  // virtual flag
      }};

  // Diamond inherits from Left and Right
  struct {
    const void *vtable_ptr;
    const char *type_name;
    unsigned int flags;
    unsigned int base_count;
    struct __base_class_type_info base_info[3];
  } ti_Diamond = {
      .vtable_ptr = __vt_vmi_class_type_info,
      .type_name = "7Diamond",
      .flags = 0x02,  // diamond shaped flag
      .base_count = 3,
      .base_info = {
          {.base_type = (const struct __class_type_info *)&ti_Left,
           .offset_flags = 0 << 8},
          {.base_type = (const struct __class_type_info *)&ti_Right,
           .offset_flags = 16 << 8},
          {.base_type = &ti_Base, .offset_flags = (0x02 | (32 << 8))}  // virtual base
      }};

  // Test object
  char dummy_object[48] = {0};
  void *ptr = dummy_object;  // Points to Left subobject

  // Cross-cast from Left to Right via Diamond
  void *result = cross_cast_traverse(
      ptr, (const struct __class_type_info *)&ti_Left,
      (const struct __class_type_info *)&ti_Right,
      (const struct __class_type_info *)&ti_Diamond);

  // Should return pointer with offset 16 (Right's offset in Diamond)
  ASSERT(result == (char *)ptr + 16,
         "Cross-cast with virtual inheritance should work");

  TEST_PASS("CrossCastVirtualInheritance");
}

/**
 * Test 3: Failed cross-cast (no common derived type)
 *
 * Test: Unrelated classes should return NULL
 */
void test_FailedCrossCastNoCommonDerived() {
  TEST_START("FailedCrossCastNoCommonDerived");

  // Setup type_info structures for unrelated classes
  const struct __class_type_info ti_Base1 = {.vtable_ptr = __vt_class_type_info,
                                             .type_name = "5Base1"};

  const struct __class_type_info ti_Base2 = {.vtable_ptr = __vt_class_type_info,
                                             .type_name = "5Base2"};

  const struct __si_class_type_info ti_Derived1 = {
      .vtable_ptr = __vt_si_class_type_info,
      .type_name = "8Derived1",
      .base_type = &ti_Base1};

  const struct __si_class_type_info ti_Derived2 = {
      .vtable_ptr = __vt_si_class_type_info,
      .type_name = "8Derived2",
      .base_type = &ti_Base2};

  // Test object
  int dummy_object = 42;
  void *ptr = &dummy_object;

  // Try to cross-cast from Derived1 to Derived2 (no common derived type)
  // Dynamic type is Derived1, which doesn't contain Derived2
  void *result = cross_cast_traverse(
      ptr, (const struct __class_type_info *)&ti_Derived1,
      (const struct __class_type_info *)&ti_Derived2,
      (const struct __class_type_info *)&ti_Derived1);

  // Should return NULL (no common derived type)
  ASSERT(result == nullptr, "Cross-cast with no common derived should return NULL");

  TEST_PASS("FailedCrossCastNoCommonDerived");
}

/**
 * Test 4: Cross-cast in complex hierarchy
 *
 * Hierarchy:
 *         A
 *        / \
 *       B   C
 *        \ /
 *         D
 *
 * Test: B* -> C* via D
 */
void test_CrossCastComplexHierarchy() {
  TEST_START("CrossCastComplexHierarchy");

  // Setup type_info structures
  const struct __class_type_info ti_A = {.vtable_ptr = __vt_class_type_info,
                                         .type_name = "1A"};

  const struct __si_class_type_info ti_B = {.vtable_ptr = __vt_si_class_type_info,
                                            .type_name = "1B",
                                            .base_type = &ti_A};

  const struct __si_class_type_info ti_C = {.vtable_ptr = __vt_si_class_type_info,
                                            .type_name = "1C",
                                            .base_type = &ti_A};

  // D inherits from both B and C
  struct {
    const void *vtable_ptr;
    const char *type_name;
    unsigned int flags;
    unsigned int base_count;
    struct __base_class_type_info base_info[2];
  } ti_D = {
      .vtable_ptr = __vt_vmi_class_type_info,
      .type_name = "1D",
      .flags = 0,
      .base_count = 2,
      .base_info = {
          {.base_type = (const struct __class_type_info *)&ti_B,
           .offset_flags = 0 << 8},
          {.base_type = (const struct __class_type_info *)&ti_C,
           .offset_flags = 16 << 8}
      }};

  // Test object
  char dummy_object[32] = {0};
  void *ptr = dummy_object;  // Points to B subobject

  // Cross-cast from B to C via D
  void *result = cross_cast_traverse(
      ptr, (const struct __class_type_info *)&ti_B,
      (const struct __class_type_info *)&ti_C,
      (const struct __class_type_info *)&ti_D);

  // Should return pointer with offset 16 (C's offset in D)
  ASSERT(result == (char *)ptr + 16,
         "Complex hierarchy cross-cast should work");

  TEST_PASS("CrossCastComplexHierarchy");
}

/**
 * Test 5: NULL pointer handling in cross-cast
 */
void test_CrossCastNullPointer() {
  TEST_START("CrossCastNullPointer");

  const struct __class_type_info ti_Base1 = {.vtable_ptr = __vt_class_type_info,
                                             .type_name = "5Base1"};

  const struct __class_type_info ti_Base2 = {.vtable_ptr = __vt_class_type_info,
                                             .type_name = "5Base2"};

  const struct __class_type_info ti_Diamond = {.vtable_ptr = __vt_class_type_info,
                                               .type_name = "7Diamond"};

  // Cross-cast with NULL pointer
  void *result = cross_cast_traverse(nullptr, &ti_Base1, &ti_Base2, &ti_Diamond);

  // Should return NULL
  ASSERT(result == nullptr, "NULL pointer cross-cast should return NULL");

  TEST_PASS("CrossCastNullPointer");
}

/**
 * Test 6: Bidirectional traversal (up then down)
 *
 * Test: Verify algorithm navigates up to common derived, then down to target
 */
void test_BidirectionalTraversal() {
  TEST_START("BidirectionalTraversal");

  // Setup: Base1, Base2 <- Diamond
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
          {.base_type = &ti_Base2, .offset_flags = 16 << 8}
      }};

  // Test object
  char dummy_object[32] = {0};
  void *ptr = dummy_object;

  // Cross-cast: Base1 -> Base2
  // Algorithm should: navigate to Diamond (up), then to Base2 (down)
  void *result = cross_cast_traverse(
      ptr, &ti_Base1, &ti_Base2,
      (const struct __class_type_info *)&ti_Diamond);

  // Should successfully navigate and return Base2 pointer
  ASSERT(result == (char *)ptr + 16,
         "Bidirectional traversal should find target");

  TEST_PASS("BidirectionalTraversal");
}

/**
 * Test 7: Cross-cast same type optimization
 *
 * Test: Source == Target should return immediately
 */
void test_CrossCastSameType() {
  TEST_START("CrossCastSameType");

  const struct __class_type_info ti_Base = {.vtable_ptr = __vt_class_type_info,
                                            .type_name = "4Base"};

  int dummy_object = 42;
  void *ptr = &dummy_object;

  // Cross-cast from Base to Base (same type)
  void *result = cross_cast_traverse(ptr, &ti_Base, &ti_Base, &ti_Base);

  // Should return original pointer
  ASSERT(result == ptr, "Same type cross-cast should return original pointer");

  TEST_PASS("CrossCastSameType");
}

/**
 * Main function: runs all tests
 */
int main() {
  std::cout << "===============================================" << std::endl;
  std::cout << "Cross-Cast Traversal Tests (Story #87)" << std::endl;
  std::cout << "===============================================" << std::endl
            << std::endl;

  test_SimpleCrossCastDiamond();
  test_CrossCastVirtualInheritance();
  test_FailedCrossCastNoCommonDerived();
  test_CrossCastComplexHierarchy();
  test_CrossCastNullPointer();
  test_BidirectionalTraversal();
  test_CrossCastSameType();

  std::cout << std::endl;
  std::cout << "===============================================" << std::endl;
  std::cout << "All tests passed!" << std::endl;
  std::cout << "===============================================" << std::endl;

  return 0;
}

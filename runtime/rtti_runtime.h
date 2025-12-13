/**
 * @file rtti_runtime.h
 * @brief Story #86, #87, #88: RTTI Runtime Library Header
 *
 * Complete RTTI runtime library following Itanium C++ ABI specification.
 * Provides type_info structures, hierarchy traversal, dynamic_cast, and
 * type comparison operations.
 *
 * Features:
 * - Story #86: Hierarchy traversal algorithm
 * - Story #87: Cross-cast support
 * - Story #88: Complete dynamic_cast implementation and type comparison
 */

#ifndef RTTI_RUNTIME_H
#define RTTI_RUNTIME_H

#include <stddef.h> /* For ptrdiff_t */

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Base class for all class type_info (Itanium ABI)
 * Used for classes with no inheritance
 */
struct __class_type_info {
  const void *vtable_ptr; /**< Pointer to type_info vtable */
  const char *type_name;  /**< Length-prefixed type name */
};

/**
 * @brief Type info for single inheritance (Itanium ABI)
 * Used for classes with exactly one non-virtual base
 */
struct __si_class_type_info {
  const void *vtable_ptr;                    /**< Pointer to type_info vtable */
  const char *type_name;                     /**< Length-prefixed type name */
  const struct __class_type_info *base_type; /**< Pointer to base type_info */
};

/**
 * @brief Base class type info for multiple/virtual inheritance (Itanium ABI)
 */
struct __base_class_type_info {
  const struct __class_type_info *base_type; /**< Pointer to base type_info */
  long offset_flags; /**< Offset (bits 8+) and flags (bits 0-7) */
};

/**
 * @brief Type info for virtual/multiple inheritance (Itanium ABI)
 * Used for classes with multiple bases or virtual inheritance
 */
struct __vmi_class_type_info {
  const void *vtable_ptr;  /**< Pointer to type_info vtable */
  const char *type_name;   /**< Length-prefixed type name */
  unsigned int flags;      /**< Inheritance flags */
  unsigned int base_count; /**< Number of base classes */
  struct __base_class_type_info
      base_info[1]; /**< Variable-length array of bases */
};

/**
 * @brief External vtable pointers (defined by compiler/runtime)
 */
extern const void *__vt_class_type_info;
extern const void *__vt_si_class_type_info;
extern const void *__vt_vmi_class_type_info;

/**
 * @brief Traverse hierarchy to find target type
 *
 * Recursively walks the inheritance hierarchy from source type to find target.
 * Returns pointer adjusted for base class offset if found, NULL otherwise.
 *
 * @param ptr Pointer to object being cast
 * @param src Source type_info
 * @param dst Target type_info
 * @return Pointer to target type if found, NULL otherwise
 */
void *traverse_hierarchy(const void *ptr, const struct __class_type_info *src,
                         const struct __class_type_info *dst);

/**
 * @brief Cross-cast traverse (Story #87)
 *
 * Performs cross-casting between sibling classes in multiple inheritance.
 * Navigates up from source to common derived type, then down to target.
 *
 * Algorithm:
 * 1. Check if src == dst (same type)
 * 2. Search dynamic_type hierarchy for both src and dst
 * 3. If both found, calculate offset from src to dst via dynamic_type
 * 4. Return adjusted pointer or NULL if cross-cast fails
 *
 * @param ptr Pointer to object being cast
 * @param src Source type_info
 * @param dst Target type_info
 * @param dynamic_type Most-derived (actual) type of the object
 * @return Pointer to target type if found, NULL otherwise
 */
void *cross_cast_traverse(const void *ptr,
                          const struct __class_type_info *src,
                          const struct __class_type_info *dst,
                          const struct __class_type_info *dynamic_type);

/**
 * @brief Complete dynamic_cast implementation (Story #88)
 *
 * Implements full dynamic_cast runtime according to Itanium C++ ABI.
 * Performs runtime type checking and pointer adjustment for all cast types:
 * - Downcasts (Base* -> Derived*)
 * - Upcasts (Derived* -> Base*)
 * - Cross-casts (Left* -> Right* in multiple inheritance)
 * - Identity casts (T* -> T*)
 *
 * Algorithm (Itanium ABI):
 * 1. NULL check: return NULL if sub is NULL
 * 2. Get dynamic type from vtable
 * 3. Fast path: use static offset hint if available (src2dst_offset >= 0)
 * 4. Same type check: if src == dst, return sub
 * 5. Downcast/cross-cast: use hierarchy traversal or cross-cast
 * 6. Return NULL if cast fails
 *
 * @param sub Source pointer (subobject being cast)
 * @param src Static source type (compile-time known)
 * @param dst Destination type (compile-time known)
 * @param src2dst_offset Static offset hint:
 *                       -1 = no hint (downcast/unknown)
 *                       -2 = src is not a public base of dst (cross-cast)
 *                       -3 = src is a multiple public base
 *                       >= 0 = static offset from src to dst (upcast)
 * @return Pointer to destination type if valid, NULL otherwise
 */
void *cxx_dynamic_cast(const void *sub, const struct __class_type_info *src,
                       const struct __class_type_info *dst,
                       ptrdiff_t src2dst_offset);

/**
 * @brief Type comparison - equality (Story #88)
 *
 * Compares two type_info pointers for equality.
 * In flat address spaces (x86-64, ARM64), pointer equality is sufficient
 * because each type has exactly one type_info object globally.
 *
 * @param type1 First type_info
 * @param type2 Second type_info
 * @return 1 if types are equal, 0 otherwise
 */
static inline int type_info_equals(const struct __class_type_info *type1,
                                   const struct __class_type_info *type2) {
  return type1 == type2;
}

/**
 * @brief Type comparison - inequality (Story #88)
 *
 * Compares two type_info pointers for inequality.
 *
 * @param type1 First type_info
 * @param type2 Second type_info
 * @return 1 if types are not equal, 0 otherwise
 */
static inline int type_info_not_equals(const struct __class_type_info *type1,
                                       const struct __class_type_info *type2) {
  return type1 != type2;
}

#ifdef __cplusplus
}
#endif

#endif /* RTTI_RUNTIME_H */

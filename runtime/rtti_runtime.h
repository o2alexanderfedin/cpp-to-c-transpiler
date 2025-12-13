/**
 * @file rtti_runtime.h
 * @brief Story #86: Hierarchy Traversal Algorithm Header
 *
 * Defines runtime structures and functions for RTTI hierarchy traversal.
 * Follows Itanium C++ ABI specification for type_info structures.
 */

#ifndef RTTI_RUNTIME_H
#define RTTI_RUNTIME_H

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

#ifdef __cplusplus
}
#endif

#endif /* RTTI_RUNTIME_H */

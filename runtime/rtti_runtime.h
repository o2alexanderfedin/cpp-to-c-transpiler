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

// ============================================================================
// ACSL Predicate Definitions for RTTI Formal Verification
// ============================================================================

/*@ predicate valid_type_info(struct __class_type_info *t) =
        \valid_read(t) &&
        \valid_read(t->type_name);
*/

/*@ predicate valid_si_type_info(struct __si_class_type_info *t) =
        \valid_read(t) &&
        \valid_read(t->type_name) &&
        (t->base_type == \null || valid_type_info((struct __class_type_info*)t->base_type));
*/

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
/*@ requires valid_src: valid_type_info((struct __class_type_info*)src);
    requires valid_dst: valid_type_info((struct __class_type_info*)dst);
    requires valid_ptr: ptr == \null || \valid_read((char*)ptr);
    ensures null_preserving: ptr == \null ==> \result == \null;
    ensures same_type: src == dst ==> \result == (void*)ptr;
    ensures valid_result: \result == \null || \valid_read((char*)\result);
    assigns \result \from ptr, src, dst, *(struct __si_class_type_info*)src, *(struct __vmi_class_type_info*)src;
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
/*@ requires valid_src: valid_type_info((struct __class_type_info*)src);
    requires valid_dst: valid_type_info((struct __class_type_info*)dst);
    requires valid_dynamic: valid_type_info((struct __class_type_info*)dynamic_type);
    requires valid_ptr: ptr == \null || \valid_read((char*)ptr);
    ensures null_preserving: ptr == \null ==> \result == \null;
    ensures same_type: src == dst ==> \result == (void*)ptr;
    ensures valid_result: \result == \null || \valid_read((char*)\result);
    assigns \result \from ptr, src, dst, dynamic_type, *(struct __vmi_class_type_info*)dynamic_type;
*/
void *cross_cast_traverse(const void *ptr,
                          const struct __class_type_info *src,
                          const struct __class_type_info *dst,
                          const struct __class_type_info *dynamic_type);

/**
 * @brief C++ dynamic_cast runtime support (Story #111)
 *
 * Main entry point for dynamic_cast<T> operations. Performs runtime type
 * checking and returns appropriately cast pointer or NULL if cast fails.
 *
 * This function provides the core runtime support for C++ dynamic_cast,
 * ensuring type safety at runtime through RTTI hierarchy traversal.
 *
 * @param ptr Pointer to object being cast
 * @param src Source type_info (static type of ptr)
 * @param dst Target type_info (requested cast type)
 * @return Pointer to target type if cast is valid, NULL otherwise
 */
/*@ requires valid_src: valid_type_info((struct __class_type_info*)src);
    requires valid_dst: valid_type_info((struct __class_type_info*)dst);
    requires valid_ptr: ptr == \null || \valid_read((char*)ptr);
    ensures null_preserving: ptr == \null ==> \result == \null;
    ensures same_type: src == dst ==> \result == (void*)ptr;
    ensures valid_result: \result == \null || \valid_read((char*)\result);
    assigns \result \from ptr, src, dst, *(struct __si_class_type_info*)src, *(struct __vmi_class_type_info*)src;
*/
void *cxx_dynamic_cast(const void *ptr,
                       const struct __class_type_info *src,
                       const struct __class_type_info *dst);

#ifdef __cplusplus
}
#endif

#endif /* RTTI_RUNTIME_H */

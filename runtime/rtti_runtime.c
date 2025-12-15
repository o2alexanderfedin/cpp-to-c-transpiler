/**
 * @file rtti_runtime.c
 * @brief Story #86 & #87: Hierarchy Traversal Algorithm Implementation
 *
 * Implements runtime hierarchy traversal for dynamic_cast support.
 * Walks inheritance hierarchies (single and multiple) to determine cast
 * validity. Includes cross-casting support for sibling classes.
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only handles hierarchy traversal
 * - Open/Closed: Extensible for new type_info variants
 * - Interface Segregation: Minimal runtime API
 * - Dependency Inversion: Depends on Itanium ABI abstractions
 *
 * Design Pattern: libcxxabi hierarchy traversal algorithm
 *
 * Story #87 Extensions:
 * - find_type_offset: Helper for finding type offset in hierarchy
 * - cross_cast_traverse: Cross-casting between sibling classes
 */

#include "rtti_runtime.h"
#include <stddef.h>

/**
 * @brief Traverse hierarchy to find target type
 *
 * Recursively walks the inheritance hierarchy from source type to find target.
 * Handles both single inheritance (__si_class_type_info) and multiple/virtual
 * inheritance (__vmi_class_type_info).
 *
 * Algorithm:
 * 1. Check if source == target (same type optimization)
 * 2. If single inheritance: check direct base, recurse if needed
 * 3. If multiple inheritance: check all bases with offsets, recurse
 * 4. Return NULL if target not found
 *
 * @param ptr Pointer to object being cast
 * @param src Source type_info
 * @param dst Target type_info
 * @return Pointer to target type if found, NULL otherwise
 */
void *traverse_hierarchy(const void *ptr, const struct __class_type_info *src,
                         const struct __class_type_info *dst) {
  // NULL pointer check
  if (ptr == NULL || src == NULL || dst == NULL) {
    return NULL;
  }

  // Same type optimization: if src == dst, return immediately
  if (src == dst) {
    return (void *)ptr;
  }

  // Single inheritance: __si_class_type_info
  if (src->vtable_ptr == __vt_si_class_type_info) {
    const struct __si_class_type_info *si_src =
        (const struct __si_class_type_info *)src;

    // Check if direct base matches target
    if (si_src->base_type == dst) {
      return (void *)ptr;
    }

    // Recursively check base's hierarchy
    return traverse_hierarchy(ptr, si_src->base_type, dst);
  }

  // Multiple/virtual inheritance: __vmi_class_type_info
  if (src->vtable_ptr == __vt_vmi_class_type_info) {
    const struct __vmi_class_type_info *vmi_src =
        (const struct __vmi_class_type_info *)src;

    // Iterate through all base classes
    /*@ loop invariant 0 <= i <= vmi_src->base_count;
        loop invariant \valid_read(vmi_src);
        loop invariant \valid_read(vmi_src->base_info + (0 .. vmi_src->base_count - 1));
        loop assigns i;
        loop variant vmi_src->base_count - i;
    */
    for (unsigned i = 0; i < vmi_src->base_count; i++) {
      const struct __base_class_type_info *base = &vmi_src->base_info[i];

      // Check if this base matches target
      if (base->base_type == dst) {
        // Found: apply offset
        ptrdiff_t offset = base->offset_flags >> 8;
        /*@ assert \valid_read((char*)ptr + offset); */
        return (char *)ptr + offset;
      }

      // Recursively check this base's hierarchy
      ptrdiff_t offset = base->offset_flags >> 8;
      /*@ assert \valid_read((char*)ptr + offset); */
      void *result =
          traverse_hierarchy((char *)ptr + offset, base->base_type, dst);

      if (result != NULL) {
        return result;
      }
    }
  }

  // Target not found in hierarchy
  return NULL;
}

/**
 * @brief Helper to find type in hierarchy and return offset
 *
 * Searches for target type in source hierarchy and returns offset if found.
 *
 * @param src Source type_info to search
 * @param target Target type_info to find
 * @param offset_out Output parameter for offset (set to 0 if found at same level)
 * @return 1 if found, 0 if not found
 */
/*@ requires \valid(offset_out);
    requires src == \null || \valid_read(src);
    requires target == \null || \valid_read(target);
    assigns *offset_out;
    ensures \result == 0 || \result == 1;
    ensures (src == \null || target == \null) ==> \result == 0;
    ensures (src == target) ==> (\result == 1 && *offset_out == 0);
*/
static int find_type_offset(const struct __class_type_info *src,
                            const struct __class_type_info *target,
                            ptrdiff_t *offset_out) {
  // NULL check
  if (src == NULL || target == NULL) {
    return 0;
  }

  // Same type: offset is 0
  if (src == target) {
    *offset_out = 0;
    return 1;
  }

  // Single inheritance: __si_class_type_info
  if (src->vtable_ptr == __vt_si_class_type_info) {
    const struct __si_class_type_info *si_src =
        (const struct __si_class_type_info *)src;

    // Check if direct base matches target
    if (si_src->base_type == target) {
      *offset_out = 0;  // No offset for single inheritance
      return 1;
    }

    // Recursively check base's hierarchy
    return find_type_offset(si_src->base_type, target, offset_out);
  }

  // Multiple/virtual inheritance: __vmi_class_type_info
  if (src->vtable_ptr == __vt_vmi_class_type_info) {
    const struct __vmi_class_type_info *vmi_src =
        (const struct __vmi_class_type_info *)src;

    // Iterate through all base classes
    /*@ loop invariant 0 <= i <= vmi_src->base_count;
        loop invariant \valid_read(vmi_src);
        loop invariant \valid_read(vmi_src->base_info + (0 .. vmi_src->base_count - 1));
        loop invariant \valid(offset_out);
        loop assigns i, *offset_out;
        loop variant vmi_src->base_count - i;
    */
    for (unsigned i = 0; i < vmi_src->base_count; i++) {
      const struct __base_class_type_info *base = &vmi_src->base_info[i];

      // Check if this base matches target
      if (base->base_type == target) {
        // Found: extract offset
        *offset_out = base->offset_flags >> 8;
        return 1;
      }

      // Recursively check this base's hierarchy
      ptrdiff_t base_offset = base->offset_flags >> 8;
      ptrdiff_t sub_offset;
      if (find_type_offset(base->base_type, target, &sub_offset)) {
        *offset_out = base_offset + sub_offset;
        return 1;
      }
    }
  }

  // Target not found
  return 0;
}

/**
 * @brief Cross-cast traverse (Story #87)
 *
 * Performs cross-casting between sibling classes in multiple inheritance.
 * Navigates up from source to common derived type, then down to target.
 *
 * Algorithm:
 * 1. Check if src == dst (same type optimization)
 * 2. Find src in dynamic_type hierarchy (get src_offset)
 * 3. Find dst in dynamic_type hierarchy (get dst_offset)
 * 4. If both found: return ptr - src_offset + dst_offset
 * 5. Otherwise: return NULL (cross-cast fails)
 *
 * @param ptr Pointer to object being cast (points to src subobject)
 * @param src Source type_info
 * @param dst Target type_info
 * @param dynamic_type Most-derived (actual) type of the object
 * @return Pointer to target type if found, NULL otherwise
 */
void *cross_cast_traverse(const void *ptr,
                          const struct __class_type_info *src,
                          const struct __class_type_info *dst,
                          const struct __class_type_info *dynamic_type) {
  // NULL pointer check
  if (ptr == NULL || src == NULL || dst == NULL || dynamic_type == NULL) {
    return NULL;
  }

  // Same type optimization: if src == dst, return immediately
  if (src == dst) {
    return (void *)ptr;
  }

  // Step 1: Find source type in dynamic_type hierarchy
  ptrdiff_t src_offset;
  int src_found = find_type_offset(dynamic_type, src, &src_offset);

  if (!src_found) {
    // Source not found in dynamic_type - should not happen, but be defensive
    return NULL;
  }

  // Step 2: Find destination type in dynamic_type hierarchy
  ptrdiff_t dst_offset;
  int dst_found = find_type_offset(dynamic_type, dst, &dst_offset);

  if (!dst_found) {
    // Destination not found in dynamic_type - cross-cast fails
    return NULL;
  }

  // Step 3: Calculate cross-cast offset
  // ptr points to src subobject at offset src_offset from dynamic_type base
  // We need to return pointer to dst subobject at offset dst_offset from dynamic_type base
  //
  // dynamic_type base is at: ptr - src_offset
  // dst subobject is at: (ptr - src_offset) + dst_offset
  // Simplified: ptr + (dst_offset - src_offset)

  ptrdiff_t cross_offset = dst_offset - src_offset;
  return (char *)ptr + cross_offset;
}

/**
 * @brief C++ dynamic_cast runtime support (Story #111)
 *
 * Main entry point for dynamic_cast<T> operations. Performs runtime type
 * checking and returns appropriately cast pointer or NULL if cast fails.
 *
 * This function provides the core runtime support for C++ dynamic_cast,
 * ensuring type safety at runtime through RTTI hierarchy traversal.
 *
 * Algorithm:
 * 1. Check if ptr == NULL (null-preserving)
 * 2. Check if src == dst (same-type shortcut)
 * 3. Delegate to traverse_hierarchy for actual hierarchy walk
 * 4. Return result (adjusted pointer or NULL)
 *
 * @param ptr Pointer to object being cast
 * @param src Source type_info (static type of ptr)
 * @param dst Target type_info (requested cast type)
 * @return Pointer to target type if cast is valid, NULL otherwise
 */
void *cxx_dynamic_cast(const void *ptr,
                       const struct __class_type_info *src,
                       const struct __class_type_info *dst) {
  // NULL pointer check - null-preserving property
  if (ptr == NULL) {
    return NULL;
  }

  // NULL type_info check - defensive
  if (src == NULL || dst == NULL) {
    return NULL;
  }

  // Same type shortcut optimization
  if (src == dst) {
    return (void *)ptr;
  }

  // Delegate to hierarchy traversal
  // This handles single inheritance, multiple inheritance, and virtual bases
  return traverse_hierarchy(ptr, src, dst);
}

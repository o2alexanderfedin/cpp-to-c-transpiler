/**
 * @file rtti_runtime.c
 * @brief Story #86: Hierarchy Traversal Algorithm Implementation
 *
 * Implements runtime hierarchy traversal for dynamic_cast support.
 * Walks inheritance hierarchies (single and multiple) to determine cast
 * validity.
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only handles hierarchy traversal
 * - Open/Closed: Extensible for new type_info variants
 * - Interface Segregation: Minimal runtime API
 * - Dependency Inversion: Depends on Itanium ABI abstractions
 *
 * Design Pattern: libcxxabi hierarchy traversal algorithm
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
    for (unsigned i = 0; i < vmi_src->base_count; i++) {
      const struct __base_class_type_info *base = &vmi_src->base_info[i];

      // Check if this base matches target
      if (base->base_type == dst) {
        // Found: apply offset
        ptrdiff_t offset = base->offset_flags >> 8;
        return (char *)ptr + offset;
      }

      // Recursively check this base's hierarchy
      ptrdiff_t offset = base->offset_flags >> 8;
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

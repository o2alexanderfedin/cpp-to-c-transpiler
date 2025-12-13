/**
 * @file rtti_runtime.c
 * @brief Story #86, #87, #88: Complete RTTI Runtime Library
 *
 * Complete implementation of RTTI runtime following Itanium C++ ABI.
 * Provides hierarchy traversal, cross-casting, and full dynamic_cast support.
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Focused on RTTI type checking and casting
 * - Open/Closed: Extensible for new type_info variants
 * - Interface Segregation: Minimal runtime API
 * - Dependency Inversion: Depends on Itanium ABI abstractions
 *
 * Design Pattern: libcxxabi RTTI implementation
 *
 * Features:
 * - Story #86: Hierarchy traversal algorithm
 * - Story #87: Cross-cast support for multiple inheritance
 * - Story #88: Complete cxx_dynamic_cast implementation
 */

#include "rtti_runtime.h"
#include <stddef.h>

/**
 * @brief Vtable markers for type_info types (Story #88)
 *
 * These markers distinguish between different type_info variants.
 * They are used to determine the inheritance pattern at runtime.
 *
 * Note: These are dummy values - only their addresses matter.
 * Each type_info structure's vtable_ptr points to one of these.
 *
 * These are defined as weak symbols to allow tests to override them.
 */
__attribute__((weak)) const int __vt_class_type_info_marker = 0;
__attribute__((weak)) const int __vt_si_class_type_info_marker = 1;
__attribute__((weak)) const int __vt_vmi_class_type_info_marker = 2;

__attribute__((weak)) const void *__vt_class_type_info = &__vt_class_type_info_marker;
__attribute__((weak)) const void *__vt_si_class_type_info = &__vt_si_class_type_info_marker;
__attribute__((weak)) const void *__vt_vmi_class_type_info = &__vt_vmi_class_type_info_marker;

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

  // No inheritance: __class_type_info (leaf class)
  if (src->vtable_ptr == __vt_class_type_info) {
    // No bases to check
    return NULL;
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
 * @brief Vtable structure (matches the vtable layout in generated code)
 *
 * This structure definition is used to extract type_info from objects.
 * It must match the vtable layout used by the compiler.
 */
struct __vtable_layout {
  ptrdiff_t offset_to_top;               /**< Offset to most-derived object */
  const struct __class_type_info *type_info; /**< RTTI type information */
  void (*virtual_functions[])();         /**< Virtual function pointers */
};

/**
 * @brief Complete dynamic_cast implementation (Story #88)
 *
 * Implements full dynamic_cast runtime according to Itanium C++ ABI.
 * Handles all cast scenarios: downcasts, upcasts, cross-casts, and identity.
 *
 * Algorithm (Itanium ABI __dynamic_cast):
 * 1. NULL check: return NULL if sub is NULL
 * 2. Get dynamic (most-derived) type from object's vtable
 * 3. Fast path: if src2dst_offset >= 0 (upcast hint), use static offset
 * 4. Same type check: if src == dst, return sub (identity cast)
 * 5. Downcast: traverse from dynamic_type down to dst
 * 6. Cross-cast: use cross_cast_traverse for sibling types
 * 7. Return NULL if cast fails
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
                       ptrdiff_t src2dst_offset) {
  // Step 1: NULL pointer check
  if (sub == NULL || src == NULL || dst == NULL) {
    return NULL;
  }

  // Step 2: Get dynamic (most-derived) type from vtable
  // Object's first pointer is vtable pointer
  const struct __vtable_layout *vtable =
      *(const struct __vtable_layout **)sub;
  const struct __class_type_info *dynamic_type = vtable->type_info;

  // Step 3: Fast path - upcast with static offset hint
  // If src2dst_offset >= 0, the compiler knows this is an upcast with a known
  // offset This is an optimization for common upcasts (Derived* -> Base*)
  if (src2dst_offset >= 0) {
    // For upcasts, we just need to verify that dst is a base of src
    // (or dynamic_type is compatible with dst)
    // The offset tells us how to adjust the pointer
    // Verify: dst is a base of dynamic_type (so cast is valid)
    if (traverse_hierarchy(sub, src, dst) != NULL) {
      // Use the static offset hint for efficiency
      return (char *)sub + src2dst_offset;
    }
    // If hierarchy check fails, fall through to slow path
  }

  // Step 4: Same type check (identity cast)
  if (src == dst) {
    return (void *)sub;
  }

  // Step 5: Downcast - traverse from dynamic_type to dst
  // This handles: Base* -> Derived* where object is actually Derived
  // Also handles "upcasts" where we search from derived dynamic_type to base dst
  void *downcast_result = traverse_hierarchy(sub, dynamic_type, dst);
  if (downcast_result != NULL) {
    return downcast_result;
  }

  // Step 6: Cross-cast - for sibling classes in multiple inheritance
  // Hint: src2dst_offset == -2 means src is not a base of dst (cross-cast)
  if (src2dst_offset == -2) {
    // Use cross-cast traversal
    void *crosscast_result =
        cross_cast_traverse(sub, src, dst, dynamic_type);
    if (crosscast_result != NULL) {
      return crosscast_result;
    }
  }

  // Step 7: Cast failed - no valid path from src to dst
  return NULL;
}

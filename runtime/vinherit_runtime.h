// vinherit_runtime.h - Virtual inheritance runtime library header
// Story #116: Implement Inline Runtime Mode
//
// This header provides runtime support for virtual inheritance including
// virtual base tables and offset calculation.
//
// SOLID Principles:
//   - Single Responsibility: Provides virtual inheritance runtime interface
//   - Interface Segregation: Clean, minimal API for virtual inheritance
//   - Dependency Inversion: Depends on standard C library abstractions

#ifndef __VINHERIT_RUNTIME_H__
#define __VINHERIT_RUNTIME_H__

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

// ============================================================================
// Virtual Inheritance Data Structures
// ============================================================================

/// @brief Virtual base table entry
///
/// Each entry describes one virtual base class, including its offset
/// from the derived class object and the class type information.
struct __cxx_virtual_base_entry {
  ptrdiff_t offset;        ///< Offset to virtual base from derived object
  const void *type_info;   ///< Type information for virtual base class
};

/// @brief Virtual base table
///
/// Table containing all virtual bases for a class. Used at runtime to
/// calculate correct offsets for virtual inheritance casts.
struct __cxx_virtual_base_table {
  size_t count;                              ///< Number of virtual bases
  struct __cxx_virtual_base_entry entries[]; ///< Virtual base entries (flexible array)
};

// ============================================================================
// ACSL Predicate Definitions for Formal Verification
// ============================================================================

/*@ predicate valid_vbase_entry(struct __cxx_virtual_base_entry *e) =
        \valid_read(e) &&
        e->type_info != \null &&
        \valid_read((char*)e->type_info);
*/

/*@ predicate valid_vbase_table(struct __cxx_virtual_base_table *t) =
        \valid_read(t) &&
        t->count >= 0 &&
        \valid_read(&t->entries[0..t->count-1]) &&
        (\forall integer i; 0 <= i < t->count ==> valid_vbase_entry(&t->entries[i]));
*/

// ============================================================================
// Runtime Functions
// ============================================================================

/// @brief Calculate virtual base offset
///
/// Looks up the offset to a virtual base class in the virtual base table.
/// Returns the offset if found, or 0 if not found.
///
/// @param table Virtual base table for the derived class
/// @param base_type Type information for the virtual base being sought
/// @return Offset to virtual base, or 0 if not found
///
/*@ requires valid_table: valid_vbase_table(table);
    requires valid_type: base_type != \null && \valid_read((char*)base_type);
    ensures valid_offset: \result >= 0;
    assigns \nothing;
*/
static inline ptrdiff_t __cxx_get_virtual_base_offset(
    const struct __cxx_virtual_base_table *table,
    const void *base_type) {

  if (!table || !base_type) return 0;

  // Linear search through virtual base entries
  for (size_t i = 0; i < table->count; i++) {
    if (table->entries[i].type_info == base_type) {
      return table->entries[i].offset;
    }
  }

  return 0; // Virtual base not found
}

/// @brief Adjust pointer for virtual base access
///
/// Adjusts a derived class pointer to point to a virtual base subobject
/// using the virtual base table.
///
/// @param derived Pointer to derived class object
/// @param table Virtual base table for the derived class
/// @param base_type Type information for the virtual base
/// @return Pointer to virtual base subobject, or NULL if not found
///
/*@ requires valid_table: valid_vbase_table(table);
    requires valid_type: base_type != \null && \valid_read((char*)base_type);
    requires valid_ptr: derived == \null || \valid_read((char*)derived);
    ensures null_preserving: derived == \null ==> \result == \null;
    ensures valid_result: \result == \null || \valid_read((char*)\result);
    assigns \nothing;
*/
static inline void *__cxx_adjust_to_virtual_base(
    void *derived,
    const struct __cxx_virtual_base_table *table,
    const void *base_type) {

  if (!derived || !table) return NULL;

  ptrdiff_t offset = __cxx_get_virtual_base_offset(table, base_type);
  if (offset == 0) return NULL; // Not found

  // Adjust pointer by offset
  return (void*)((char*)derived + offset);
}

#ifdef __cplusplus
}
#endif

#endif // __VINHERIT_RUNTIME_H__

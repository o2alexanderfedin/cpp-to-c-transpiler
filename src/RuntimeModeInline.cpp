// RuntimeModeInline.cpp - Inline runtime mode implementation
// Story #116: Implement Inline Runtime Mode
//
// TDD GREEN Phase: Full implementation
//
// This implementation embeds runtime code directly into generated C files
// for zero-dependency, self-contained output suitable for embedded systems
// and safety-critical applications.
//
// NOTE: Runtime code is embedded as string literals to avoid path dependencies

#include "RuntimeModeInline.h"
#include <sstream>

// Constructor - minimal initialization
RuntimeModeInline::RuntimeModeInline() {
  // Empty for now - will populate used features based on AST analysis
}

// Check if inline mode is active
bool RuntimeModeInline::isInlineMode() const {
  return true; // GREEN: Always true for inline mode
}

// Mark a runtime feature as used
void RuntimeModeInline::markFeatureUsed(RuntimeFeature feature) {
  usedFeatures_.insert(feature); // GREEN: Add feature to set
}

// Embed exception handling runtime code
std::string RuntimeModeInline::embedExceptionRuntime() const {
  // Embedded exception runtime code
  const char* exceptionRuntime = R"(
// Exception handling runtime - embedded inline

struct __cxx_action_entry {
  void (*destructor)(void *);
  void *object;
};

struct __cxx_exception_frame {
  jmp_buf jmpbuf;
  struct __cxx_exception_frame *next;
  const struct __cxx_action_entry *actions;
  void *exception_object;
  const char *exception_type;
};

#ifdef __cplusplus
extern thread_local struct __cxx_exception_frame *__cxx_exception_stack;
#else
extern _Thread_local struct __cxx_exception_frame *__cxx_exception_stack;
#endif

void __cxx_throw(void *exception, const char *type_info);
void __cxx_begin_catch(void);
void __cxx_end_catch(void);
)";

  std::stringstream result;
  result << "#ifndef __EXCEPTION_RUNTIME_INLINE_H__\n";
  result << "#define __EXCEPTION_RUNTIME_INLINE_H__\n\n";
  result << exceptionRuntime;
  result << "\n#endif // __EXCEPTION_RUNTIME_INLINE_H__\n";

  return result.str();
}

// Embed RTTI (Runtime Type Information) code
std::string RuntimeModeInline::embedRTTIRuntime() const {
  // Embedded RTTI runtime code
  const char* rttiRuntime = R"(
// RTTI runtime - embedded inline

struct __cxx_type_info {
  const void *vtable_ptr;
  const char *type_name;
};

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

void *__cxx_dynamic_cast(const void *ptr,
                         const struct __class_type_info *src,
                         const struct __class_type_info *dst,
                         ptrdiff_t offset);

void *traverse_hierarchy(const void *ptr,
                         const struct __class_type_info *src,
                         const struct __class_type_info *dst);
)";

  std::stringstream result;
  result << "#ifndef __RTTI_RUNTIME_INLINE_H__\n";
  result << "#define __RTTI_RUNTIME_INLINE_H__\n\n";
  result << rttiRuntime;
  result << "\n#endif // __RTTI_RUNTIME_INLINE_H__\n";

  return result.str();
}

// Embed memory management runtime code
std::string RuntimeModeInline::embedMemoryRuntime() const {
  // Embedded memory runtime code
  const char* memoryRuntime = R"(
// Memory management runtime - embedded inline

static inline void *__cxx_allocate(size_t size, size_t alignment) {
  void *ptr = malloc(size + alignment);
  if (!ptr) return NULL;

  size_t addr = (size_t)ptr;
  size_t aligned = (addr + alignment - 1) & ~(alignment - 1);
  return (void*)aligned;
}

static inline void __cxx_deallocate(void *ptr) {
  if (ptr) {
    free(ptr);
  }
}

static inline void __cxx_zero_memory(void *ptr, size_t size) {
  memset(ptr, 0, size);
}
)";

  std::stringstream result;
  result << "#ifndef __MEMORY_RUNTIME_INLINE_H__\n";
  result << "#define __MEMORY_RUNTIME_INLINE_H__\n\n";
  result << memoryRuntime;
  result << "\n#endif // __MEMORY_RUNTIME_INLINE_H__\n";

  return result.str();
}

// Embed virtual inheritance runtime code
std::string RuntimeModeInline::embedVInheritRuntime() const {
  // Embedded virtual inheritance runtime code
  const char* vinheritRuntime = R"(
// Virtual inheritance runtime - embedded inline

struct __cxx_virtual_base_entry {
  ptrdiff_t offset;
  const void *type_info;
};

struct __cxx_virtual_base_table {
  size_t count;
  struct __cxx_virtual_base_entry entries[];
};

static inline ptrdiff_t __cxx_get_virtual_base_offset(
    const struct __cxx_virtual_base_table *table,
    const void *base_type) {

  if (!table || !base_type) return 0;

  for (size_t i = 0; i < table->count; i++) {
    if (table->entries[i].type_info == base_type) {
      return table->entries[i].offset;
    }
  }

  return 0;
}

static inline void *__cxx_adjust_to_virtual_base(
    void *derived,
    const struct __cxx_virtual_base_table *table,
    const void *base_type) {

  if (!derived || !table) return NULL;

  ptrdiff_t offset = __cxx_get_virtual_base_offset(table, base_type);
  if (offset == 0) return NULL;

  return (void*)((char*)derived + offset);
}
)";

  std::stringstream result;
  result << "#ifndef __VINHERIT_RUNTIME_INLINE_H__\n";
  result << "#define __VINHERIT_RUNTIME_INLINE_H__\n\n";
  result << vinheritRuntime;
  result << "\n#endif // __VINHERIT_RUNTIME_INLINE_H__\n";

  return result.str();
}

// Generate complete inline runtime for all used features
std::string RuntimeModeInline::generateInlineRuntime() const {
  // GREEN: Combine runtime code for all marked features
  std::stringstream result;

  // Add header comment
  result << "// Inline Runtime Code - Generated by cpptoc\n";
  result << "// Only includes runtime features used in this translation unit\n\n";

  // Include standard library headers needed by runtime
  result << "#include <setjmp.h>\n";
  result << "#include <stddef.h>\n";
  result << "#include <stdlib.h>\n";
  result << "#include <string.h>\n\n";

  // Embed each used feature's runtime code
  if (usedFeatures_.count(RuntimeFeature::Exceptions) > 0) {
    result << embedExceptionRuntime() << "\n\n";
  }

  if (usedFeatures_.count(RuntimeFeature::RTTI) > 0) {
    result << embedRTTIRuntime() << "\n\n";
  }

  if (usedFeatures_.count(RuntimeFeature::Memory) > 0) {
    result << embedMemoryRuntime() << "\n\n";
  }

  if (usedFeatures_.count(RuntimeFeature::VInherit) > 0) {
    result << embedVInheritRuntime() << "\n\n";
  }

  return result.str();
}

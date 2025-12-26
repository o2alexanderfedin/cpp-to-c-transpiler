// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/unit/smart_pointers/RaiiIntegrationTest_old.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

void test_unique_ptr_with_file_resource();
void test_shared_ptr_with_file_resource();
void test_unique_ptr_with_raii_buffer();
void test_unique_ptr_with_multiple_raii_resources();
void test_shared_ptr_with_raii_early_return();
void test_unique_ptr_with_mutex_lock();
void test_shared_ptr_with_lock_guard();
void test_unique_ptr_with_recursive_lock();
void test_unique_ptr_with_read_write_lock();
void test_multiple_locks_with_unique_ptr();
void test_unique_ptr_exception_safety_automatic_cleanup();
void test_shared_ptr_exception_safety();
void test_make_unique_exception_safety_vs_constructor();
void test_raii_with_exception_in_constructor();
void test_exception_with_multiple_raii_resources();
void test_exception_safety_with_nested_scopes();
void test_smart_pointer_with_virtual_inheritance_raii();
void test_smart_pointer_in_member_initialization_list();
void test_smart_pointer_move_semantics_in_constructor();
void test_smart_pointer_conditional_cleanup();
void test_smart_pointer_factory_pattern();
void test_shared_pointer_observer_pattern();
void test_smart_pointer_vs_raw_pointer_overhead();
void test_memory_layout_with_smart_pointers();
void test_smart_pointer_cache_locality();
int main();

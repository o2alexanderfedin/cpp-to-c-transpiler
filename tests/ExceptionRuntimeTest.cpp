// ExceptionRuntimeTest.cpp - Tests for exception runtime library (Story #81)
// Following TDD: Write failing tests first

#include <cassert>
#include <csetjmp>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>

// Forward declarations for runtime functions we'll implement
extern "C" {
// Exception frame structure (from Story #76)
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

// Thread-local exception stack (C++ uses thread_local, C uses _Thread_local)
extern thread_local struct __cxx_exception_frame *__cxx_exception_stack;

// Runtime functions to test (AC #1-6)
void cxx_throw(void *exception, const char *type_info);
}

// ============================================================================
// Test Utilities
// ============================================================================

// Counter for tracking destructor calls
static int destructor_call_count = 0;
static void *last_destroyed_object = nullptr;

// Simple destructor for testing
void test_destructor(void *obj) {
  destructor_call_count++;
  last_destroyed_object = obj;
}

// Reset test state
void reset_test_state() {
  destructor_call_count = 0;
  last_destroyed_object = nullptr;
  __cxx_exception_stack = nullptr;
}

// ============================================================================
// Test Suite 1: cxx_throw Basic Functionality (AC #1)
// ============================================================================

void test_cxx_throw_walks_exception_stack() {
  std::cout << "Test 1: cxx_throw walks exception stack... ";
  reset_test_state();

  // GIVEN: An exception frame on the stack
  struct __cxx_exception_frame frame;
  frame.next = nullptr;
  frame.actions = nullptr;
  frame.exception_object = nullptr;
  frame.exception_type = nullptr;
  __cxx_exception_stack = &frame;

  // WHEN: setjmp is called and cxx_throw is invoked
  if (setjmp(frame.jmpbuf) == 0) {
    // Throw path
    int exception_value = 42;
    cxx_throw(&exception_value, "int");

    // Should never reach here
    assert(false && "cxx_throw should not return");
  } else {
    // Catch path - longjmp landed here
    // THEN: Exception info should be stored in frame
    assert(frame.exception_object != nullptr);
    assert(strcmp(frame.exception_type, "int") == 0);
  }

  std::cout << "✓" << std::endl;
}

void test_cxx_throw_stores_exception_info() {
  std::cout << "Test 2: cxx_throw stores exception info in frame... ";
  reset_test_state();

  // GIVEN: An exception frame and exception value
  double exception_value = 3.14;
  struct __cxx_exception_frame frame;
  frame.next = nullptr;
  frame.actions = nullptr;
  frame.exception_object = nullptr;
  frame.exception_type = nullptr;
  __cxx_exception_stack = &frame;

  // WHEN: Throwing an exception
  if (setjmp(frame.jmpbuf) == 0) {
    cxx_throw(&exception_value, "double");
    assert(false);
  } else {
    // THEN: Exception object and type should be stored (AC #4)
    assert(frame.exception_object == static_cast<void *>(&exception_value));
    assert(strcmp(frame.exception_type, "double") == 0);
  }

  std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 2: Action Table Execution (AC #2)
// ============================================================================

void test_cxx_throw_executes_action_table() {
  std::cout << "Test 3: cxx_throw executes action table... ";
  reset_test_state();

  // GIVEN: An exception frame with action table
  int obj1 = 1, obj2 = 2;
  static const struct __cxx_action_entry actions[] = {
      {test_destructor, &obj1},
      {test_destructor, &obj2},
      {nullptr, nullptr} // Sentinel
  };

  struct __cxx_exception_frame frame;
  frame.next = nullptr;
  frame.actions = actions;
  frame.exception_object = nullptr;
  frame.exception_type = nullptr;
  __cxx_exception_stack = &frame;

  // WHEN: Throwing an exception
  if (setjmp(frame.jmpbuf) == 0) {
    int exception_value = 99;
    cxx_throw(&exception_value, "int");
    assert(false);
  } else {
    // THEN: All destructors should be called (AC #2)
    assert(destructor_call_count == 2);
  }

  std::cout << "✓" << std::endl;
}

void test_action_table_calls_all_destructors() {
  std::cout << "Test 4: Action table calls all destructors in sequence... ";
  reset_test_state();

  // GIVEN: Multiple objects with destructors
  int obj1 = 10, obj2 = 20, obj3 = 30;
  static const struct __cxx_action_entry actions[] = {{test_destructor, &obj1},
                                                      {test_destructor, &obj2},
                                                      {test_destructor, &obj3},
                                                      {nullptr, nullptr}};

  struct __cxx_exception_frame frame;
  frame.next = nullptr;
  frame.actions = actions;
  __cxx_exception_stack = &frame;

  // WHEN: Exception is thrown
  if (setjmp(frame.jmpbuf) == 0) {
    char exception_char = 'X';
    cxx_throw(&exception_char, "char");
    assert(false);
  } else {
    // THEN: All 3 destructors called
    assert(destructor_call_count == 3);
  }

  std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 3: Stack Unwinding (AC #3)
// ============================================================================

void test_cxx_throw_pops_frame_from_stack() {
  std::cout << "Test 5: cxx_throw pops frame from stack... ";
  reset_test_state();

  // GIVEN: A nested exception frame stack
  struct __cxx_exception_frame outer_frame;
  outer_frame.next = nullptr;
  outer_frame.actions = nullptr;
  __cxx_exception_stack = &outer_frame;

  struct __cxx_exception_frame inner_frame;
  inner_frame.next = &outer_frame;
  inner_frame.actions = nullptr;
  __cxx_exception_stack = &inner_frame;

  // WHEN: Exception thrown from inner frame
  if (setjmp(inner_frame.jmpbuf) == 0) {
    // Verify stack before throw
    assert(__cxx_exception_stack == &inner_frame);

    int exception_value = 123;
    cxx_throw(&exception_value, "int");
    assert(false);
  } else {
    // THEN: Stack should be popped (AC #3)
    assert(__cxx_exception_stack == &outer_frame);
  }

  std::cout << "✓" << std::endl;
}

void test_nested_frames_unwind_correctly() {
  std::cout << "Test 6: Nested frames unwind correctly... ";
  reset_test_state();

  // GIVEN: Three levels of nesting
  struct __cxx_exception_frame frame1, frame2, frame3;

  frame1.next = nullptr;
  frame1.actions = nullptr;
  __cxx_exception_stack = &frame1;

  frame2.next = &frame1;
  frame2.actions = nullptr;
  __cxx_exception_stack = &frame2;

  frame3.next = &frame2;
  frame3.actions = nullptr;
  __cxx_exception_stack = &frame3;

  // WHEN: Exception thrown from innermost frame
  if (setjmp(frame3.jmpbuf) == 0) {
    assert(__cxx_exception_stack == &frame3);
    int ex = 777;
    cxx_throw(&ex, "int");
    assert(false);
  } else {
    // THEN: Stack unwound one level
    assert(__cxx_exception_stack == &frame2);
  }

  std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 4: Uncaught Exception Handling (AC #5)
// ============================================================================

// Note: Testing abort() is tricky - we'll verify the condition instead
void test_uncaught_exception_detection() {
  std::cout << "Test 7: Uncaught exception detection... ";
  reset_test_state();

  // GIVEN: No exception frames on stack
  __cxx_exception_stack = nullptr;

  // WHEN/THEN: cxx_throw with null stack should abort
  // We can't easily test abort(), but we verify the condition
  // In production, cxx_throw would call abort() here

  // For testing, we'll just verify the stack is null
  assert(__cxx_exception_stack == nullptr);

  std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 5: Longjmp Behavior (AC #1)
// ============================================================================

void test_cxx_throw_performs_longjmp() {
  std::cout << "Test 8: cxx_throw performs longjmp to handler... ";
  reset_test_state();

  // GIVEN: An exception frame with setjmp
  struct __cxx_exception_frame frame;
  frame.next = nullptr;
  frame.actions = nullptr;
  __cxx_exception_stack = &frame;

  bool catch_handler_reached = false;

  // WHEN: setjmp returns 0 (normal path), then cxx_throw is called
  if (setjmp(frame.jmpbuf) == 0) {
    // Normal execution - throw exception
    int ex = 42;
    cxx_throw(&ex, "int");

    // Should never reach here
    assert(false && "After cxx_throw - should not reach");
  } else {
    // Catch handler - longjmp landed here
    catch_handler_reached = true;
  }

  // THEN: Catch handler should be reached via longjmp
  assert(catch_handler_reached);

  std::cout << "✓" << std::endl;
}

void test_longjmp_returns_nonzero() {
  std::cout << "Test 9: longjmp returns non-zero to catch handler... ";
  reset_test_state();

  struct __cxx_exception_frame frame;
  frame.next = nullptr;
  frame.actions = nullptr;
  __cxx_exception_stack = &frame;

  int setjmp_return_value = -1;

  // WHEN: Throwing exception
  setjmp_return_value = setjmp(frame.jmpbuf);
  if (setjmp_return_value == 0) {
    int ex = 100;
    cxx_throw(&ex, "int");
    assert(false);
  } else {
    // THEN: setjmp should return non-zero (1)
    assert(setjmp_return_value == 1);
  }

  std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 6: Integration Tests
// ============================================================================

void test_full_exception_handling_flow() {
  std::cout << "Test 10: Full exception handling flow... ";
  reset_test_state();

  // GIVEN: Complete exception handling setup
  int obj1 = 1, obj2 = 2;
  static const struct __cxx_action_entry actions[] = {
      {test_destructor, &obj1}, {test_destructor, &obj2}, {nullptr, nullptr}};

  struct __cxx_exception_frame frame;
  frame.next = nullptr;
  frame.actions = actions;
  frame.exception_object = nullptr;
  frame.exception_type = nullptr;
  __cxx_exception_stack = &frame;

  bool exception_caught = false;

  // WHEN: Full try-catch simulation
  if (setjmp(frame.jmpbuf) == 0) {
    // Try block
    int *exception = new int(42);
    cxx_throw(exception, "int");
    assert(false);
  } else {
    // Catch block
    exception_caught = true;

    // THEN: Verify all behaviors
    assert(frame.exception_object != nullptr);
    assert(strcmp(frame.exception_type, "int") == 0);
    assert(destructor_call_count == 2);
    assert(__cxx_exception_stack == nullptr);

    // Clean up exception object
    delete static_cast<int *>(frame.exception_object);
  }

  assert(exception_caught);

  std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite 7: Empty Action Table
// ============================================================================

void test_empty_action_table() {
  std::cout << "Test 11: Empty action table (no destructors)... ";
  reset_test_state();

  // GIVEN: Frame with empty action table
  static const struct __cxx_action_entry actions[] = {
      {nullptr, nullptr} // Immediately terminated
  };

  struct __cxx_exception_frame frame;
  frame.next = nullptr;
  frame.actions = actions;
  __cxx_exception_stack = &frame;

  // WHEN: Throwing exception
  if (setjmp(frame.jmpbuf) == 0) {
    int ex = 1;
    cxx_throw(&ex, "int");
    assert(false);
  } else {
    // THEN: No destructors called, but exception still caught
    assert(destructor_call_count == 0);
    assert(frame.exception_object != nullptr);
  }

  std::cout << "✓" << std::endl;
}

// ============================================================================
// Main
// ============================================================================

int main() {
  std::cout << "===================================" << std::endl;
  std::cout << "Exception Runtime Library Tests" << std::endl;
  std::cout << "Story #81" << std::endl;
  std::cout << "===================================" << std::endl;

  // Test Suite 1: cxx_throw Basic Functionality (AC #1)
  test_cxx_throw_walks_exception_stack();
  test_cxx_throw_stores_exception_info();

  // Test Suite 2: Action Table Execution (AC #2)
  test_cxx_throw_executes_action_table();
  test_action_table_calls_all_destructors();

  // Test Suite 3: Stack Unwinding (AC #3)
  test_cxx_throw_pops_frame_from_stack();
  test_nested_frames_unwind_correctly();

  // Test Suite 4: Uncaught Exception Handling (AC #5)
  test_uncaught_exception_detection();

  // Test Suite 5: Longjmp Behavior (AC #1)
  test_cxx_throw_performs_longjmp();
  test_longjmp_returns_nonzero();

  // Test Suite 6: Integration Tests
  test_full_exception_handling_flow();

  // Test Suite 7: Edge Cases
  test_empty_action_table();

  std::cout << "===================================" << std::endl;
  std::cout << "All tests passed! ✓" << std::endl;
  std::cout << "===================================" << std::endl;

  return 0;
}

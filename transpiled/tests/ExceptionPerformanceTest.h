// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/ExceptionPerformanceTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct __cxx_action_entry {
	void (void *) * destructor;
	void * object;
};
static void __cxx_action_entry__ctor_default(struct __cxx_action_entry * this);
static void __cxx_action_entry__ctor_copy(struct __cxx_action_entry * this, const struct __cxx_action_entry * other);
struct __cxx_exception_frame {
	int jmpbuf;
	struct __cxx_exception_frame * next;
	const struct __cxx_action_entry * actions;
	void * exception_object;
	const char * exception_type;
};
static void __cxx_exception_frame__ctor_default(struct __cxx_exception_frame * this);
static void __cxx_exception_frame__ctor_copy(struct __cxx_exception_frame * this, const struct __cxx_exception_frame * other);
struct BenchmarkException {
	int value;
};
static void BenchmarkException__ctor_default(struct BenchmarkException * this);
static void BenchmarkException__ctor_copy(struct BenchmarkException * this, const struct BenchmarkException * other);
void BenchmarkException__ctor(struct BenchmarkException * this_ptr, int val);
void BenchmarkException__dtor(void * this_ptr);
struct BenchmarkResource {
	int data;
};
static void BenchmarkResource__ctor_default(struct BenchmarkResource * this);
static void BenchmarkResource__ctor_copy(struct BenchmarkResource * this, const struct BenchmarkResource * other);
void BenchmarkResource__ctor(struct BenchmarkResource * this_ptr, int val);
void BenchmarkResource__dtor(void * this_ptr);
void benchmark_no_exception_transpiled(int iterations);
void benchmark_no_exception_native(int iterations);

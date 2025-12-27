// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/ExceptionPerformanceTest.cpp
// Implementation file

#include "ExceptionPerformanceTest.h"

static void __cxx_action_entry__ctor_default(struct __cxx_action_entry * this) {
	this->destructor = 0;
	this->object = 0;
}

static void __cxx_action_entry__ctor_copy(struct __cxx_action_entry * this, const struct __cxx_action_entry * other) {
	this->destructor = other->destructor;
	this->object = other->object;
}

static void __cxx_exception_frame__ctor_default(struct __cxx_exception_frame * this) {
	this->jmpbuf = 0;
	this->next = 0;
	this->actions = 0;
	this->exception_object = 0;
	this->exception_type = 0;
}

static void __cxx_exception_frame__ctor_copy(struct __cxx_exception_frame * this, const struct __cxx_exception_frame * other) {
	this->jmpbuf = other->jmpbuf;
	this->next = other->next;
	this->actions = other->actions;
	this->exception_object = other->exception_object;
	this->exception_type = other->exception_type;
}

static void BenchmarkException__ctor_default(struct BenchmarkException * this) {
	this->value = 0;
}

static void BenchmarkException__ctor_copy(struct BenchmarkException * this, const struct BenchmarkException * other) {
	this->value = other->value;
}

void BenchmarkException__ctor(struct BenchmarkException * this_ptr, int val) {
	this_ptr->value = val;
}

void BenchmarkException__dtor(void * this_ptr) {
	(void)this_ptr;
}

static void BenchmarkResource__ctor_default(struct BenchmarkResource * this) {
	this->data = 0;
}

static void BenchmarkResource__ctor_copy(struct BenchmarkResource * this, const struct BenchmarkResource * other) {
	this->data = other->data;
}

void BenchmarkResource__ctor(struct BenchmarkResource * this_ptr, int val) {
	this_ptr->data = val;
}

void BenchmarkResource__dtor(void * this_ptr) {
	(void)this_ptr;
}

void benchmark_no_exception_transpiled(int iterations) {
	for (int i = 0; i < iterations; i++) {
        struct __cxx_exception_frame frame;
        frame.next = __cxx_exception_stack;
        frame.actions = nullptr;
        frame.exception_object = nullptr;
        frame.exception_type = nullptr;
}

}

void benchmark_no_exception_native(int iterations) {
	for (int i = 0; i < iterations; i++) {
        try {
                volatile int dummy = i * 2;
                (void)dummy;
        } catch (...) {
                <recovery-expr>(assert, false);
        }
}

}


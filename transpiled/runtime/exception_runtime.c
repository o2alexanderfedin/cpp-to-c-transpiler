// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./runtime/exception_runtime.cpp
// Implementation file

#include "exception_runtime.h"

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

extern void cxx_throw(void * exception, const char * type_info) {
	struct __cxx_exception_frame *frame = __cxx_exception_stack;

	const struct __cxx_action_entry *action = frame->actions;

	__cxx_exception_stack = frame->next;
	frame->exception_object = exception;
	frame->exception_type = type_info;
}


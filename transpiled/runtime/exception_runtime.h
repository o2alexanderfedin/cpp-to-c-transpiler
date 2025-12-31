// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./runtime/exception_runtime.cpp
// Header file

#pragma once

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
	int jmpbuf[48];
	struct __cxx_exception_frame * next;
	const struct __cxx_action_entry * actions;
	void * exception_object;
	const char * exception_type;
};
static void __cxx_exception_frame__ctor_default(struct __cxx_exception_frame * this);
static void __cxx_exception_frame__ctor_copy(struct __cxx_exception_frame * this, const struct __cxx_exception_frame * other);
extern void cxx_throw(void * exception, const char * type_info);

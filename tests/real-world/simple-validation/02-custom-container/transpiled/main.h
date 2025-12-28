// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/02-custom-container/main.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

size_t LinkedList_size(struct LinkedList * this);
bool LinkedList_isEmpty(struct LinkedList * this);
void LinkedList_push_back(struct LinkedList * this, const int * value);
int LinkedList_front(struct LinkedList * this);
void LinkedList_push_front(struct LinkedList * this, const int * value);
void LinkedList_pop_front(struct LinkedList * this);
void LinkedList_push_back_float_ref(struct LinkedList * this, const float * value);
size_t LinkedList_size(struct LinkedList * this);
float LinkedList_front(struct LinkedList * this);
int main();
struct LinkedList_int_Node {
	int data;
	struct LinkedList_int_Node * next;
};
void LinkedList_int_Node__ctor(struct LinkedList_int_Node * this, int * value);
struct LinkedList_int {
	struct LinkedList_int_Node * head;
	struct LinkedList_int_Node * tail;
	size_t count;
};
void LinkedList_int_push_back(struct LinkedList_int * this, int * value);
void LinkedList_int_push_front(struct LinkedList_int * this, int * value);
void LinkedList_int_pop_front(struct LinkedList_int * this);
int LinkedList_int_front(struct LinkedList_int * this);
size_t LinkedList_int_size(struct LinkedList_int * this);
bool LinkedList_int_isEmpty(struct LinkedList_int * this);
void LinkedList_int_clear(struct LinkedList_int * this);
extern struct LinkedList_int_Node * newNode;
extern struct LinkedList_int_Node * newNode;
extern struct LinkedList_int_Node * temp;
extern struct LinkedList_int_Node * temp;
struct LinkedList_float_Node {
	float data;
	struct LinkedList_float_Node * next;
};
void LinkedList_float_Node__ctor(struct LinkedList_float_Node * this, float * value);
struct LinkedList_float {
	struct LinkedList_float_Node * head;
	struct LinkedList_float_Node * tail;
	size_t count;
};
void LinkedList_float_push_back(struct LinkedList_float * this, float * value);
void LinkedList_float_push_front(struct LinkedList_float * this, float * value);
void LinkedList_float_pop_front(struct LinkedList_float * this);
float LinkedList_float_front(struct LinkedList_float * this);
size_t LinkedList_float_size(struct LinkedList_float * this);
bool LinkedList_float_isEmpty(struct LinkedList_float * this);
void LinkedList_float_clear(struct LinkedList_float * this);
extern struct LinkedList_float_Node * newNode;
extern struct LinkedList_float_Node * newNode;
extern struct LinkedList_float_Node * temp;
extern struct LinkedList_float_Node * temp;

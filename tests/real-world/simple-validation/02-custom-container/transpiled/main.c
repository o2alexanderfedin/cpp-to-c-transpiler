// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/02-custom-container/main.cpp
// Implementation file

#include "main.h"

size_t LinkedList_size(struct LinkedList * this);
bool LinkedList_isEmpty(struct LinkedList * this);
void LinkedList_push_back_const_int_ref(struct LinkedList * this, const int * value);
int LinkedList_front(struct LinkedList * this);
void LinkedList_push_front_const_int_ref(struct LinkedList * this, const int * value);
void LinkedList_pop_front(struct LinkedList * this);
void LinkedList_push_back_const_float_ref(struct LinkedList * this, const float * value);
int main() {
	struct LinkedList_int list;
	printf("LinkedList<int> Tests:\n");
	printf("  Initial size: %zu\n", LinkedList_size(&list));
	printf("  Is empty: %s\n", list.isEmpty() ? "true" : "false");
	list.push_back(10);
	list.push_back(20);
	list.push_back(30);
	printf("  After push_back(10, 20, 30): size = %zu\n", LinkedList_size(&list));
	printf("  Front element: %d\n", LinkedList_front(&list));
	list.push_front(5);
	printf("  After push_front(5): size = %zu, front = %d\n", LinkedList_size(&list), LinkedList_front(&list));
	LinkedList_pop_front(&list);
	printf("  After pop_front(): size = %zu, front = %d\n", LinkedList_size(&list), LinkedList_front(&list));
	struct LinkedList_float floatList;
	floatList.push_back(1.5F);
	floatList.push_back(2.5F);
	floatList.push_back(3.5F);
	printf("\nLinkedList<float> Tests:\n");
	printf("  Size: %zu\n", LinkedList_size(&floatList));
	printf("  Front: %.1f\n", LinkedList_front(&floatList));
	bool passed = true;
	passed = passed && (LinkedList_size(&list) == 3);
	passed = passed && (LinkedList_front(&list) == 10);
	passed = passed && (!list.isEmpty());
	passed = passed && (LinkedList_size(&floatList) == 3);
	passed = passed && (LinkedList_front(&floatList) > 1.39999998F && LinkedList_front(&floatList) < 1.60000002F);
	printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
	return passed ? 0 : 1;
;
}

void LinkedList_int_push_back(struct LinkedList_int * this, int * value) {
	struct LinkedList_int_Node * newNode = malloc(sizeof(struct LinkedList_int_Node));
	if (this->tail == 0) 	{
		this->head = this->tail = newNode;
	}
 else 	{
		this->tail->next = newNode;
		this->tail = newNode;
	}

	this->count++;
}

void LinkedList_int_push_front(struct LinkedList_int * this, int * value) {
	struct LinkedList_int_Node * newNode = malloc(sizeof(struct LinkedList_int_Node));
	newNode->next = this->head;
	this->head = newNode;
	if (this->tail == 0) 	{
		this->tail = this->head;
	}

	this->count++;
}

void LinkedList_int_pop_front(struct LinkedList_int * this) {
	if (this->head != 0) 	{
		struct LinkedList_int_Node * temp = this->head;
		this->head = this->head->next;
		if (this->head == 0) 		{
			this->tail = 0;
		}

		free(temp);
		this->count--;
	}

}

int LinkedList_int_front(struct LinkedList_int * this) {
	return this->head->data;
;
}

size_t LinkedList_int_size(struct LinkedList_int * this) {
	return this->count;
;
}

bool LinkedList_int_isEmpty(struct LinkedList_int * this) {
	return this->count == 0;
;
}

void LinkedList_int_clear(struct LinkedList_int * this) {
	while (this->head != 0) 	{
		struct LinkedList_int_Node * temp = this->head;
		this->head = this->head->next;
		free(temp);
	}
	this->tail = 0;
	this->count = 0;
}

void LinkedList_float_push_back(struct LinkedList_float * this, float * value) {
	struct LinkedList_float_Node * newNode = malloc(sizeof(struct LinkedList_float_Node));
	if (this->tail == 0) 	{
		this->head = this->tail = newNode;
	}
 else 	{
		this->tail->next = newNode;
		this->tail = newNode;
	}

	this->count++;
}

void LinkedList_float_push_front(struct LinkedList_float * this, float * value) {
	struct LinkedList_float_Node * newNode = malloc(sizeof(struct LinkedList_float_Node));
	newNode->next = this->head;
	this->head = newNode;
	if (this->tail == 0) 	{
		this->tail = this->head;
	}

	this->count++;
}

void LinkedList_float_pop_front(struct LinkedList_float * this) {
	if (this->head != 0) 	{
		struct LinkedList_float_Node * temp = this->head;
		this->head = this->head->next;
		if (this->head == 0) 		{
			this->tail = 0;
		}

		free(temp);
		this->count--;
	}

}

float LinkedList_float_front(struct LinkedList_float * this) {
	return this->head->data;
;
}

size_t LinkedList_float_size(struct LinkedList_float * this) {
	return this->count;
;
}

bool LinkedList_float_isEmpty(struct LinkedList_float * this) {
	return this->count == 0;
;
}

void LinkedList_float_clear(struct LinkedList_float * this) {
	while (this->head != 0) 	{
		struct LinkedList_float_Node * temp = this->head;
		this->head = this->head->next;
		free(temp);
	}
	this->tail = 0;
	this->count = 0;
}

struct LinkedList_float_Node * newNode = malloc(sizeof(struct LinkedList_float_Node));
struct LinkedList_float_Node * newNode = malloc(sizeof(struct LinkedList_float_Node));
struct LinkedList_float_Node * temp = this->head;
struct LinkedList_float_Node * temp = this->head;

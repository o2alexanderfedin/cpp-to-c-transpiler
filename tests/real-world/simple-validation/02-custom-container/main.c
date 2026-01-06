// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/02-custom-container/./main.cpp
// Implementation file

#include "main.h"

int main() {
	LinkedList<int> list;

	LinkedList<float> floatList;

	bool passed = true;

	return passed ? 0 : 1;
;
}

void LinkedList_int_Node__ctor(struct LinkedList_int_Node * this, int * value);
void LinkedList_int_push_back(struct LinkedList_int * this, int * value) {
	Node *newNode = malloc(sizeof(Node));

	if (this->tail == 0) 	{
		this->head = this->tail = newNode;
	}
 else 	{
		this->tail->next = newNode;
		this->tail = newNode;
	}

}

void LinkedList_int_push_front(struct LinkedList_int * this, int * value) {
	Node *newNode = malloc(sizeof(Node));

	newNode->next = this->head;
	this->head = newNode;
	if (this->tail == 0) 	{
		this->tail = this->head;
	}

}

void LinkedList_int_pop_front(struct LinkedList_int * this) {
	if (this->head != 0) 	{
		Node *temp = this->head;

		this->head = this->head->next;
		if (this->head == 0) 		{
			this->tail = 0;
		}

		free(temp);
	}

}

int LinkedList_int_front(struct LinkedList_int * this) {
	return this->head->data;
;
}

int LinkedList_int_size(struct LinkedList_int * this);
bool LinkedList_int_isEmpty(struct LinkedList_int * this) {
}

void LinkedList_int_clear(struct LinkedList_int * this) {
	while (this->head != 0) 	{
		Node *temp = this->head;

		this->head = this->head->next;
		free(temp);
	}
	this->tail = 0;
}

Node *newNode = malloc(sizeof(Node))
Node *newNode = malloc(sizeof(Node))
void LinkedList_float_Node__ctor(struct LinkedList_float_Node * this, float * value);
void LinkedList_float_push_back(struct LinkedList_float * this, float * value) {
	Node *newNode = malloc(sizeof(Node));

	if (this->tail == 0) 	{
		this->head = this->tail = newNode;
	}
 else 	{
		this->tail->next = newNode;
		this->tail = newNode;
	}

}

void LinkedList_float_push_front(struct LinkedList_float * this, float * value) {
	Node *newNode = malloc(sizeof(Node));

	newNode->next = this->head;
	this->head = newNode;
	if (this->tail == 0) 	{
		this->tail = this->head;
	}

}

void LinkedList_float_pop_front(struct LinkedList_float * this) {
	if (this->head != 0) 	{
		Node *temp = this->head;

		this->head = this->head->next;
		if (this->head == 0) 		{
			this->tail = 0;
		}

		free(temp);
	}

}

float LinkedList_float_front(struct LinkedList_float * this) {
	return this->head->data;
;
}

int LinkedList_float_size(struct LinkedList_float * this);
bool LinkedList_float_isEmpty(struct LinkedList_float * this) {
}

void LinkedList_float_clear(struct LinkedList_float * this) {
	while (this->head != 0) 	{
		Node *temp = this->head;

		this->head = this->head->next;
		free(temp);
	}
	this->tail = 0;
}

Node *newNode = malloc(sizeof(Node))
Node *newNode = malloc(sizeof(Node))

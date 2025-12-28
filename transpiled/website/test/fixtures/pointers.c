// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./website/test/fixtures/pointers.cpp
// Implementation file

#include "pointers.h"

void swap(int * a, int * b) {
	int temp = *a;
	*a = *b;
	*b = temp;
}

int * createArray(int size) {
	int * arr = malloc(sizeof(int));
	for (int i = 0; i < size; i++) {
        arr[i] = i * 2;
}

	return arr;
;
}

void deleteArray(int * arr) {
	free(arr);
}

static void Node__ctor_default(struct Node * this) {
	this->data = 0;
	this->next = 0;
}

static void Node__ctor_copy(struct Node * this, const struct Node * other) {
	this->data = other->data;
	this->next = other->next;
}

struct Node * createNode(int value) {
	Node * node = malloc(sizeof(Node));
	node->data = value;
	node->next = 0;
	return node;
;
}

void appendNode(struct Node * head, int value) {
	Node * current = head;
	while (current->next != 0) 	{
		current = current->next;
	}
	current->next = createNode(value);
}

int countNodes(struct Node * head) {
	int count = 0;
	Node * current = head;
	while (current != 0) 	{
		count++;
		current = current->next;
	}
	return count;
;
}


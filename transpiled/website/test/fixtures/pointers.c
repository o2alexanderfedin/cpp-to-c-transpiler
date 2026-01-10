#include "pointers.h"

void swap(int * a, int * b) {
	int temp = *a;
	*a = *b;
	*b = temp;
}

int * createArray(int size) {
	int * arr = 0;
	for (int i = 0; i < size; i++) {
        arr[i] = i * 2;
}

	return arr;
;
}

void deleteArray(int * arr) {
}

struct Node * createNode(int value) {
	struct Node * node = 0;
	node->data = value;
	node->next = 0;
	return node;
;
}

void appendNode(struct Node * head, int value) {
	struct Node * current = head;
	while (current->next != 0) 	{
		current = current->next;
	}
	current->next = createNode(value);
}

int countNodes(struct Node * head) {
	int count = 0;
	struct Node * current = head;
	while (current != 0) 	{
		count++;
		current = current->next;
	}
	return count;
;
}


#pragma once

void swap(int * a, int * b);
int * createArray(int size);
void deleteArray(int * arr);
struct Node {
	int data;
	struct Node * next;
};
struct Node * createNode(int value);
void appendNode(struct Node * head, int value);
int countNodes(struct Node * head);

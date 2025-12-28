// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./website/test/fixtures/pointers.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

void swap(int * a, int * b);
int * createArray(int size);
void deleteArray(int * arr);
struct Node {
	int data;
	struct Node * next;
};
static void Node__ctor_default(struct Node * this);
static void Node__ctor_copy(struct Node * this, const struct Node * other);
struct Node * createNode(int value);
void appendNode(struct Node * head, int value);
int countNodes(struct Node * head);

// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/integration/cpp23/output/05_range_for_custom_containers_project/main.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

void SimpleList_add(struct SimpleList * this, int value);
int main();
struct SimpleList_int_Iterator {
	int * ptr;
};
void SimpleList_int_Iterator__ctor(struct SimpleList_int_Iterator * this, int * p);
struct SimpleList_int {
	int data[10];
	int size;
};
void SimpleList_int_add(struct SimpleList_int * this, int value);
int SimpleList_int_getSize(struct SimpleList_int * this);
int SimpleList_int_get(struct SimpleList_int * this, int index);
struct SimpleList_int_Iterator SimpleList_int_begin(struct SimpleList_int * this);
struct SimpleList_int_Iterator SimpleList_int_end(struct SimpleList_int * this);
struct SimpleList_double_Iterator {
	double * ptr;
};
void SimpleList_double_Iterator__ctor(struct SimpleList_double_Iterator * this, double * p);
struct SimpleList_double {
	double data[10];
	int size;
};
void SimpleList_double_add(struct SimpleList_double * this, double value);
int SimpleList_double_getSize(struct SimpleList_double * this);
double SimpleList_double_get(struct SimpleList_double * this, int index);
struct SimpleList_double_Iterator SimpleList_double_begin(struct SimpleList_double * this);
struct SimpleList_double_Iterator SimpleList_double_end(struct SimpleList_double * this);

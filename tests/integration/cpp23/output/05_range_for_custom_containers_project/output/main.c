// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/integration/cpp23/output/05_range_for_custom_containers_project/main.cpp
// Implementation file

#include "main.h"

void SimpleList_add(struct SimpleList * this, int value);
int main() {
	struct SimpleList_int list;

	SimpleList_add(&list, 10);
	SimpleList_add(&list, 20);
	SimpleList_add(&list, 30);
	SimpleList_add(&list, 40);
	SimpleList_add(&list, 50);
	int sum = 0;

	int expected[] = {10, 20, 30, 40, 50};

	int index = 0;

	struct SimpleList_double doubleList;

	double doubleSum = 0.;

	return 0;
;
}

void SimpleList_int_Iterator__ctor(struct SimpleList_int_Iterator * this, int * p);
void SimpleList_int_add(struct SimpleList_int * this, int value) {
	if (this->size < MAX_SIZE) 	{
		this->data[this->size++] = value;
	}

}

int SimpleList_int_getSize(struct SimpleList_int * this) {
	return this->size;
;
}

int SimpleList_int_get(struct SimpleList_int * this, int index) {
	return this->data[index];
;
}

struct SimpleList_int_Iterator SimpleList_int_begin(struct SimpleList_int * this) {
	return Iterator(this->data);
;
}

struct SimpleList_int_Iterator SimpleList_int_end(struct SimpleList_int * this) {
	return Iterator(this->data + this->size);
;
}

void SimpleList_double_Iterator__ctor(struct SimpleList_double_Iterator * this, double * p);
void SimpleList_double_add(struct SimpleList_double * this, double value) {
	if (this->size < MAX_SIZE) 	{
		this->data[this->size++] = value;
	}

}

int SimpleList_double_getSize(struct SimpleList_double * this) {
	return this->size;
;
}

double SimpleList_double_get(struct SimpleList_double * this, int index) {
	return this->data[index];
;
}

struct SimpleList_double_Iterator SimpleList_double_begin(struct SimpleList_double * this) {
	return Iterator(this->data);
;
}

struct SimpleList_double_Iterator SimpleList_double_end(struct SimpleList_double * this) {
	return Iterator(this->data + this->size);
;
}


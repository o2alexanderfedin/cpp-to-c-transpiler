// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/integration/cpp23/output/02_virtual_multiple_inheritance_project/main.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct Base {
	const struct Base_vtable * vptr;
	int baseValue;
};
static void Base__ctor_copy(struct Base * this, const struct Base * other);
void Base__ctor(struct Base * this, int v);
void Base__dtor(struct Base * this);
int Base_getBaseValue(struct Base * this);
struct Left {
	const struct Base_vtable * vptr;
	int baseValue;
	int leftValue;
};
static void Left__ctor_copy(struct Left * this, const struct Left * other);
void Left__ctor(struct Left * this, int b, int l);
int Left_getLeftValue(struct Left * this);
struct Right {
	const struct Base_vtable * vptr;
	int baseValue;
	int rightValue;
};
static void Right__ctor_copy(struct Right * this, const struct Right * other);
void Right__ctor(struct Right * this, int b, int r);
int Right_getRightValue(struct Right * this);
struct Diamond {
	const struct Base_vtable * vptr;
	int baseValue;
	int leftValue;
	const struct Base_vtable * vptr;
	int baseValue;
	int rightValue;
	int diamondValue;
};
static void Diamond__ctor_copy(struct Diamond * this, const struct Diamond * other);
void Diamond__ctor(struct Diamond * this, int b1, int l, int b2, int r, int d);
int Diamond_getDiamondValue(struct Diamond * this);
int main();

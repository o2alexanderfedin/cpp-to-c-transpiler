// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/integration/cpp23/output/03_scoped_enums_namespaces_project/main.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct Pixel {
	Color::Primary primary;
	int value;
};
static void Pixel__ctor_copy(struct Pixel * this, const struct Pixel * other);
void Pixel__ctor(struct Pixel * this, Color::Primary p, int v);
Color::Primary Pixel_getPrimary(struct Pixel * this);
int Pixel_getValue(struct Pixel * this);
bool Pixel_isRed(struct Pixel * this);
bool Pixel_isGreen(struct Pixel * this);
bool Pixel_isBlue(struct Pixel * this);
int main();

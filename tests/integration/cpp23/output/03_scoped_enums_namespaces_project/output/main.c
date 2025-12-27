// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/integration/cpp23/output/03_scoped_enums_namespaces_project/main.cpp
// Implementation file

#include "main.h"

static void Pixel__ctor_copy(struct Pixel * this, const struct Pixel * other) {
	this->primary = other->primary;
	this->value = other->value;
}

void Pixel__ctor(struct Pixel * this, Color::Primary p, int v) {
	this->primary = p;
	this->value = v;
}

Color::Primary Pixel_getPrimary(struct Pixel * this) {
	return this->primary;
;
}

int Pixel_getValue(struct Pixel * this) {
	return this->value;
;
}

bool Pixel_isRed(struct Pixel * this) {
	return this->primary == Primary__Red;
;
}

bool Pixel_isGreen(struct Pixel * this) {
	return this->primary == Primary__Green;
;
}

bool Pixel_isBlue(struct Pixel * this) {
	return this->primary == Primary__Blue;
;
}

int main() {
	struct Pixel redPixel;

	Pixel__ctor(&redPixel, Primary__Red, 255);
	struct Pixel greenPixel;

	Pixel__ctor(&greenPixel, Primary__Green, 128);
	return 0;
;
}


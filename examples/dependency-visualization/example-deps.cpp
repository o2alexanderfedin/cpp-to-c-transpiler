// Example C++ file to demonstrate dependency visualization
// This file shows a simple multi-file project structure

// Point.h would contain:
struct Point {
    int x;
    int y;
};

// Circle.h would contain:
struct Circle {
    Point center;  // Depends on Point
    double radius;
};

// Rectangle.h would contain:
struct Rectangle {
    Point topLeft;      // Depends on Point
    Point bottomRight;  // Depends on Point
};

// Main function using all structures
int main() {
    Point p = {10, 20};
    Circle c = {p, 5.0};
    Rectangle r = {{0, 0}, {100, 100}};
    return 0;
}

// Test file for Phase 31-03: COM-style declarations for all methods

class Counter {
    int value;
public:
    Counter(int v) : value(v) {}
    int getValue() const { return value; }
    void increment() { value++; }
    virtual ~Counter() {}
};

class Point {
    int x, y;
public:
    Point() : x(0), y(0) {}
    Point(int v) : x(v), y(v) {}
    Point(int x_, int y_) : x(x_), y(y_) {}
    int getX() const { return x; }
    int getY() const { return y; }
};

int main() {
    Counter c(0);
    c.increment();

    Point p1;
    Point p2(5);
    Point p3(3, 4);

    return c.getValue() + p3.getX();
}

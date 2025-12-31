// Integration Test 4: Operator Overloading + Templates
// Tests: Template class with arithmetic operators
// Expected: Transpiles to C with proper operator function names

#include <cassert>

template<typename T>
class Vector2D {
    T x, y;
public:
    Vector2D(T x_val, T y_val) : x(x_val), y(y_val) {}

    T getX() const { return x; }
    T getY() const { return y; }

    // Arithmetic operators
    Vector2D operator+(const Vector2D& other) const {
        return Vector2D(x + other.x, y + other.y);
    }

    Vector2D operator-(const Vector2D& other) const {
        return Vector2D(x - other.x, y - other.y);
    }

    Vector2D operator*(T scalar) const {
        return Vector2D(x * scalar, y * scalar);
    }

    // Comparison operators
    bool operator==(const Vector2D& other) const {
        return x == other.x && y == other.y;
    }

    bool operator!=(const Vector2D& other) const {
        return !(*this == other);
    }

    // Subscript operator
    T operator[](int index) const {
        return index == 0 ? x : y;
    }
};

int main() {
    Vector2D<int> v1(3, 4);
    Vector2D<int> v2(1, 2);

    // Test arithmetic
    Vector2D<int> v3 = v1 + v2;
    assert(v3.getX() == 4);
    assert(v3.getY() == 6);

    Vector2D<int> v4 = v1 - v2;
    assert(v4.getX() == 2);
    assert(v4.getY() == 2);

    Vector2D<int> v5 = v1 * 2;
    assert(v5.getX() == 6);
    assert(v5.getY() == 8);

    // Test comparison
    assert(v1 == Vector2D<int>(3, 4));
    assert(v1 != v2);

    // Test subscript
    assert(v1[0] == 3);
    assert(v1[1] == 4);

    // Test with double
    Vector2D<double> vd1(1.5, 2.5);
    Vector2D<double> vd2(0.5, 0.5);
    Vector2D<double> vd3 = vd1 + vd2;
    assert(vd3.getX() == 2.0);
    assert(vd3.getY() == 3.0);

    return 0;
}

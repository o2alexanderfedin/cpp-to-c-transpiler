// Integration Test 1: Templates + Inheritance
// Tests: Template classes with single inheritance
// Expected: Transpiles to C with proper struct hierarchy and function pointers

#include <cassert>

// Template base class
template<typename T>
class Container {
protected:
    T value;
public:
    Container(T v) : value(v) {}
    virtual ~Container() {}

    virtual T getValue() const {
        return value;
    }

    void setValue(T v) {
        value = v;
    }
};

// Derived template class
template<typename T>
class Box : public Container<T> {
    T multiplier;
public:
    Box(T v, T m) : Container<T>(v), multiplier(m) {}

    T getValue() const override {
        return this->value * multiplier;
    }

    T getMultiplier() const {
        return multiplier;
    }
};

int main() {
    // Test with int
    Box<int> intBox(5, 3);
    assert(intBox.getValue() == 15);
    assert(intBox.getMultiplier() == 3);

    intBox.setValue(10);
    assert(intBox.getValue() == 30);

    // Test with double
    Box<double> doubleBox(2.5, 4.0);
    assert(doubleBox.getValue() == 10.0);

    return 0;
}

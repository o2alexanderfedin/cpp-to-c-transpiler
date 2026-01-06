// Integration Test 2: Virtual Methods + Multiple Inheritance
// Tests: Diamond inheritance with virtual methods
// Expected: Transpiles to C with proper vtable and offset handling

#include <cassert>

class Base {
protected:
    int baseValue;
public:
    Base(int v) : baseValue(v) {}
    virtual ~Base() {}

    virtual int compute() const {
        return baseValue;
    }

    int getBaseValue() const {
        return baseValue;
    }
};

class Left : public Base {
    int leftValue;
public:
    Left(int b, int l) : Base(b), leftValue(l) {}

    int compute() const override {
        return baseValue + leftValue;
    }

    int getLeftValue() const {
        return leftValue;
    }
};

class Right : public Base {
    int rightValue;
public:
    Right(int b, int r) : Base(b), rightValue(r) {}

    int compute() const override {
        return baseValue * rightValue;
    }

    int getRightValue() const {
        return rightValue;
    }
};

class Diamond : public Left, public Right {
    int diamondValue;
public:
    Diamond(int b1, int l, int b2, int r, int d)
        : Left(b1, l), Right(b2, r), diamondValue(d) {}

    int compute() const override {
        return Left::compute() + Right::compute() + diamondValue;
    }

    int getDiamondValue() const {
        return diamondValue;
    }
};

int main() {
    Diamond d(10, 5, 3, 4, 7);

    // Left::compute() = 10 + 5 = 15
    // Right::compute() = 3 * 4 = 12
    // Diamond::compute() = 15 + 12 + 7 = 34
    assert(d.compute() == 34);
    assert(d.getLeftValue() == 5);
    assert(d.getRightValue() == 4);
    assert(d.getDiamondValue() == 7);

    return 0;
}

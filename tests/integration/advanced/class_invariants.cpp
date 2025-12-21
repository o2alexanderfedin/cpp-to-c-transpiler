// Advanced test: Class with invariants
// Expected ACSL: class invariant predicate, type invariant

class BoundedCounter {
private:
    int value;
    int max;

public:
    BoundedCounter(int m) : value(0), max(m) {}

    void increment() {
        if (value < max) {
            value++;
        }
    }

    int getValue() const {
        return value;
    }
};

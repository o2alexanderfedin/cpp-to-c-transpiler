// Example: Simple class with methods
class Counter {
    int count;

public:
    Counter(int initial) {
        count = initial;
    }

    void increment() {
        count = count + 1;
    }

    int getValue() {
        return count;
    }
};

// Usage
int test() {
    Counter c(0);
    c.increment();
    return c.getValue();
}

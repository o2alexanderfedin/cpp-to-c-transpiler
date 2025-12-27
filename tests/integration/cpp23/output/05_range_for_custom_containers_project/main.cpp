// Integration Test 5: Range-for + Custom Containers
// Tests: Custom container with range-for loop support
// Expected: Transpiles to C with proper iterator implementation

#include <cassert>

template<typename T>
class SimpleList {
    static const int MAX_SIZE = 10;
    T data[MAX_SIZE];
    int size;

public:
    SimpleList() : size(0) {}

    void add(T value) {
        if (size < MAX_SIZE) {
            data[size++] = value;
        }
    }

    int getSize() const {
        return size;
    }

    T get(int index) const {
        return data[index];
    }

    // Iterator support
    class Iterator {
        T* ptr;
    public:
        Iterator(T* p) : ptr(p) {}

        T& operator*() {
            return *ptr;
        }

        Iterator& operator++() {
            ++ptr;
            return *this;
        }

        bool operator!=(const Iterator& other) const {
            return ptr != other.ptr;
        }
    };

    Iterator begin() {
        return Iterator(data);
    }

    Iterator end() {
        return Iterator(data + size);
    }
};

int main() {
    SimpleList<int> list;
    list.add(10);
    list.add(20);
    list.add(30);
    list.add(40);
    list.add(50);

    assert(list.getSize() == 5);

    // Test range-for loop
    int sum = 0;
    for (int value : list) {
        sum += value;
    }
    assert(sum == 150);  // 10 + 20 + 30 + 40 + 50

    // Test manual iteration
    int expected[] = {10, 20, 30, 40, 50};
    int index = 0;
    for (int value : list) {
        assert(value == expected[index++]);
    }

    // Test with different type
    SimpleList<double> doubleList;
    doubleList.add(1.5);
    doubleList.add(2.5);
    doubleList.add(3.5);

    double doubleSum = 0.0;
    for (double value : doubleList) {
        doubleSum += value;
    }
    assert(doubleSum == 7.5);  // 1.5 + 2.5 + 3.5

    return 0;
}

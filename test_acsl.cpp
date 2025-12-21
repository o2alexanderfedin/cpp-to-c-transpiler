// Test file for ACSL integration testing
// This file tests basic ACSL annotation generation

class Stack {
private:
    int* data;
    int size;
    int capacity;

public:
    Stack(int cap) : size(0), capacity(cap) {
        data = new int[capacity];
    }

    void push(int value) {
        if (size < capacity) {
            data[size] = value;
            size++;
        }
    }

    int pop() {
        if (size > 0) {
            size--;
            return data[size];
        }
        return -1;
    }

    ~Stack() {
        delete[] data;
    }
};

// Function with array processing - should generate ACSL annotations
void fillArray(int* arr, int n, int value) {
    for (int i = 0; i < n; i++) {
        arr[i] = value;
    }
}

// Function with pointer validity requirements
int safeDivide(int* numerator, int* denominator) {
    if (numerator && denominator && *denominator != 0) {
        return *numerator / *denominator;
    }
    return 0;
}

int main() {
    Stack s(10);
    s.push(5);
    s.push(10);

    int arr[5];
    fillArray(arr, 5, 42);

    int a = 10, b = 2;
    int result = safeDivide(&a, &b);

    return 0;
}

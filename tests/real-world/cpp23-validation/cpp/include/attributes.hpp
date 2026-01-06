#ifndef ATTRIBUTES_HPP
#define ATTRIBUTES_HPP

#include <iostream>

namespace cpp23::attributes {

// Feature: [[assume]] attribute (P1774)
// Gives optimization hints to compiler about invariants

inline int divide_positive(int a, int b) {
    [[assume(b > 0)]];  // Tell compiler b is always positive
    return a / b;
}

inline void process_array(int* arr, int size) {
    [[assume(arr != nullptr)]];
    [[assume(size > 0)]];

    for (int i = 0; i < size; ++i) {
        arr[i] *= 2;
    }
}

// Multiple assumptions
inline int compute(int x, int y) {
    [[assume(x >= 0)]];
    [[assume(y >= 0)]];
    [[assume(x + y < 1000)]];

    return x * x + y * y;
}

// Feature: Labels at end of compound statements (P2324)
inline void labeled_blocks() {
    bool done = false;
    if (done) goto block1_end;

    {
        std::cout << "Block 1\n";
    }
    // C++23: Labels can now appear at the end of compound statements
    block1_end:;  // This is now legal in C++23

    if (done) goto block2_end;

    {
        std::cout << "Block 2\n";
    }
    block2_end:;
}

void test_attributes();

} // namespace cpp23::attributes

#endif // ATTRIBUTES_HPP

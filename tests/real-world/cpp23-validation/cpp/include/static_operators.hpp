#ifndef STATIC_OPERATORS_HPP
#define STATIC_OPERATORS_HPP

#include <iostream>

namespace cpp23::static_operators {

// Feature: static operator() and static operator[] (P1169)
// Allows function call and subscript operators to be static

class Calculator {
public:
    // Static function call operator
    static int operator()(int a, int b) {
        return a + b;
    }
};

class SquareTable {
public:
    // Static subscript operator
    static int operator[](int n) {
        return n * n;
    }
};

// Combined example
class MathOps {
public:
    static double operator()(double x) {
        return x * x;
    }

    static int operator[](int idx) {
        static const int primes[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29};
        return (idx >= 0 && idx < 10) ? primes[idx] : -1;
    }
};

void test_static_operators();

} // namespace cpp23::static_operators

#endif // STATIC_OPERATORS_HPP

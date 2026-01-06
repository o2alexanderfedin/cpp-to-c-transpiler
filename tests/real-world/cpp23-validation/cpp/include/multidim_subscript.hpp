#ifndef MULTIDIM_SUBSCRIPT_HPP
#define MULTIDIM_SUBSCRIPT_HPP

#include <iostream>
#include <vector>
#include <cstddef>

namespace cpp23::multidim_subscript {

// Feature: Multidimensional subscript operator (P2128) - operator[] with multiple arguments
// Before C++23: matrix[i][j] or matrix.at(i, j)
// C++23: matrix[i, j]

template<typename T>
class Matrix {
private:
    std::vector<T> data_;
    std::size_t rows_;
    std::size_t cols_;

public:
    Matrix(std::size_t rows, std::size_t cols)
        : data_(rows * cols), rows_(rows), cols_(cols) {}

    // C++23 multidimensional subscript operator
    T& operator[](std::size_t row, std::size_t col) {
        return data_[row * cols_ + col];
    }

    const T& operator[](std::size_t row, std::size_t col) const {
        return data_[row * cols_ + col];
    }

    // Single index still works
    T& operator[](std::size_t idx) {
        return data_[idx];
    }

    std::size_t rows() const { return rows_; }
    std::size_t cols() const { return cols_; }
};

// 3D Tensor with triple subscript
template<typename T>
class Tensor3D {
private:
    std::vector<T> data_;
    std::size_t dim1_, dim2_, dim3_;

public:
    Tensor3D(std::size_t d1, std::size_t d2, std::size_t d3)
        : data_(d1 * d2 * d3), dim1_(d1), dim2_(d2), dim3_(d3) {}

    // Triple subscript operator
    T& operator[](std::size_t i, std::size_t j, std::size_t k) {
        return data_[i * dim2_ * dim3_ + j * dim3_ + k];
    }

    const T& operator[](std::size_t i, std::size_t j, std::size_t k) const {
        return data_[i * dim2_ * dim3_ + j * dim3_ + k];
    }
};

// Variadic subscript operator
template<typename T>
class MultiArray {
private:
    std::vector<T> data_;

public:
    explicit MultiArray(std::size_t size) : data_(size) {}

    // Variadic subscript - any number of indices
    template<typename... Indices>
    T& operator[](Indices... indices) {
        std::size_t idx = 0;
        std::size_t mult = 1;
        ((idx += indices * mult, mult *= 10), ...);
        return data_[idx % data_.size()];
    }
};

// Static subscript operator (C++23 feature)
class StaticLookup {
public:
    static int operator[](int key) {
        return key * key;
    }
};

void test_multidim_subscript();

} // namespace cpp23::multidim_subscript

#endif // MULTIDIM_SUBSCRIPT_HPP

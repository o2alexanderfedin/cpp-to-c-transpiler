/**
 * @file vector_example.cpp
 * @brief Example demonstrating std::vector<int> transpilation
 *
 * Story #69: STL Container Support and Integration Testing
 *
 * This example shows how the transpiler handles std::vector<int> including:
 * - Template instantiation
 * - Name mangling (vector_int)
 * - Method translation (push_back, size, operator[])
 *
 * Expected C Output:
 * - typedef struct vector_int { int* data; int size_; int capacity_; }
 * - void vector_int_push_back(vector_int* this, const int* value)
 * - int vector_int_size(const vector_int* this)
 * - int* vector_int_operator[](vector_int* this, int index)
 */

#include <vector>

/**
 * Example 1: Basic std::vector<int> usage
 *
 * Demonstrates:
 * - Vector instantiation
 * - push_back method calls
 * - size method calls
 * - operator[] access
 */
void basicVectorUsage() {
    // Create a vector of integers
    std::vector<int> numbers;

    // Add elements using push_back
    numbers.push_back(10);
    numbers.push_back(20);
    numbers.push_back(30);

    // Get size
    int count = numbers.size();

    // Access elements using operator[]
    int first = numbers[0];
    int second = numbers[1];

    // Modify elements
    numbers[0] = 100;
}

/**
 * Example 2: Multiple vector types
 *
 * Demonstrates that the transpiler handles multiple instantiations:
 * - std::vector<int>
 * - std::vector<double>
 * - std::vector<float>
 *
 * Each gets a unique mangled name:
 * - vector_int
 * - vector_double
 * - vector_float
 */
void multipleVectorTypes() {
    std::vector<int> integers;
    std::vector<double> doubles;
    std::vector<float> floats;

    integers.push_back(42);
    doubles.push_back(3.14);
    floats.push_back(2.71f);

    int intCount = integers.size();
    int doubleCount = doubles.size();
    int floatCount = floats.size();
}

/**
 * Example 3: Vector as function parameter
 *
 * Shows how the transpiler handles:
 * - Pass by reference (pointer in C)
 * - const correctness
 */
void processVector(std::vector<int>& vec) {
    vec.push_back(999);
    int lastIndex = vec.size() - 1;
    vec[lastIndex] = 1000;
}

int countElements(const std::vector<int>& vec) {
    return vec.size();
}

/**
 * Example 4: Vector as return type
 *
 * Demonstrates return value handling
 */
std::vector<int> createVector() {
    std::vector<int> result;
    result.push_back(1);
    result.push_back(2);
    result.push_back(3);
    return result;
}

/**
 * Example 5: Nested vector access
 *
 * Shows complex operations with vectors
 */
void complexVectorOperations() {
    std::vector<int> data;

    // Build vector
    for (int i = 0; i < 10; i++) {
        data.push_back(i * 10);
    }

    // Process vector
    int sum = 0;
    for (int i = 0; i < data.size(); i++) {
        sum += data[i];
    }

    // Modify specific elements
    if (data.size() > 5) {
        data[5] = sum;
    }
}

/**
 * Main function to demonstrate all examples
 */
int main() {
    basicVectorUsage();
    multipleVectorTypes();

    std::vector<int> myVec;
    processVector(myVec);
    int count = countElements(myVec);

    std::vector<int> created = createVector();
    complexVectorOperations();

    return 0;
}

// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/temp_project/attributes.cpp
// Implementation file

#include "attributes.h"

namespace cpp23 {
        namespace attributes {
                inline int divide_positive(int a, int b) {
[[assume(b > 0)]]                        ;
                        return a / b;
                }
                inline void process_array(int *arr, int size) {
[[assume(arr != nullptr)]]                        ;
[[assume(size > 0)]]                        ;
                        for (int i = 0; i < size; ++i) {
                                arr[i] *= 2;
                        }
                }
                inline int compute(int x, int y) {
[[assume(x >= 0)]]                        ;
[[assume(y >= 0)]]                        ;
[[assume(x + y < 1000)]]                        ;
                        return x * x + y * y;
                }
                inline void labeled_blocks() {
                        bool done = false;
                        if (done)
                                goto block1_end;
                        {
                        }
                      block1_end:
                        ;
                        if (done)
                                goto block2_end;
                        {
                        }
                      block2_end:
                        ;
                }
                void test_attributes();
        }
}
namespace cpp23 {
        namespace attributes {
                void test_attributes() {
                        int result1 = divide_positive(100, 5);
                        int arr[] = {1, 2, 3, 4, 5};
                        process_array(arr, 5);
                        for (int i = 0; i < 5; ++i) {
                        }
                        int result2 = compute(3, 4);
                        labeled_blocks();
                }
        }
}
void cpp23_attributes_test_attributes() {
        int result1 = divide_positive(100, 5);
        int arr[] = {1, 2, 3, 4, 5};
        process_array(arr, 5);
        for (int i = 0; i < 5; ++i) {
        }
        int result2 = compute(3, 4);
        labeled_blocks();
}


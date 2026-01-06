#include "LinkedList.h"
#include <cstdio>

int main() {
    LinkedList<int> list;

    printf("LinkedList<int> Tests:\n");
    printf("  Initial size: %zu\n", list.size());
    printf("  Is empty: %s\n", list.isEmpty() ? "true" : "false");

    // Add elements
    list.push_back(10);
    list.push_back(20);
    list.push_back(30);
    printf("  After push_back(10, 20, 30): size = %zu\n", list.size());
    printf("  Front element: %d\n", list.front());

    // Add to front
    list.push_front(5);
    printf("  After push_front(5): size = %zu, front = %d\n", list.size(), list.front());

    // Remove from front
    list.pop_front();
    printf("  After pop_front(): size = %zu, front = %d\n", list.size(), list.front());

    // Test with different type
    LinkedList<float> floatList;
    floatList.push_back(1.5f);
    floatList.push_back(2.5f);
    floatList.push_back(3.5f);
    printf("\nLinkedList<float> Tests:\n");
    printf("  Size: %zu\n", floatList.size());
    printf("  Front: %.1f\n", floatList.front());

    // Validation
    bool passed = true;
    passed = passed && (list.size() == 3);
    passed = passed && (list.front() == 10);
    passed = passed && (!list.isEmpty());
    passed = passed && (floatList.size() == 3);
    passed = passed && (floatList.front() > 1.4f && floatList.front() < 1.6f);

    printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
    return passed ? 0 : 1;
}

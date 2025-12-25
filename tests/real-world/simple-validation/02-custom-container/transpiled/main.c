// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/02-custom-container/main.cpp
// Implementation file

#include "main.h"

int main() {
        int list;
        <recovery-expr>(printf, "LinkedList<int> Tests:\n");
        printf("  Initial size: %zu\n", <recovery-expr>().size());
        printf("  Is empty: %s\n", <recovery-expr>().isEmpty() ? "true" : "false");
        <recovery-expr>(list).push_back(10);
        <recovery-expr>(list).push_back(20);
        <recovery-expr>(list).push_back(30);
        printf("  After push_back(10, 20, 30): size = %zu\n", <recovery-expr>().size());
        printf("  Front element: %d\n", <recovery-expr>().front());
        <recovery-expr>(list).push_front(5);
        printf("  After push_front(5): size = %zu, front = %d\n", <recovery-expr>().size(), <recovery-expr>().front());
        <recovery-expr>(list).pop_front();
        printf("  After pop_front(): size = %zu, front = %d\n", <recovery-expr>().size(), <recovery-expr>().front());
        int floatList;
        <recovery-expr>(floatList).push_back(1.5F);
        <recovery-expr>(floatList).push_back(2.5F);
        <recovery-expr>(floatList).push_back(3.5F);
        <recovery-expr>(printf, "\nLinkedList<float> Tests:\n");
        printf("  Size: %zu\n", <recovery-expr>().size());
        printf("  Front: %.1f\n", <recovery-expr>().front());
        bool passed = true;
        passed = passed && (<recovery-expr>(list).size() == 3);
        passed = passed && (<recovery-expr>(list).front() == 10);
        passed = passed && (!<recovery-expr>().isEmpty());
        passed = passed && (<recovery-expr>(floatList).size() == 3);
        passed = passed && (<recovery-expr>(floatList).front() > 1.39999998F && <recovery-expr>().front() < 1.60000002F);
        <recovery-expr>(printf, "\nValidation: %s\n", passed ? "PASS" : "FAIL");
        return passed ? 0 : 1;
}



#include "main.h"

int main() {
	struct LinkedList list = (LinkedList<int>){};
	printf("LinkedList<int> Tests:\n");
	printf("  Initial size: %zu\n", size(list));
	printf("  Is empty: %s\n", isEmpty(list) ? "true" : "false");
	printf("  After push_back(10, 20, 30): size = %zu\n", size(list));
	printf("  Front element: %d\n", front(list));
	printf("  After push_front(5): size = %zu, front = %d\n", size(list), front(list));
	pop_front(list);
	printf("  After pop_front(): size = %zu, front = %d\n", size(list), front(list));
	struct LinkedList floatList = (LinkedList<float>){};
	printf("\nLinkedList<float> Tests:\n");
	printf("  Size: %zu\n", size(floatList));
	printf("  Front: %.1f\n", front(floatList));
	bool passed = 1;
	passed = passed && (LinkedList_size(list) == 3);
	passed = passed && (LinkedList_front(list) == 10);
	passed = passed && (!isEmpty(list));
	passed = passed && (LinkedList_size(floatList) == 3);
	passed = passed && (LinkedList_front(floatList) > 1.39999998F && LinkedList_front(floatList) < 1.60000002F);
	printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
	return passed ? 0 : 1;
;
}


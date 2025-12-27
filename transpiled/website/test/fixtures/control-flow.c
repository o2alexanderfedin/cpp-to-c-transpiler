// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./website/test/fixtures/control-flow.cpp
// Implementation file

#include "control-flow.h"

int factorial(int n) {
	if (n <= 1) 	{
		return 1;
;
	}

	return n * factorial(n - 1);
;
}

int fibonacci(int n) {
	if (n <= 1) 	{
		return n;
;
	}

	int a = 0;

	int b = 1;

	for (int i = 2; i <= n; i++) {
        int temp = a + b;
        a = b;
        b = temp;
}

	return b;
;
}

int findMax(int * arr, int size) {
	if (size <= 0) 	{
		return 0;
;
	}

	int max = arr[0];

	for (int i = 1; i < size; i++) {
        if (arr[i] > max) {
                max = arr[i];
        }
}

	return max;
;
}

void bubbleSort(int * arr, int size) {
	for (int i = 0; i < size - 1; i++) {
        for (int j = 0; j < size - i - 1; j++) {
                if (arr[j] > arr[j + 1]) {
                        int temp = arr[j];
                        arr[j] = arr[j + 1];
                        arr[j + 1] = temp;
                }
        }
}

}


// Basic test: Array fill function
// Expected ACSL: requires, ensures with quantifier, loop invariant

void fillArray(int* arr, int n, int value) {
    for (int i = 0; i < n; i++) {
        arr[i] = value;
    }
}

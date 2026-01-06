// Example 1: If statement
int max(int a, int b) {
    if (a > b) {
        return a;
    } else {
        return b;
    }
}

// Example 2: While loop
int sum_to_n(int n) {
    int sum = 0;
    int i = 1;
    while (i <= n) {
        sum = sum + i;
        i = i + 1;
    }
    return sum;
}

// Example 3: For loop
int factorial(int n) {
    int result = 1;
    for (int i = 1; i <= n; i++) {
        result = result * i;
    }
    return result;
}

// Example 4: Switch statement
int classify(int x) {
    switch (x) {
        case 0:
            return 1;
        case 1:
            return 2;
        default:
            return 0;
    }
}

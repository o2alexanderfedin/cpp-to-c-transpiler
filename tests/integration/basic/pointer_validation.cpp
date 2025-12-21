// Basic test: Pointer validation
// Expected ACSL: requires \valid(ptr), assigns clause

int safeDereference(int* ptr) {
    if (ptr != nullptr) {
        return *ptr;
    }
    return 0;
}

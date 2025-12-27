// Example: Simple template class
template<typename T>
class Box {
    T value;

public:
    Box(T v) : value(v) {}

    T getValue() {
        return value;
    }
};

// Instantiation
int test() {
    Box<int> intBox(42);
    return intBox.getValue();
}

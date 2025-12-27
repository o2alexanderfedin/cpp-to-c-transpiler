template<typename T>
class SimpleTemplate {
public:
    T value;
    SimpleTemplate(T v) : value(v) {}
    T getValue() { return value; }
};

int main() {
    SimpleTemplate<int> obj(42);
    return obj.getValue();
}

// Test file for dual layout generation
class Base {
public:
    int b;
};

class Derived : virtual Base {
public:
    int d;
};

int main() {
    Derived obj;
    obj.d = 42;
    return 0;
}

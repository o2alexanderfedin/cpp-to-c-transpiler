// Test case for virtual inheritance C1/C2 constructor generation
// This should trigger the circular dependency bug we're fixing

class Base {
public:
    int baseValue;
    Base() : baseValue(0) {}
};

class Derived : public virtual Base {
public:
    int derivedValue;
    Derived() : derivedValue(0) {}
};

int main() {
    Derived d;
    return 0;
}

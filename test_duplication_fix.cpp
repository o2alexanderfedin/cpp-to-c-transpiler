// Test file to verify Bug #11 fix
// This file combines a header declaration and implementation
// to test that we don't generate duplicate functions

// Header part (declaration without body)
class TestClass {
public:
    int getValue();  // Declaration only
};

// Implementation part (definition with body)
int TestClass::getValue() {
    return 42;
}

// When transpiled, we should get ONLY ONE function:
// int TestClass_getValue(struct TestClass* this) { return 42; }
// NOT two functions!

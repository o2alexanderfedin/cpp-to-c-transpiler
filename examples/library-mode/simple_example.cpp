// simple_example.cpp - Comprehensive C++ to C Runtime Example
// Demonstrates: exceptions, RTTI, virtual functions, inheritance, and RAII

#include <iostream>
#include <typeinfo>
#include <string>

// ============================================================================
// Base Class with Virtual Functions
// ============================================================================

class Shape {
public:
    Shape(const std::string& name) : name_(name) {
        std::cout << "Shape constructor: " << name_ << std::endl;
    }

    virtual ~Shape() {
        std::cout << "Shape destructor: " << name_ << std::endl;
    }

    // Virtual function for polymorphism
    virtual double area() const = 0;  // Pure virtual

    virtual void print() const {
        std::cout << "Shape: " << name_ << std::endl;
    }

    const std::string& getName() const { return name_; }

protected:
    std::string name_;
};

// ============================================================================
// Derived Classes
// ============================================================================

class Rectangle : public Shape {
public:
    Rectangle(double width, double height)
        : Shape("Rectangle"), width_(width), height_(height) {
        std::cout << "Rectangle constructor: " << width_ << "x" << height_ << std::endl;
    }

    ~Rectangle() override {
        std::cout << "Rectangle destructor" << std::endl;
    }

    double area() const override {
        return width_ * height_;
    }

    void print() const override {
        std::cout << "Rectangle: " << width_ << "x" << height_
                  << " (area: " << area() << ")" << std::endl;
    }

private:
    double width_;
    double height_;
};

class Circle : public Shape {
public:
    Circle(double radius)
        : Shape("Circle"), radius_(radius) {
        std::cout << "Circle constructor: radius=" << radius_ << std::endl;
    }

    ~Circle() override {
        std::cout << "Circle destructor" << std::endl;
    }

    double area() const override {
        return 3.14159 * radius_ * radius_;
    }

    void print() const override {
        std::cout << "Circle: radius=" << radius_
                  << " (area: " << area() << ")" << std::endl;
    }

private:
    double radius_;
};

// ============================================================================
// RAII Resource Management Example
// ============================================================================

class Resource {
public:
    Resource(const std::string& name) : name_(name) {
        std::cout << "Resource acquired: " << name_ << std::endl;
    }

    ~Resource() {
        std::cout << "Resource released: " << name_ << std::endl;
    }

private:
    std::string name_;
};

// ============================================================================
// Exception Handling Examples
// ============================================================================

void testExceptionHandling() {
    std::cout << "\n=== Testing Exception Handling ===" << std::endl;

    try {
        Resource r1("file.txt");
        Resource r2("database.db");

        std::cout << "About to throw exception..." << std::endl;
        throw std::runtime_error("Test exception");

        std::cout << "This should not print" << std::endl;
    } catch (const std::exception& e) {
        std::cout << "Caught exception: " << e.what() << std::endl;
        std::cout << "(Resources should be automatically released)" << std::endl;
    }
}

// ============================================================================
// RTTI (dynamic_cast and typeid) Examples
// ============================================================================

void testRTTI(Shape* shape) {
    std::cout << "\n=== Testing RTTI ===" << std::endl;

    // Test typeid operator
    std::cout << "Type of shape: " << typeid(*shape).name() << std::endl;

    // Test dynamic_cast to Rectangle
    Rectangle* rect = dynamic_cast<Rectangle*>(shape);
    if (rect) {
        std::cout << "Successfully cast to Rectangle" << std::endl;
        rect->print();
    } else {
        std::cout << "Failed to cast to Rectangle (expected)" << std::endl;
    }

    // Test dynamic_cast to Circle
    Circle* circle = dynamic_cast<Circle*>(shape);
    if (circle) {
        std::cout << "Successfully cast to Circle" << std::endl;
        circle->print();
    } else {
        std::cout << "Failed to cast to Circle (expected)" << std::endl;
    }
}

// ============================================================================
// Virtual Function and Polymorphism Test
// ============================================================================

void testPolymorphism(Shape* shape) {
    std::cout << "\n=== Testing Polymorphism ===" << std::endl;

    // Virtual function call through base pointer
    shape->print();
    std::cout << "Area: " << shape->area() << std::endl;
}

// ============================================================================
// Main Program
// ============================================================================

int main() {
    std::cout << "C++ to C Runtime Example" << std::endl;
    std::cout << "=========================" << std::endl;

    // Test with Rectangle
    {
        std::cout << "\n--- Creating Rectangle ---" << std::endl;
        Rectangle rect(10.0, 5.0);

        testPolymorphism(&rect);
        testRTTI(&rect);
    }

    // Test with Circle
    {
        std::cout << "\n--- Creating Circle ---" << std::endl;
        Circle circle(7.0);

        testPolymorphism(&circle);
        testRTTI(&circle);
    }

    // Test exception handling and RAII
    testExceptionHandling();

    std::cout << "\n=== Program completed successfully ===" << std::endl;
    return 0;
}

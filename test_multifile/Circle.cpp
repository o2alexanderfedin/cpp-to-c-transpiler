class Circle {
private:
    int radius;

public:
    Circle(int r) : radius(r) {}
    int getRadius() const { return radius; }
    void setRadius(int r) { radius = r; }
    int getArea() const { return 3 * radius * radius; }  // Simplified pi
};

class Rectangle {
    int width;
    int height;
public:
    Rectangle(int w, int h) : width(w), height(h) {}

    int getWidth() const { return width; }
    int getHeight() const { return height; }

    int area() const { return width * height; }
};

// Integration Test 3: Scoped Enums + Namespaces
// Tests: Nested namespaces with scoped enums
// Expected: Transpiles to C with proper enum prefixing and name mangling

#include <cassert>

namespace Graphics {
    namespace Color {
        enum class Primary {
            Red,
            Green,
            Blue
        };

        enum class Secondary {
            Cyan,
            Magenta,
            Yellow
        };
    }

    class Pixel {
        Color::Primary primary;
        int value;
    public:
        Pixel(Color::Primary p, int v) : primary(p), value(v) {}

        Color::Primary getPrimary() const {
            return primary;
        }

        int getValue() const {
            return value;
        }

        bool isRed() const {
            return primary == Color::Primary::Red;
        }

        bool isGreen() const {
            return primary == Color::Primary::Green;
        }

        bool isBlue() const {
            return primary == Color::Primary::Blue;
        }
    };
}

int main() {
    Graphics::Pixel redPixel(Graphics::Color::Primary::Red, 255);
    assert(redPixel.isRed());
    assert(!redPixel.isGreen());
    assert(!redPixel.isBlue());
    assert(redPixel.getValue() == 255);

    Graphics::Pixel greenPixel(Graphics::Color::Primary::Green, 128);
    assert(!greenPixel.isRed());
    assert(greenPixel.isGreen());
    assert(!greenPixel.isBlue());
    assert(greenPixel.getValue() == 128);

    return 0;
}

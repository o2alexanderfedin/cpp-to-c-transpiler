#ifndef DEDUCING_THIS_HPP
#define DEDUCING_THIS_HPP

#include <iostream>
#include <string>
#include <utility>

namespace cpp23::deducing_this {

// Feature: Deducing this (P0847) - Explicit object parameter
// This eliminates the need for const/non-const/lvalue/rvalue overload quadruplication

class TextBuffer {
private:
    std::string data_;

public:
    TextBuffer(std::string data) : data_(std::move(data)) {}

    // Single templated function replaces 4 overloads:
    // - T& get()
    // - const T& get() const
    // - T&& get() &&
    // - const T&& get() const &&
    template<typename Self>
    auto&& get(this Self&& self) {
        std::cout << "get() called with ";
        if constexpr (std::is_const_v<std::remove_reference_t<Self>>) {
            std::cout << "const ";
        }
        if constexpr (std::is_lvalue_reference_v<Self>) {
            std::cout << "lvalue\n";
        } else {
            std::cout << "rvalue\n";
        }
        return std::forward<Self>(self).data_;
    }

    // Explicit object parameter with specific type
    void print(this const TextBuffer& self) {
        std::cout << "Buffer content: " << self.data_ << "\n";
    }

    // By-value explicit object parameter (CRTP simplification)
    void modify(this TextBuffer self) {
        self.data_ += " [modified]";
        std::cout << "Modified (copy): " << self.data_ << "\n";
    }
};

// Simplified CRTP pattern with deducing this
template<typename T>
class CRTPBase {
public:
    void interface(this auto&& self) {
        std::forward<decltype(self)>(self).implementation();
    }
};

class CRTPDerived : public CRTPBase<CRTPDerived> {
public:
    void implementation() {
        std::cout << "CRTPDerived implementation\n";
    }
};

// Recursive lambda with deducing this
inline auto factorial_lambda() {
    return [](this auto self, int n) -> int {
        if (n <= 1) return 1;
        return n * self(n - 1);
    };
}

void test_deducing_this();

} // namespace cpp23::deducing_this

#endif // DEDUCING_THIS_HPP

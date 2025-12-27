// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/temp_project/deducing_this.cpp
// Implementation file

#include "deducing_this.h"

namespace cpp23 {
        namespace deducing_this {
                class TextBuffer {
                private:
                        int data_;
                public:
                        TextBuffer(int data) {
                        }
                        template <typename Self> auto &&get(this Self &&self) {
                                if (<recovery-expr>()) {
                                }
                                if (<recovery-expr>()) {
                                } else {
                                }
                        }
                        void print(this const TextBuffer &self) {
                        }
                        void modify(this TextBuffer self) {
                                <recovery-expr>(self) += " [modified]";
                        }
                };
                template <typename T> class CRTPBase {
                public:
                        void interface(this int &&self) {
                        }
                };
                class CRTPDerived {
                public:
                        void implementation() {
                        }
                };
                inline class (lambda at /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/temp_project/deducing_this.hpp:69:12) factorial_lambda() {
                        return [](auto self, int n) mutable -> int {
                                if (n <= 1)
                                        return 1;
                                return n * self(n - 1);
                        };
                }
                void test_deducing_this();
        }
}
namespace cpp23 {
        namespace deducing_this {
                void test_deducing_this() {
                        TextBuffer buf1 = <recovery-expr>("Hello");
                        auto &ref = <recovery-expr>(buf1.get);
                        const TextBuffer buf2 = <recovery-expr>("World");
                        auto &cref = <recovery-expr>(buf2.get);
                        auto &&rref = <recovery-expr>(<recovery-expr>("Temporary").get);
                        print(buf1);
                        modify(buf1);
                        print(buf1);
                        CRTPDerived derived;
                        <recovery-expr>(derived)();
                        auto fact = factorial_lambda();
                }
        }
}
void cpp23_deducing_this_test_deducing_this() {
        TextBuffer buf1 = <recovery-expr>("Hello");
        auto &ref = <recovery-expr>(buf1.get);
        const TextBuffer buf2 = <recovery-expr>("World");
        auto &cref = <recovery-expr>(buf2.get);
        auto &&rref = <recovery-expr>(<recovery-expr>("Temporary").get);
        print(buf1);
        modify(buf1);
        print(buf1);
        CRTPDerived derived;
        <recovery-expr>(derived)();
        auto fact = factorial_lambda();
}


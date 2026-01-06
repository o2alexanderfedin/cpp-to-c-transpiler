// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/temp_project/literals.cpp
// Header file

namespace cpp23 {
        namespace literals {
                inline void test_size_t_literals() {
                        auto s1 = 42UL;
                        auto s2 = 100UL;
                        auto s3 = 255UL;
                }
                inline void test_named_escapes() {
                        const char *smiley = "\360\237\230\200";
                        const char *heart = "\342\235\244";
                        int message = <recovery-expr>("Hello \360\237\221\213");
                }
                void test_literals();
        }
}
namespace cpp23 {
        namespace literals {
                void test_literals() {
                        test_size_t_literals();
                }
        }
}
void cpp23_literals_test_literals();

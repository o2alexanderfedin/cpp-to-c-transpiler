// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/temp_project/consteval_if.cpp
// Implementation file

#include "consteval_if.h"

namespace cpp23 {
        namespace consteval_if {
                int compile_time_only(int x) {
                        return x * x;
                }
                constexpr int flexible_compute(int x) {
                }
                constexpr void debug_log(const char *msg) {
                }
                int square_consteval(int x) {
                        return x * x;
                }
                constexpr int compute_with_logging(int x) {
                }
                constexpr int runtime_preferred(int x) {
                }
                void test_consteval_if();
        }
}
namespace cpp23 {
        namespace consteval_if {
                void test_consteval_if() {
                        constexpr int ct_result;
                        int x = 5;
                        int rt_result;
                        debug_log("This appears only at runtime");
                        constexpr int sq;
                        constexpr int ct_logged;
                        int rt_logged;
                        int pref;
                }
        }
}
void cpp23_consteval_if_test_consteval_if() {
        constexpr int ct_result;
        int x = 5;
        int rt_result;
        debug_log("This appears only at runtime");
        constexpr int sq;
        constexpr int ct_logged;
        int rt_logged;
        int pref;
}


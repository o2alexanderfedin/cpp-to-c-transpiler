// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/main.cpp
// Implementation file

#include "main.h"

int main() {
        int eval;
        <recovery-expr>(printf, "Expression Evaluator Tests:\n");
        const char *expr1 = "2 + 3";
        int result1 = <recovery-expr>().evaluate(expr1);
        <recovery-expr>(printf, "  %s = %d\n", expr1, result1);
        const char *expr2 = "10 - 4";
        int result2 = <recovery-expr>().evaluate(expr2);
        <recovery-expr>(printf, "  %s = %d\n", expr2, result2);
        const char *expr3 = "2 * 3 + 4";
        int result3 = <recovery-expr>().evaluate(expr3);
        <recovery-expr>(printf, "  %s = %d\n", expr3, result3);
        const char *expr4 = "20 / 4";
        int result4 = <recovery-expr>().evaluate(expr4);
        <recovery-expr>(printf, "  %s = %d\n", expr4, result4);
        const char *expr5 = "2 + 3 * 4";
        int result5 = <recovery-expr>().evaluate(expr5);
        <recovery-expr>(printf, "  %s = %d\n", expr5, result5);
        bool passed = true;
        passed = passed && (result1 == 5);
        passed = passed && (result2 == 6);
        passed = passed && (result3 == 10);
        passed = passed && (result4 == 5);
        passed = passed && (result5 == 14);
        <recovery-expr>(printf, "\nValidation: %s\n", passed ? "PASS" : "FAIL");
        return passed ? 0 : 1;
}


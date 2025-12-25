// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/01-math-library/main.cpp
// Implementation file

#include "main.h"

int main() {
        int v1 = <recovery-expr>((1.F, 2.F, 3.F));
        int v2 = <recovery-expr>((4.F, 5.F, 6.F));
        int sum = <recovery-expr>(<recovery-expr>().add(<recovery-expr>()));
        float dot = <recovery-expr>().dot(<recovery-expr>());
        int cross = <recovery-expr>(<recovery-expr>().cross(<recovery-expr>()));
        <recovery-expr>(printf, "Vector3D Tests:\n");
        printf("  v1 = (%.1f, %.1f, %.1f)\n", <recovery-expr>().x, <recovery-expr>().y, <recovery-expr>().z);
        printf("  v2 = (%.1f, %.1f, %.1f)\n", <recovery-expr>().x, <recovery-expr>().y, <recovery-expr>().z);
        printf("  v1 + v2 = (%.1f, %.1f, %.1f)\n", <recovery-expr>().x, <recovery-expr>().y, <recovery-expr>().z);
        <recovery-expr>(printf, "  v1 . v2 = %.1f\n", dot);
        printf("  v1 x v2 = (%.1f, %.1f, %.1f)\n", <recovery-expr>().x, <recovery-expr>().y, <recovery-expr>().z);
        int m1 = <recovery-expr>((1, 0, 0, 0, 1, 0, 0, 0, 1));
        int m2 = <recovery-expr>((2, 0, 0, 0, 2, 0, 0, 0, 2));
        int mProd = <recovery-expr>(<recovery-expr>().multiply(<recovery-expr>()));
        int transformed = <recovery-expr>(<recovery-expr>().multiply(<recovery-expr>()));
        <recovery-expr>(printf, "\nMatrix3x3 Tests:\n");
        printf("  Identity * 2I = 2I (first element: %.1f)\n", <recovery-expr>().get(0, 0));
        printf("  2I * v1 = (%.1f, %.1f, %.1f)\n", <recovery-expr>().x, <recovery-expr>().y, <recovery-expr>().z);
        bool passed = true;
        passed = passed && (fabsf(<recovery-expr>().x - 5.F) < 0.00100000005F);
        passed = passed && (fabsf(<recovery-expr>().y - 7.F) < 0.00100000005F);
        passed = passed && (fabsf(<recovery-expr>().z - 9.F) < 0.00100000005F);
        passed = passed && (<recovery-expr>(fabsf, dot - 32.F) < 0.00100000005F);
        passed = passed && (fabsf(<recovery-expr>().x - (-3.F)) < 0.00100000005F);
        passed = passed && (fabsf(<recovery-expr>().y - 6.F) < 0.00100000005F);
        passed = passed && (fabsf(<recovery-expr>().z - (-3.F)) < 0.00100000005F);
        passed = passed && (fabsf(<recovery-expr>().get(0, 0) - 2.F) < 0.00100000005F);
        passed = passed && (fabsf(<recovery-expr>().x - 2.F) < 0.00100000005F);
        <recovery-expr>(printf, "\nValidation: %s\n", passed ? "PASS" : "FAIL");
        return passed ? 0 : 1;
}



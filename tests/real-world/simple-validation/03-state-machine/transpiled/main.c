// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/03-state-machine/main.cpp
// Implementation file

#include "main.h"

const char * stateToString(int state) {
        switch (<recovery-expr>(state)) {
                return "Menu";
                return "Playing";
                return "Paused";
                return "GameOver";
              default:
                return "Unknown";
        }
}


int main() {
        int sm(int);
        <recovery-expr>(printf, "State Machine Tests:\n");
        <recovery-expr>(printf, "  Initial state: %s\n");
        <recovery-expr>(<recovery-expr>(sm).transition);
        <recovery-expr>(printf, "  After Menu -> Playing: %s\n");
        <recovery-expr>(<recovery-expr>(sm).transition);
        <recovery-expr>(printf, "  After Playing -> Paused: %s\n");
        <recovery-expr>(<recovery-expr>(sm).transition);
        <recovery-expr>(printf, "  After Paused -> Playing: %s\n");
        <recovery-expr>(<recovery-expr>(sm).transition);
        <recovery-expr>(printf, "  After Playing -> GameOver: %s\n");
        <recovery-expr>(<recovery-expr>(sm).transition);
        <recovery-expr>(printf, "  After GameOver -> Playing (invalid): %s\n");
        <recovery-expr>(<recovery-expr>(sm).transition);
        <recovery-expr>(printf, "  After GameOver -> Menu: %s\n");
        printf("  Total valid transitions: %d\n", <recovery-expr>().getTransitionCount());
        bool passed = true;
        passed = passed && (<recovery-expr>(sm).getTransitionCount() == 5);
        <recovery-expr>(printf, "\nValidation: %s\n", passed ? "PASS" : "FAIL");
        return passed ? 0 : 1;
}



// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/05-game-logic/main.cpp
// Implementation file

#include "main.h"

int main() {
        <recovery-expr>(printf, "Game Logic Tests:\n");
        int player = <recovery-expr>((100.F, 100.F));
        int enemy = <recovery-expr>((150.F, 100.F));
        printf("  Player: pos=(%.1f, %.1f), health=%d, score=%d\n", <recovery-expr>().getX(), <recovery-expr>().getY(), <recovery-expr>().getHealth(), <recovery-expr>().getScore());
        printf("  Enemy: pos=(%.1f, %.1f), damage=%d\n", <recovery-expr>().getX(), <recovery-expr>().getY(), <recovery-expr>().getDamage());
        bool colliding1;
        <recovery-expr>(printf, "  Initial collision: %s\n", colliding1 ? "true" : "false");
        <recovery-expr>(enemy).setPosition(110.F, 100.F);
        bool colliding2;
        <recovery-expr>(printf, "  After enemy moves to (110, 100): collision = %s\n", colliding2 ? "true" : "false");
        printf("  Player takes %d damage\n", <recovery-expr>().getDamage());
        <recovery-expr>(player).takeDamage(<recovery-expr>().getDamage());
        printf("  Player health after damage: %d\n", <recovery-expr>().getHealth());
        <recovery-expr>(player).addScore(100);
        printf("  Player score after +100: %d\n", <recovery-expr>().getScore());
        bool inside;
        <recovery-expr>(printf, "  Point (115, 115) inside player: %s\n", inside ? "true" : "false");
        bool passed = true;
        passed = passed && (<recovery-expr>(player).getHealth() == 90);
        passed = passed && (<recovery-expr>(player).getScore() == 100);
        passed = passed && (colliding1 == false);
        passed = passed && (colliding2 == true);
        passed = passed && (inside == true);
        <recovery-expr>(printf, "\nValidation: %s\n", passed ? "PASS" : "FAIL");
        return passed ? 0 : 1;
}


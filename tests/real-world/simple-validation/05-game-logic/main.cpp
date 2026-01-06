#include "Player.h"
#include "Enemy.h"
#include "CollisionDetector.h"
#include <cstdio>

int main() {
    printf("Game Logic Tests:\n");

    // Create entities
    Player player(100.0f, 100.0f);
    Enemy enemy(150.0f, 100.0f);

    printf("  Player: pos=(%.1f, %.1f), health=%d, score=%d\n",
           player.getX(), player.getY(), player.getHealth(), player.getScore());
    printf("  Enemy: pos=(%.1f, %.1f), damage=%d\n",
           enemy.getX(), enemy.getY(), enemy.getDamage());

    // Test collision detection
    bool colliding1 = CollisionDetector::checkCollision(player, enemy);
    printf("  Initial collision: %s\n", colliding1 ? "true" : "false");

    // Move enemy closer
    enemy.setPosition(110.0f, 100.0f);
    bool colliding2 = CollisionDetector::checkCollision(player, enemy);
    printf("  After enemy moves to (110, 100): collision = %s\n",
           colliding2 ? "true" : "false");

    // Test damage
    printf("  Player takes %d damage\n", enemy.getDamage());
    player.takeDamage(enemy.getDamage());
    printf("  Player health after damage: %d\n", player.getHealth());

    // Test score
    player.addScore(100);
    printf("  Player score after +100: %d\n", player.getScore());

    // Test point inside
    bool inside = CollisionDetector::pointInside(115.0f, 115.0f, player);
    printf("  Point (115, 115) inside player: %s\n", inside ? "true" : "false");

    // Validation
    bool passed = true;
    passed = passed && (player.getHealth() == 90);
    passed = passed && (player.getScore() == 100);
    passed = passed && (colliding1 == false);  // Initially not colliding
    passed = passed && (colliding2 == true);   // After move, colliding
    passed = passed && (inside == true);

    printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
    return passed ? 0 : 1;
}

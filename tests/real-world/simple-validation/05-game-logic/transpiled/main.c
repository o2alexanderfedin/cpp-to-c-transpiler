#include "main.h"

int main() {
	printf("Game Logic Tests:\n");
	struct Player player = (struct Player){100.F, 100.F};
	struct Enemy enemy = (struct Enemy){150.F, 100.F};
	printf("  Player: pos=(%.1f, %.1f), health=%d, score=%d\n", getX(&player), getY(&player), getHealth(&player), getScore(&player));
	printf("  Enemy: pos=(%.1f, %.1f), damage=%d\n", getX(&enemy), getY(&enemy), getDamage(&enemy));
	bool colliding1 = checkCollision(player, enemy);
	printf("  Initial collision: %s\n", colliding1 ? "true" : "false");
	setPosition(&enemy, 110.F, 100.F);
	bool colliding2 = checkCollision(player, enemy);
	printf("  After enemy moves to (110, 100): collision = %s\n", colliding2 ? "true" : "false");
	printf("  Player takes %d damage\n", getDamage(&enemy));
	takeDamage(&player, getDamage(&enemy));
	printf("  Player health after damage: %d\n", getHealth(&player));
	addScore(&player, 100);
	printf("  Player score after +100: %d\n", getScore(&player));
	bool inside = pointInside(115.F, 115.F, player);
	printf("  Point (115, 115) inside player: %s\n", inside ? "true" : "false");
	bool passed = 1;
	passed = passed && (Player_getHealth(&player) == 90);
	passed = passed && (Player_getScore(&player) == 100);
	passed = passed && (colliding1 == 0);
	passed = passed && (colliding2 == 1);
	passed = passed && (inside == 1);
	printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
	return passed ? 0 : 1;
;
}


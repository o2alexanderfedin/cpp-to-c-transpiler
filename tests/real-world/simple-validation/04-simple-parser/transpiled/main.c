#include "main.h"

int main() {
	struct ExpressionEvaluator eval = (struct ExpressionEvaluator){};
	printf("Expression Evaluator Tests:\n");
	const char * expr1 = "2 + 3";
	int result1 = ExpressionEvaluator_evaluate(eval, expr1);
	printf("  %s = %d\n", expr1, result1);
	const char * expr2 = "10 - 4";
	int result2 = ExpressionEvaluator_evaluate(eval, expr2);
	printf("  %s = %d\n", expr2, result2);
	const char * expr3 = "2 * 3 + 4";
	int result3 = ExpressionEvaluator_evaluate(eval, expr3);
	printf("  %s = %d\n", expr3, result3);
	const char * expr4 = "20 / 4";
	int result4 = ExpressionEvaluator_evaluate(eval, expr4);
	printf("  %s = %d\n", expr4, result4);
	const char * expr5 = "2 + 3 * 4";
	int result5 = ExpressionEvaluator_evaluate(eval, expr5);
	printf("  %s = %d\n", expr5, result5);
	bool passed = 1;
	passed = passed && (result1 == 5);
	passed = passed && (result2 == 6);
	passed = passed && (result3 == 10);
	passed = passed && (result4 == 5);
	passed = passed && (result5 == 14);
	printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
	return passed ? 0 : 1;
;
}


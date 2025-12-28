// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/main.cpp
// Implementation file

#include "main.h"

static void Token__ctor_copy(struct Token * this, const struct Token * other) {
	this->type = other->type;
	this->value = other->value;
}

void Token__ctor(struct Token * this, TokenType t, int v) {
	this->type = t;
	this->value = v;
}

static void Tokenizer__ctor_copy(struct Tokenizer * this, const struct Tokenizer * other) {
	this->input = other->input;
	this->position = other->position;
}

static void ExpressionEvaluator__ctor_copy(struct ExpressionEvaluator * this, const struct ExpressionEvaluator * other) {
	this->tokenizer = other->tokenizer;
	Token__ctor_copy(&this->currentToken, &other->currentToken);
}

void ExpressionEvaluator__dtor(struct ExpressionEvaluator * this) {
}

int ExpressionEvaluator_evaluate(struct ExpressionEvaluator * this, const char * expression);
int main() {
	struct ExpressionEvaluator eval;
	printf("Expression Evaluator Tests:\n");
	const char * expr1 = "2 + 3";
	int result1 = ExpressionEvaluator_evaluate(&eval, expr1);
	printf("  %s = %d\n", expr1, result1);
	const char * expr2 = "10 - 4";
	int result2 = ExpressionEvaluator_evaluate(&eval, expr2);
	printf("  %s = %d\n", expr2, result2);
	const char * expr3 = "2 * 3 + 4";
	int result3 = ExpressionEvaluator_evaluate(&eval, expr3);
	printf("  %s = %d\n", expr3, result3);
	const char * expr4 = "20 / 4";
	int result4 = ExpressionEvaluator_evaluate(&eval, expr4);
	printf("  %s = %d\n", expr4, result4);
	const char * expr5 = "2 + 3 * 4";
	int result5 = ExpressionEvaluator_evaluate(&eval, expr5);
	printf("  %s = %d\n", expr5, result5);
	bool passed = true;
	passed = passed && (result1 == 5);
	passed = passed && (result2 == 6);
	passed = passed && (result3 == 10);
	passed = passed && (result4 == 5);
	passed = passed && (result5 == 14);
	printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
	return passed ? 0 : 1;
;
	ExpressionEvaluator__dtor(&eval);
}


#include "ExpressionEvaluator.h"

void ExpressionEvaluator__advance__void(struct ExpressionEvaluator * this) {
}

int ExpressionEvaluator__parseFactor__void(struct ExpressionEvaluator * this) {
	if (this->currentToken.type == Number) 	{
		int value = this->currentToken.value;
		ExpressionEvaluator__advance__void(this);
		return value;
;
	}

	return 0;
;
}

int ExpressionEvaluator__parseTerm__void(struct ExpressionEvaluator * this) {
	int left = ExpressionEvaluator__parseFactor__void(this);
	while (this->currentToken.type == Multiply || this->currentToken.type == Divide) 	{
		TokenType op = this->currentToken.type;
		ExpressionEvaluator__advance__void(this);
		int right = ExpressionEvaluator__parseFactor__void(this);
		if (op == Multiply) 		{
			left = left * right;
		}
 else 		{
			left = left / right;
		}

	}
	return left;
;
}

int ExpressionEvaluator__evaluate__constcharptr(struct ExpressionEvaluator * this, const char * expression) {
	if (this->tokenizer != 0) 	{
	}

	this->tokenizer = 0;
	ExpressionEvaluator__advance__void(this);
	int result = ExpressionEvaluator__parseTerm__void(this);
	while (this->currentToken.type == Plus || this->currentToken.type == Minus) 	{
		TokenType op = this->currentToken.type;
		ExpressionEvaluator__advance__void(this);
		int right = ExpressionEvaluator__parseTerm__void(this);
		if (op == Plus) 		{
			result = result + right;
		}
 else 		{
			result = result - right;
		}

	}
	return result;
;
}


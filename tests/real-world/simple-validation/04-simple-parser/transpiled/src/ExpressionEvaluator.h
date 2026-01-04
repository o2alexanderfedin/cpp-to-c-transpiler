#pragma once

void ExpressionEvaluator__advance__void(struct ExpressionEvaluator * this);
int ExpressionEvaluator__parseFactor__void(struct ExpressionEvaluator * this);
int ExpressionEvaluator__parseTerm__void(struct ExpressionEvaluator * this);
int ExpressionEvaluator__evaluate__constcharptr(struct ExpressionEvaluator * this, const char * expression);

// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/src/Tokenizer.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/Token.h"

void Tokenizer__ctor_1(struct Tokenizer * this, const char * input);
extern void Tokenizer_skipWhitespace(struct Tokenizer * this);
extern int Tokenizer_parseNumber(struct Tokenizer * this);
extern struct Token Tokenizer_nextToken(struct Tokenizer * this);
extern bool Tokenizer_hasMore(struct Tokenizer * this);

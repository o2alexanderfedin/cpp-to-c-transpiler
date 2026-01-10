#include "StateMachine.h"

void StateMachine__transition__enumGameState(struct StateMachine * this, enum GameState newState) {
	if (StateMachine_isValidTransition(&this, this->currentState, newState)) 	{
		this->currentState = newState;
		this->transitionCount++;
	}

}

enum GameState StateMachine__getCurrentState__void(struct StateMachine * this) {
	return this->currentState;
;
}

int StateMachine__getTransitionCount__void(struct StateMachine * this) {
	return this->transitionCount;
;
}

bool StateMachine__isValidTransition__enumGameState_enumGameState(struct StateMachine * this, enum GameState from, enum GameState to) {
	switch (from) 	{
	}

}


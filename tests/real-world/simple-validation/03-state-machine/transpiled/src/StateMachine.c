#include "StateMachine.h"

void StateMachine__transition__GameState(struct StateMachine * this, GameState newState) {
	if (StateMachine_isValidTransition(this, this->currentState, newState)) 	{
		this->currentState = newState;
		this->transitionCount++;
	}

}

GameState StateMachine__getCurrentState__void(struct StateMachine * this) {
	return this->currentState;
;
}

int StateMachine__getTransitionCount__void(struct StateMachine * this) {
	return this->transitionCount;
;
}

bool StateMachine__isValidTransition__GameState_GameState(struct StateMachine * this, GameState from, GameState to) {
	switch (from) 	{
	}

}


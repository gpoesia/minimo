#!/usr/bin/env python3
# Wrapper for PyProofAction that allows for sequences of actions to be chained together.

import functools

import peano


class ProofAction:
    def __init__(self, peano_actions: list):
        self._actions = peano_actions

    def __str__(self) -> str:
        return ' => '.join(map(str, self._actions))

    def __repr__(self) -> str:
        return str(self)

    def __eq__(self, rhs) -> bool:
        return isinstance(rhs, ProofAction) and self._actions == rhs._actions

    def is_intro(self) -> bool:
        return len(self._actions) == 1 and self._actions[0].is_intro()

    def is_construct(self):
        return len(self._actions) <= 2 and self._actions[0].is_construct()

    def is_apply(self):
        return len(self._actions) <= 2 and self._actions[0].is_apply()

    def execute(self, state: peano.PyProofState) -> peano.PyProofState:
        return functools.reduce(lambda s, a: s[0].execute_action(a),
                                self._actions, [state])

    def is_eager(self):
        return self.is_intro() or len(self._actions) == 2

    def arrow_name(self):
        assert not self.is_intro()
        return str(self._actions[0]).split()[1]

    def construction_dtype(self):
        c_a = (self._actions[1]
               if self._actions[0].is_construct()
               else self._actions[0])
        dtype, _value = c_a.selected_construction()
        return str(dtype)


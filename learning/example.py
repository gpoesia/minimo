#!/usr/bin/env python3

"""
Example of
1- Setting up an environment for proof search
2- Running MCTS on a simple example, finding a proof
3- Reconstructing the proof from the search tree

Usage:

# Run the default example
python example.py

# Run the second example
python example.py 1
"""

import sys
import peano
from proofsearch import MonteCarloTreeSearch, TreeSearchNode, HolophrasmNode, UniformPolicy
from util import format_blocks_with_indent


EXAMPLES = [
    {
        "theory": """
= : [('t : type) -> 't -> 't -> prop].

nat : type.

z : nat.
s : [nat -> nat].

+ : [nat -> nat -> nat].
* : [nat -> nat -> nat].

+_z : [('n : nat) -> (= (+ 'n z) 'n)].
+_s : [('n : nat) -> ('m : nat) -> (= (+ 'n (s 'm)) (s (+ 'n 'm)))].

nat_ind : [('p : [nat -> prop]) -> ('p z) -> [('n : nat) -> ('p 'n) -> ('p (s 'n))] -> [('n : nat) -> ('p 'n)]].

#backward nat_ind.
#forward +_z ((+ 'n z) : nat).
#forward +_s ((+ 'n (s 'm)) : nat).
""",
        "premises": ['+_z', '+_s', 'rewrite'],
        "statement": '(= (+ (s z) (s z)) (s (s z)))'
    },

    {"theory": """
prop : type.

false : prop.

/* Connectives */
not : [prop -> prop].
and : [prop -> prop -> prop].
or : [prop -> prop -> prop].
iff : [prop -> prop -> prop].

/* Introduction rule for conjunction */
#backward and_i.
and_i : [('P : prop) -> ('Q : prop) -> 'P -> 'Q -> (and 'P 'Q)].
/* Elimination rules for conjunction */
#forward and_el ('_ : (and 'P 'Q)).
and_el : [('P : prop) -> ('Q : prop) -> (and 'P 'Q) -> 'P].
#forward and_er ('_ : (and 'P 'Q)).
and_er : [('P : prop) -> ('Q : prop) -> (and 'P 'Q) -> 'Q].

/* Introduction rules for disjunction */
#backward or_il.
or_il : [('P : prop) -> ('Q : prop) -> 'P -> (or 'P 'Q)].
#backward or_ir.
or_ir : [('P : prop) -> ('Q : prop) -> 'Q -> (or 'P 'Q)].
/* Elimination rule for disjunction */
#backward or_e infer infer infer infer subgoal subgoal.
or_e : [('P : prop) -> ('Q : prop) -> ('R : prop) ->
        (or 'P 'Q) -> ['P -> 'R] -> ['Q -> 'R] -> 'R].

/* Introduction rule for negation */
#backward not_i.
not_i : [('P : prop) -> ['P -> false] -> (not 'P)].
/* Elimination rule for negation */
not_e : [('P : prop) -> (not 'P) -> 'P -> false].
#backward exfalso.
exfalso : [false -> ('P : prop) -> 'P].

/* Introduction rules for equivalence */
#backward iff_i.
iff_i : [('P : prop) -> ('Q : prop) -> ['P -> 'Q] -> ['Q -> 'P] -> (iff 'P 'Q)].
/* Elimination rules for equivalence */
#forward iff_el ('_ : (iff 'P 'Q)).
iff_el : [('P : prop) -> ('Q : prop) -> (iff 'P 'Q) -> ['P -> 'Q]].
#forward iff_er ('_ : (iff 'P 'Q)).
iff_er : [('P : prop) -> ('Q : prop) -> (iff 'P 'Q) -> ['Q -> 'P]].

/* Excluded middle */
#forward em.
em : [('P : prop) -> (or 'P (not 'P))].
     """,
     "premises": ['and_i', 'and_el', 'and_er', 'or_il', 'or_ir', 'or_e',
                'not_i', 'not_e', 'exfalso', 'iff_i', 'iff_el', 'iff_er', 'em'],
     "statement": "(iff false false)",
     }
]


EXAMPLE = EXAMPLES[int(sys.argv[1]) if len(sys.argv) > 1 else 0]
initial_state = peano.PyProofState(EXAMPLE["theory"],
                                   EXAMPLE["premises"],
                                   EXAMPLE["statement"])

root = TreeSearchNode(HolophrasmNode([initial_state]))

mcts = MonteCarloTreeSearch(UniformPolicy({}))
solved, pi, _, it = mcts.evaluate(root)

assert solved

print(format_blocks_with_indent(root.reconstruct_proof()))

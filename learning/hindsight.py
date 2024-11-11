#!/usr/bin/env python3

from dataclasses import dataclass
import random

from omegaconf import DictConfig

import problems
import logging
import peano
import proofsearch
from action import ProofAction
from util import format_blocks_with_indent

log = logging.getLogger(__name__)

@dataclass
class HindsightExample:
    goal: str
    statement: str
    proof: list[str]
    solution_actions: list[str]
    logprob: float
    examples: list[str]


def extract_hindsight_examples(root,
                               theory: str,
                               premises: list[str],
                               pi: proofsearch.Policy,
                               max_goals: int = 50) -> list[dict]:
    # 1- Find distinct goals - map goal to terminal node
    goals_to_node = find_distinct_goals(root)
    # Sample goals
    goals_to_node = dict(random.sample(list(goals_to_node.items()), min(max_goals, len(goals_to_node))))

    # 2- For each node, find subtree root and path from root to node
    hindsight_examples = []

    for goal, node in goals_to_node.items():
        subtree_root, path = find_subtree_root(node)
        # NOTE: For now, we only consider paths that have no new constructions
        # in them. Handling constructions is possible but needs more work
        # because removing other irrelevant constructions will change names.
        if _path_has_construction(node, subtree_root):
            continue
        if not subtree_root.state_node._proof_states[0].is_context_empty():
            # NOTE: We can generalize this by adding whatever is in context as arguments.
            # The goal will still be provable after enough intros.
            continue
        # 3- Hindsight relabel path.
        states_on_path = node.hindsight_relabel(goal, subtree_root, [])

        if not states_on_path:
            continue

        # 4- Get generalized theorem statement from goal root
        try:
            new_root_state = peano.PyProofState(theory,
                                                premises,
                                                states_on_path[0][0].goal())
        except:
            log.error('Could not generalize theorem statement')
            raise ValueError("Could not generalize theorem statement")

        new_root = proofsearch.HolophrasmNode([new_root_state])
        cleaned_path = traverse_path(new_root, path)

        if cleaned_path:
            # 5- Run MCTS from goal root
            cleaned_path = minimize_path(new_root, cleaned_path)
            mcts_root = proofsearch.TreeSearchNode(new_root)
            pi_star = get_policy(new_root, cleaned_path)
            mcts = proofsearch.MonteCarloTreeSearch(pi_star)
            success = False

            # Run MCTS until success. This should be fast and typically only take
            # one iteration, since we're using the optimal policy. It only takes
            # more iterations because MCTS will force some exploration.
            for _ in range(10):
                success, _, _, _ = mcts.evaluate(mcts_root, verbose=False)
                if success:
                    break

            assert success, 'Hindsight MCTS failed'

            examples = pi.extract_examples(mcts_root)

            # 6- Extract examples
            hindsight_examples.append(HindsightExample(
                goal=goal,
                statement=states_on_path[0][0].goal(),
                proof=mcts_root.reconstruct_proof(),
                solution_actions=list(map(str, mcts_root.get_solution_actions())),
                logprob=mcts_root.solution_logprob_under_policy(pi),
                examples=examples,
            ))

    return hindsight_examples


def find_distinct_goals(root) -> dict:
    goals_to_node = {}

    for child in root:
        if child._state._proof_states:
            dtype = child._state._proof_states[0].last_proven_proposition()
            if dtype:
                goals_to_node[dtype] = child

    return goals_to_node


def traverse_path(node, path) -> list[ProofAction]:
    taken_path = []
    for i, action in enumerate(path):
        found, taken_action, lookahead_failed = False, None, False

        for a in node.actions:
            if action == a:
                found = True
                taken_action = a

                if a.is_construct() or a.is_apply():
                    if i + 1 >= len(path):
                        lookahead_failed = True
                    else:
                        # In case this is effectively a two-step action 
                        # (apply or construct), ensure the follow-up is valid.
                        lookahead_action = path[i+1]
                        lookahead_failed = (lookahead_action not in 
                                            node.expand(taken_action).actions)
                break

        if not found or lookahead_failed:
            continue

        node = node.expand(taken_action)
        taken_path.append(taken_action)

        # If no successors, proof went through.
        if node.is_terminal():
            return taken_path

    return None


def minimize_path(node, path):
    for i in range(len(path) - 2, -1, -1):
        new_path = None
        if path[i].is_intro():
            new_path = traverse_path(node, path[:i] + path[i+1:])
        if path[i].is_construct():
            new_path = traverse_path(node, path[:i] + path[i+2:])
        if new_path:
            return minimize_path(node, new_path)
    return path


class PathFollowingPolicy(proofsearch.Policy):
    def __init__(self, pi: dict[str, str]):
        self._pi = pi

    def evaluate(self, node):
        return ([int(str(c.state_node) in self._pi) for c in node._children],
                1000*int(str(node.state_node) in self._pi))


def get_policy(node, path) -> dict[str, str]:
    policy = {}

    for action in path:
        if action not in node.actions:
            raise NotImplementedError("Action not in node actions")
        assert action in node.actions
        policy[str(node)] = str(action)
        node = node.expand(action)

    return PathFollowingPolicy(policy)


def _is_apply(action):
    return isinstance(action, ProofAction) and action.is_apply()

def _is_construct(action):
    return isinstance(action, ProofAction) and action.is_construct()

def _path_has_construction(node, root):
    while node != root and node._parent[0] != root:
        if isinstance(node._parent[0]._parent[1], ProofAction) and \
           node._parent[0]._parent[1].is_construct() and \
           node._state._proof_states[0].last_proven_proposition() is None:
            return True
        node = node._parent[0]

    return False

def find_subtree_root(node):
    path = []

    while (node._parent[1] and
           isinstance(node._parent[1], ProofAction)
           and not _is_apply(node._parent[1])):
        path.append(node._parent[1])
        node = node._parent[0]

    return node, path[::-1]


def _test_hindsight(problem, theory, premises):
    pi = proofsearch.UniformPolicy(DictConfig({
        'value_prior_weight': 10,
        'max_pos_neg_ratio': 5,
        'batch_size': 20000,
        'train_iterations': 100,
    }))

    state = peano.PyProofState(theory,
                               premises,
                               problem)

    root = proofsearch.TreeSearchNode(proofsearch.HolophrasmNode([state]))
    mcts = proofsearch.MonteCarloTreeSearch(pi)
    success, _, _, _ = mcts.evaluate(root)

    log.debug(f'{problem} Success? {success}')

    ex = extract_hindsight_examples(root, theory, premises, pi)

    log.debug(f'{len(ex)} examples')

    for i, e in enumerate(ex):
        log.debug(f'Example {i}:')
        log.debug(f'Goal: {e.goal}')
        log.debug(f'Statement: {e.statement}')
        log.debug('Proof:')
        log.debug(format_blocks_with_indent(e.proof))
        log.debug(f'Logprob: {e.logprob}')
        log.debug(f'{len(e.examples)} training examples.')


def test_natadd():
    nat_add_theory = '''
= : [('t : type) -> 't -> 't -> prop].

nat : type.

z : nat.
s : [nat -> nat].

+ : [nat -> nat -> nat].

+_z : [('n : nat) -> (= (+ 'n z) 'n)].
+_s : [('n : nat) -> ('m : nat) -> (= (+ 'n (s 'm)) (s (+ 'n 'm)))].

nat_ind : [('p : [nat -> prop]) -> ('p z) -> [('n : nat) -> ('p 'n) -> ('p (s 'n))] -> [('n : nat) -> ('p 'n)]].

#backward nat_ind.
#forward +_z ((+ 'n z) : nat).
#forward +_s ((+ 'n (s 'm)) : nat).
'''
    premises = ['eq_symm', 'eq_refl', 'rewrite', 'nat_ind', '+_z', '+_s']

    _test_hindsight("[('a0 : nat) -> (= (+ z 'a0) 'a0)]", nat_add_theory, premises)


def test_groups():
    group_theory = open('theories/groups.p').read()
    premises = ['op_assoc', 'op_comm', 'id_l', 'inv_l', 'eq_refl', 'eq_symm', 'rewrite']
    _test_hindsight(
        "[('a0 : G) -> ('a1 : (= 'a0 (inv (inv (op id 'a0))))) -> ('a2 : G) -> ('a3 : G) -> ('a4 : (= id 'a0)) -> ('a5 : G) -> ('a6 : (= 'a3 (inv 'a0))) -> (= 'a0 (inv id))]",
        group_theory,
        premises
    )

def test_propositional_logic():
    pl_theory = open('theories/propositional-logic.p').read()
    premises = ['and_i', 'and_el', 'and_er', 'or_il', 'or_ir', 'or_e', 'not_i', 'not_e',
                'exfalso', 'iff_i', 'iff_el', 'iff_er', 'em']
    _test_hindsight(
        "[('a0 : prop) -> ('a1 : prop) -> ('a2 : prop) -> (and (and 'a0 'a1) 'a2) -> 'a1]",
        pl_theory,
        premises
    )

if __name__ == '__main__':
    test_propositional_logic()

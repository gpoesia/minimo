#!/usr/bin/env python3

import random
from typing import Optional
from dataclasses import dataclass
import functools
import time
import math

import numpy as np
import hydra
import logging
from omegaconf import DictConfig
import torch
import os
import json

import peano
import problems
import policy
from util import format_blocks_with_indent, sample_batch, setup_mle_logger, value_color, tqdm_if
from action import ProofAction

from mle_logging import MLELogger
log = logging.getLogger(__name__)

@dataclass
class GeneratedProofAction:
    action: str
    children: Optional['GeneratedProofScript']


@dataclass
class GeneratedProofScript:
    actions: list[GeneratedProofAction]


class ProofStateNode:
    def actions(self) -> list[str]:
        raise NotImplementedError

    def is_conjunctive(self) -> bool:
        '''Returns whether this node is considered proven only when all of its children are proven.

        The alternative is a disjunctive node, which is proven if any of its children is proven.

        A conjunctive node is what the Holophrasm paper calls a blue node,
        and their red nodes are disjunctive.
        '''
        raise NotImplementedError

    def expand(self, action) -> list['ProofStateNode']:
        raise NotImplementedError

    def is_terminal(self) -> bool:
        raise NotImplementedError

    def __str__(self):
        raise NotImplementedError

    def goal(self) -> str:
        raise NotImplementedError

    def last_construction_dtype(self):
        if not self.is_conjunctive() and self._proof_states:
            state = self._proof_states[0]
            name = state.construction_from_last_action()
            if name:
                return state.lookup(name).get_type()

        return None


class LeftmostFirstSearchNode(ProofStateNode):
    def __init__(self, proof_states):
        self._proof_states = proof_states
        self._children = None
        self._solution_action = None

    def is_solved(self) -> bool:
        return self.is_terminal() or self._solution_action is not None

    def solution_action(self) -> Optional[str]:
        return self._solution_action

    def goal(self) -> str:
        if self.is_terminal():
            return '<solved>'

        return self._proof_states[0].format_goal()

    def is_terminal(self) -> bool:
        return len(self._proof_states) == 0

    def is_conjunctive(self) -> bool:
        'This kind of node is proven when at least one of its children is proven.'
        return False

    @functools.cached_property
    def actions(self) -> list:
        if self.is_terminal():
            return []
        return list(self._proof_states[0].actions())

    def expand(self, action):
        return LeftmostFirstSearchNode(
            self._proof_states[0].execute_action(action) + self._proof_states[1:]
        )

    def __str__(self):
        if len(self._proof_states) == 0:
            return '<solved>'

        if len(self._proof_states) > 1:
            bg = 'Background goals: ' + ' | '.join([s.format_goal() for s in self._proof_states[1:]]) + '\n'
        else:
            bg = ''

        active = self._proof_states[0]

        ap = active.format_action_prefix()
        if len(ap):
            ap = f'\n{ap}'

        return f"{bg}State: {active.format_context()}\nGoal: {active.format_goal()}{ap}"

    def reconstruct_proof(self, actions, is_root=True) -> list:
        if is_root:
            assert len(self._proof_states) == 1, "Root should always have a single proof state."

        root_goal = self._proof_states[0].format_goal()
        blocks = [f'{"theorem t" if is_root else "goal"} : {root_goal} {{']

        current = self

        while len(current._proof_states) >= len(self._proof_states):
            assert actions, 'Proof is over but there are open goals.'
            a = actions.pop(0)

            if a.is_intro():
                current = current.expand(a)
                name = current._proof_states[0].construction_from_last_action()
                dtype = current._proof_states[0].last_construction_dtype()
                blocks.append(f"intro {name} : {dtype}.")
            elif a.is_construct():
                # TODO: use proper show/construct keyword.
                current = current.expand(a)
                if len(a._actions) == 1:
                    current = current.expand(actions.pop(0))
                arrow = str(a).split(" ")[1]
                last_arrow = current._proof_states[0].generating_arguments(
                        current._proof_states[0].construction_from_last_action())[0]
                blocks.append(f"show {str(selection)[:-1]} by {arrow}.")
            elif a.is_apply():
                arrow = str(a).split(" ")[1]

                current = current.expand(a)
                if len(a._actions) == 1:
                    current = current.expand(actions.pop(0))

                blocks.append(f"apply {arrow}.")

                while len(current._proof_states) >= len(self._proof_states):
                    subproof, current = current.reconstruct_proof(actions, False)
                    blocks.append(subproof)
            else:
                raise ValueError(f'Unknown action type {str(a)}')

        blocks.append("}")
        return blocks if is_root else (blocks, current)

    def reward(self) -> float:
        if self.is_terminal():
            return np.inf  # Proof found.
        elif not self.actions:
            return -1  # Dead end.
        return -len(self._proof_states)


class HolophrasmNode(ProofStateNode):
    # Controls whether construct/apply nodes will be lazy or eager.
    # The original implementation used lazy nodes. In this model, a node's
    # children will be of the form "apply x", "construct y", ..., meaning
    # to use arrows x and y in the backward (apply) or forward (construct) direction.
    # But these edges did not yet apply the arrow exhaustively. That would only
    # be done when visiting that child. For example, visiting the edge to "apply x"
    # would lead to Peano actually enumerating all the ways to apply x in the current
    # context, and having each of those as a child of that new node (2 edges down
    # from the root).
    # This design choice results in dead nodes: if there are no ways to actually apply x
    # in the current context, we will only know when we try to expand the corresponding
    # child.
    # Eager nodes are slower, since at the root we'll have Peano enumerate all the ways
    # to use each of the arrows. However, they do not have dead nodes, since this
    # enumeration reveals to the root only the arrows that have children.
    # This class-level flag switches between these two modes.
    EAGER_NODES = True

    def __init__(self, proof_states):
        self._proof_states = proof_states

    def clone(self) -> ProofStateNode:
        return HolophrasmNode([ps.clone() for ps in self._proof_states])

    def is_terminal(self) -> bool:
        return len(self._proof_states) == 0

    def is_conjunctive(self) -> bool:
        return len(self._proof_states) > 1

    @functools.cached_property
    def actions(self) -> list:
        if self.is_terminal():
            return []

        if self.is_conjunctive():
            return [f'{i}' for i in range(len(self._proof_states))]

        # Single state: actually list out actions from Peano.
        if HolophrasmNode.EAGER_NODES:
            peano_actions = list(self._proof_states[0].actions())
            eager_actions = []

            for a in peano_actions:
                if a.is_intro():
                    eager_actions.append(ProofAction([a]))
                elif a.is_construct() or a.is_apply():
                    child = self._proof_states[0].execute_action(a)[0]
                    if child.actions():
                        eager_actions.append(ProofAction([a]))
                else:
                    eager_actions.append(ProofAction([a]))
            return eager_actions
        else:
            # Lazy nodes - straight actions from Peano.
            return [ProofAction([a]) for a in self._proof_states[0].actions()]

    def goal(self) -> str:
        if self.is_terminal():
            return '<solved>'

        return self._proof_states[0].format_goal()

    def expand(self, action):
        if self.is_conjunctive():
            # Action should be the index of the goal.
            idx = int(action)
            return HolophrasmNode([self._proof_states[idx]])

        return HolophrasmNode(action.execute(self._proof_states[0]))

    def __str__(self):
        if self.is_terminal():
            return '<solved>'

        lines = []
        lines.append(f'G={len(self._proof_states)}')

        for i, ps in enumerate(self._proof_states):
            if i > 0:
                lines.append('-' * 5)

            lines.extend([
                f'State: {ps.format_context()}',
                f'Goal: {ps.format_goal()}',
                f'{ps.format_action_prefix()}',
            ])
        return '\n'.join(lines)

    def reconstruct_proof(self, actions, is_root=True) -> list:
        if is_root:
            assert len(self._proof_states) == 1, "Root should always have a single proof state."

        root_goal = self._proof_states[0].format_goal()
        blocks = [f'{"theorem t :" if is_root else "goal"} {root_goal} {{']

        current = self

        while len(actions):
            a = actions.pop(0)
            if a.is_intro():
                goal_before = current._proof_states[0].goal()
                current = current.expand(a)
                if not current._proof_states:
                    # intro closed the goal.
                    blocks.append(f"intro _ : {goal_before}.")
                else:
                    name = current._proof_states[0].construction_from_last_action()
                    dtype = current.last_construction_dtype()
                    blocks.append(f"intro {name} : {dtype}.")
            elif a.is_construct():
                # TODO: use proper show/construct keyword.
                current = current.expand(a)
                last_arrow = a.arrow_name()

                if not a.is_eager():
                    a = actions.pop(0)
                    current = current.expand(a)

                dtype = a.construction_dtype()
                blocks.append(f"show {dtype} by {last_arrow}.")
            elif a.is_apply():
                arrow = a.arrow_name()

                current = current.expand(a)
                if len(a._actions) == 1:
                    current = current.expand(actions.pop(0))

                blocks.append(f"apply {arrow}.")

                if not current.is_conjunctive():
                    if not current.is_terminal():
                        blocks.append(current.reconstruct_proof(actions, False))
                else:
                    for i, a in enumerate(current.actions):
                        child = current if not current.is_conjunctive() else current.expand(str(i))
                        blocks.append(child.reconstruct_proof(actions[i], False))

                break
            else:
                raise ValueError(f'Unknown action type {str(a)}')

        blocks.append("}")
        return blocks

    def reward(self) -> float:
        if self.is_terminal():
            return np.inf  # Proof found.
        elif not self.actions:
            return -1  # Dead end.
        return 0

MAX_ACTION_LENGTH = 75
ACTION_ENUMERATION_TIMEOUT = 0.2

class TreeSearchNode:
    def __init__(self, state: ProofStateNode,
                 parent: tuple['TreeSearchNode', 'GeneratedProofAction'] = (None, None)):
        self._state = state
        self._visits = 0
        self._reward = 0
        self._value_estimate = None
        self._prior_policy = 1.0
        self._logit = 0
        self._parent = parent
        self._children = None
        self._is_dead = False
        self._index = None
        self._solution_action = None

    def is_solved(self):
        if self._solution_action is not None:
            return True

        state = self._state or self.state_node

        if state.is_terminal():
            return True

        if not self._children:
            return False

        if state.is_conjunctive():
            return all(c.is_solved() for c in self._children)

        return False

    def get_path_from_root(self, root=None) -> list['GeneratedProofAction']:
        if self is root or self._parent[0] is None:
            return []
        parent, action = self._parent
        return parent.get_path_from_root(root) + [action]

    def get_root(self) -> 'TreeSearchNode':
        if self._parent[0] is None:
            return self
        return self._parent[0].get_root()

    @property
    #@functools.lru_cache(maxsize=10**3)
    def state_node(self) -> ProofStateNode:
        if self._state is not None:
            return self._state

        assert False

        # Reconstruct state based on actions from root.
        root = self.get_root()
        path = self.get_path_from_root()

        state = root._state
        assert state is not None, 'Root should not have lazy state.'

        for a in path:
            state = state.expand(a)

        return state

    @functools.cached_property
    def actions(self) -> list:
        assert self._children is not None, 'Node must be expanded to get actions.'
        return [a._parent[1] for a in self._children]

    def solution_action(self):
        return self._solution_action

    def is_terminal(self):
        return self.state_node.is_terminal()

    def is_conjunctive(self):
        return self.state_node.is_conjunctive()

    def is_dead(self):
        return self._is_dead or (not self.is_terminal() and self._children == [])

    def mark_dead(self):
        self._is_dead = True

    def mark_solved(self, action=None):
        parent, parent_action = self._parent

        if self.is_conjunctive():
            # A child was marked as solved. If this node is now solved,
            # propagate the solution to the parent.
            if self.is_solved():
                if parent is not None:
                    parent.mark_solved(parent_action)
        else:
            # A child of this disjunctive node was marked as solved.
            # Save the action and propagate upwards in the tree.
            self._solution_action = action
            if parent is not None:
                parent.mark_solved(parent_action)

    def is_leaf(self):
        return not self.is_terminal() and self._children is None

    def expand(self, only_if_leaf=True):
        if only_if_leaf:
            assert self.is_leaf(), 'Can only expand leaves.'
        # NOTE: We can either compute the state for the child here (fast)
        # or do lazy reconstruction when the state is needed (memory efficient).
        # before = time.time()
        actions = [a for a in self.state_node.actions
                   if len(str(a).split(' : ')[0].lstrip('=> ')) <= MAX_ACTION_LENGTH]
        self._children = [TreeSearchNode(self._state.expand(a),
                                         parent=(self, a))
                          for a in actions]
        return
        after = time.time()
        if after - before > ACTION_ENUMERATION_TIMEOUT:
            # Kill exploding node.
            log.error(f'Killing node after {after - before:.1f}s')
            raise NotImplementedError("Node took too long to expand.")
            self._children = []

    def children(self) -> list['TreeSearchNode']:
        return self._children

    def child(self, action: str) -> 'TreeSearchNode':
        for c in self._children:
            if str(c._parent[1]) == action:
                return c

    def reconstruct_proof(self):
        # NOTE: In the future we can also reconstruct partial proofs, which will
        # have holes in open goals.
        actions = self.get_solution_actions()
        return self.state_node.reconstruct_proof(actions)

    def get_solution_actions(self):
        def dfs(node):
            assert node.is_solved(), 'Can only extract solution actions from a solved node.'

            if node.is_conjunctive():
                return [dfs(c) for c in node._children]

            if node._solution_action is None:
                return []

            action = node._solution_action
            child = next(c for c in node._children if c._parent[1] == action)
            return [action] + dfs(child)

        return dfs(self)

    def _actions_logprob_under_policy(self, actions, policy: 'Policy') -> float:
        if self.is_solved():
            return 0

        if self.is_terminal():
            raise RuntimeError("Actions lead to terminal non-solved node.")

        self.expand()

        if self.is_conjunctive():
            logprob = 0
            node_actions = self.actions
            assert len(actions) == len(node_actions)

            for sna, a in zip(actions, node_actions):
                logprob += (TreeSearchNode(self._state.expand(a),
                                           parent=(self, a))
                            ._actions_logprob_under_policy(sna, policy))
            return logprob
        else:
            policy.initialize(self)
            pi, _value = policy.evaluate(self)
            assert actions

            head, tail = actions[0], actions[1:]

            idx, a = next((i, a)
                          for i, a in enumerate(self.actions)
                          if str(a) == str(head))

            if idx >= len(pi):
                raise NotImplementedError("Could not generalize theorem statement")


            head_logprob = math.log(float(pi[idx]))
            tail_logprob = (TreeSearchNode(self.state_node.expand(a),
                                           parent=(self, a))
                            ._actions_logprob_under_policy(tail, policy))
            return head_logprob + tail_logprob

    def solution_logprob_under_policy(self, policy: 'Policy', actions=None) -> float:
        return (TreeSearchNode(self._state, None)
                ._actions_logprob_under_policy(actions or self.get_solution_actions(),
                                               policy))


    def render_dot(self, min_visits=0) -> list[str]:
        if self._index is None:
            return []

        shape = 'ellipse'

        if self.is_conjunctive():
            fillcolor = 'blue'
            shape = 'triangle'
        elif self.is_dead():
            fillcolor = 'black'
        elif self._value_estimate is not None:
            fillcolor = value_color(self._value_estimate)
        else:
            fillcolor = 'white'

        l = [f'{self._index}[style=filled,label=\"{self._visits}\",fillcolor=\"{fillcolor}\",shape={shape}]']

        if self._visits < min_visits:
            return l

        for c in (self._children or []):
            if c._index is not None:
                edge_attributes = ',weight=5,color=green' if c.is_solved() else ''
                l.append(f'{self._index} -> {c._index} [label=\"{c._parent[1]}\"{edge_attributes}]')
                l.extend(c.render_dot(min_visits))

        return l

    def __iter__(self):
        yield self
        for c in (self._children or []):
            yield from c


    def hindsight_relabel(self, new_goal, root, substitutions, intros_traversed=0) -> list[ProofStateNode]:
        assert not self._state.is_conjunctive(), 'Cannot relabel conjunctive node.'

        has_goals = len(self.state_node._proof_states) > 0
        proof_state = self.state_node.clone()

        if has_goals:
            #print('Goal before:', proof_state._proof_states[0].format_goal())
            #print('New goal:', new_goal)
            rewritten_goal = proof_state._proof_states[0].rewrite_goal_conclusion(new_goal, substitutions, intros_traversed)

            ga = str(proof_state._proof_states[0].goal())

            #print('Goal after:', ga)

            if self is root:
                return [(proof_state, None)]

        parent, action = self._parent
        new_substitutions = []

        if action.is_intro():
            intros_traversed += 1
            previous_name = parent._state._proof_states[0].next_goal_parameter()
            if previous_name is not None and has_goals:
                introduced_name = proof_state._proof_states[0].construction_from_last_action()
                new_substitutions = [(introduced_name, previous_name)]
            new_goal = rewritten_goal

        parent_path = parent.hindsight_relabel(new_goal, root, substitutions + new_substitutions, intros_traversed)

        if parent_path is None:
            return None

        # Ensure parent action to this child still exists.
        for a in parent_path[-1][0].actions:
            if a == action:
                return parent_path + [(proof_state, action)]

        return None

    def update_parent_link(self):
        parent, action = self._parent

        if parent is not None:
            for i in range(len(parent._children)):
                _, p_action_i = parent._children[i]._parent

                if p_action_i == action:
                    parent._children[i] = self
                    return


class Policy:
    'Abstract policy class: given a proof state, returns a distribution over its actions.'
    def evaluate(self, state: TreeSearchNode) -> np.array:
        raise NotImplementedError

    def initialize(self, leaf: TreeSearchNode):
        pass

    def train(self, examples):
        pass

    def extract_examples(self, root):
        return []

    def extract_examples_from_path(self, root, actions) -> list:
        return []


class UniformPolicy(Policy):
    def __init__(self, _config):
        pass

    def evaluate(self, node: TreeSearchNode) -> np.array:
        n = len(node.actions)
        value = node.state_node.reward()
        return np.ones(n) / n, value

    def extract_examples(self, root) -> list:
        return []

    def initialize(self, node: TreeSearchNode):
        if node.is_terminal() or node.is_dead():
            return

        for c in node._children:
            c._value_estimate = 0.5


class LMPolicy(Policy):
    def __init__(self, config, mle_log: MLELogger):
        self._lm = policy.TransformerLMPolicy(config, mle_log)
        self._value_prior_weight = config.get('value_prior_weight', 1)
        self._max_positive_negative_ratio = config.get('max_positive_negative_ratio', 10)
        self._lm.eval()

    def evaluate(self, node: TreeSearchNode) -> np.array:
        if node.is_terminal():
            return [], 1e6

        #p_goal = 1 / (1e-3 + np.exp(self._lm.goal_logprob(node.state_node._proof_states[0].format_context(),
        #                                                  node.state_node._proof_states[0].format_goal())))

        return [c._prior_policy for c in node._children], node._value_estimate

    def initialize(self, node: TreeSearchNode):
        if node.is_terminal() or node.is_dead():
            return

        children_states = [str(c.state_node) for c in node._children]
        actions = [str(a) for a in node.actions]
        policy_queries = [] if node.is_conjunctive() else actions

        policy_estimates, value_estimates = self._lm.estimate_state_and_action_values(
                str(node.state_node),
                actions,
                children_states)

        if node.is_conjunctive():
            policy_estimates = [1 for _ in actions]

        denom = sum(policy_estimates)

        for c, v, p in zip(node._children, value_estimates, policy_estimates):
            c._reward = v * self._value_prior_weight
            c._value_estimate = v
            c._prior_policy = p / denom

    def extract_examples(self, root):
        all = set()

        def dfs(node):
            all.add(str(node.state_node))
            for c in (node.children() or []):
                dfs(c)

        dfs(root)

        positives = set()
        action_examples = []

        def dfs_solution(node):
            if not node.is_solved():
                raise NotImplementedError("Could not generalize theorem statement")


            assert node.is_solved()
            positives.add(str(node.state_node))

            if node.state_node.is_conjunctive():
                for c in node._children:
                    dfs_solution(c)
            elif node._solution_action:
                for a in node.children():
                    action_examples.append(self._lm.format_state_action_query(
                        str(node.state_node),
                        str(a._parent[1]),
                        'Y' if a._parent[1] == node._solution_action else 'N'))

                for c in node._children:
                    if c._parent[1] == node._solution_action:
                        dfs_solution(c)
                        return

                assert False, "Solution action not found in children."

        if root.is_solved():
            dfs_solution(root)

        positive_examples = []
        negative_examples = []

        for s in all:
            # Create examples and return them.
            if s in positives:
                positive_examples.append({'type': 'value', 'str': self._lm.format_state_query(s, 'Y')})
            else:
                negative_examples.append({'type': 'value', 'str': self._lm.format_state_query(s, 'N')})

        negative_examples = random.sample(
            negative_examples,
            k=min(len(negative_examples),
                      self._max_positive_negative_ratio * len(positive_examples)))

        policy_examples = [{'type': 'policy', 'str': s} for s in action_examples]
        value_examples = positive_examples + negative_examples
        # construction_examples = self._extract_examples_from_constructions(root)

        return policy_examples + value_examples  # + construction_examples

    def extract_examples_from_path(self, path: list[ProofStateNode]) -> list[str]:
        examples = []

        for i, (state, action) in enumerate(path):
            examples.append({'type': 'value', 'str': self._lm.format_state_query(str(state), 'Y')})

            # If there was an open goal, train to predict it as provable.
            if len(state._wrapped_node._proof_states) == 1:
                examples.append(self._lm.format_provable_goal(
                    state._wrapped_node._proof_states[0].format_context(),
                    state._wrapped_node._proof_states[0].format_goal()))

            if action is not None:
                parent = path[i-1][0]
                for a in parent.actions:
                    correct_action = str(a) == str(action)
                    label = 'Y' if correct_action else 'N'

                    if not correct_action:
                        sub_state = parent.expand(a)
                        examples.append({'type': 'value', 'str': self._lm.format_state_query(str(sub_state), 'N')})

                    examples.append(self._lm.format_state_action_query(str(state), str(a), label))

        return examples


    def _extract_examples_from_constructions(self, root: TreeSearchNode) -> list[str]:
        examples = []

        for node in root:
            construction = node.state_node.last_construction_dtype()
            if construction is not None:
                examples.append({'type': 'construction',
                                 'str': self._lm.format_provable_goal('<>', construction)})

        return examples

    def val_loss(self, val_set):
        return self._lm.val_loss(val_set)

    def train(self, examples, final_goals, iteration, ratio_proven, mle_log: MLELogger, verbose=True):
        self._lm.fit(examples, final_goals, iteration, ratio_proven, mle_log, verbose)
        self._lm.eval()


class MonteCarloTreeSearch(Policy):
    def __init__(
            self,
            default_policy,
            budget=1000,
            exploration_prefix=None,
            use_policy=True,
    ):
        self._budget = budget
        self._default_policy = default_policy
        self._exploration_c = np.sqrt(2) / 2
        self._exploration_prefix = exploration_prefix
        self._use_default_policy = use_policy

    def expand(self, root: TreeSearchNode, on_expand=None, verbose=True):
        return self.evaluate(root, on_expand=on_expand, verbose=verbose)

    def evaluate(self, root: TreeSearchNode, start_index=0,
                 on_expand=None, verbose=True) -> np.array:
        for i in tqdm_if(verbose)(range(self._budget)):
            if root.is_solved():
                break

            leaf = self._tree_policy(root)

            if leaf is None:
                # Ended up visiting a node where all children were dead,
                # so forcefully would end up in a dead node. The parent
                # is marked as dead so this won't repeat in the same branch.
                continue

            leaf._index = start_index + i

            if leaf.is_terminal():
                leaf.mark_solved()
                self._backpropagate_reward(leaf, 1)
                continue

            leaf.expand()

            if self._use_default_policy and self._default_policy:
                self._default_policy.initialize(leaf)

            if on_expand is not None:
                path = leaf.get_path_from_root()
                on_expand([str(a) for a in path])

            _, reward = self._default_policy.evaluate(leaf)
            self._backpropagate_reward(leaf, reward)

        pi = self._policy(root)
        value = max(p * (c._reward / max(1, c._visits))
                    for p, c in zip(pi, root.children()))

        return root.is_solved(), pi, value, i

    def _tree_policy(self, node):
        prefix = list(self._exploration_prefix or [])

        while not (node.is_leaf() or node.is_terminal()):
            prefix_action = self._next_action_from_prefix(node, prefix)
            a = prefix_action if prefix_action is not None else self._uct(node)

            if a is None:
                return None

            node = node.children()[a]

        return node

    def _next_action_from_prefix(self, node, prefix):
        if len(prefix) == 0:  # or node._state.is_conjunctive():
            return None

        action = prefix.pop(0)

        if action is None:
            return action

        for i, c in enumerate(node.children()):
            if str(c._parent[1]) == action:
                return i

        raise ValueError(f"Exploration prefix had impossible action {action}")

    def _uct(self, node) -> int:
        if node.state_node.is_conjunctive():
            # Pick first unsolved child.
            # NOTE: the Holophrasm paper picked the least promising child (~ hardest subgoal).
            for i, child in enumerate(node.children()):
                if not child.is_solved():
                    return i

        max_value = -np.inf
        best_action_idx = None

        den = 0
        for i, child in enumerate(node.children()):
            if child.is_dead():
                continue
            if child._visits == 0:
                value = np.inf
            else:
                den += child._reward / child._visits

        den = 1 if den == 0 else den

        # baseline_reward = 1 + node._reward / max(node._visits, 1)

        for i, child in enumerate(node.children()):
            if child.is_dead():
                continue

            if child._visits == 0:
                value = np.inf
            else:
                # UCT formula with normalized rewards
                value = (child._prior_policy *
                        ((child._reward / child._visits) / den +
                            self._exploration_c * np.sqrt(math.log(node._visits, 2) / child._visits)))

            if value > max_value:
                max_value = value
                best_action_idx = i

        if best_action_idx is None:
            # node is not itself dead, but all of its children are. Mark it as dead.
            node.mark_dead()

        return best_action_idx

    def _policy(self, node):
        return np.array([c._visits / max(node._visits - 1, 1) for c in node.children()])

    def _backpropagate_reward(self, node, reward):
        if reward is None:
            return
        while node is not None:
            node._visits += 1
            node._reward += reward
            node = node._parent[0]


def make_policy(config, mle_log: MLELogger):
    if not config.type:
        return None
    if config.type == 'LM':
        return LMPolicy(config, mle_log)
    if config.type == 'Uniform':
        return UniformPolicy(config)
    raise ValueError(f'Unknown policy type', config.type)


@dataclass
class ProofSearchResult:
    problem: str
    success: bool
    root: TreeSearchNode
    examples: list[str]
    iterations: int


class ProofSearchAgent:
    def __init__(self, config: DictConfig, mle_log: MLELogger):
        agent_config = config.agent
        self.config = config
        self._max_mcts_nodes = agent_config.get('max_mcts_nodes', 1000)
        self._max_searches = agent_config.get('max_searches', 1)
        self._max_examples = agent_config.get('max_examples', 10**8)
        self._checkpoint_every = agent_config.get('checkpoint_every', 1000)
        self._policy = make_policy(agent_config.policy, mle_log)
        self._node_type = ({'vanilla': LeftmostFirstSearchNode,
                            'holophrasm': HolophrasmNode})[agent_config.get('node_type', 'holophrasm')]
        self._checkpoint_dir = agent_config.get('checkpoint_dir', 'checkpoints')
        self._training_its = 0
        self._checkpoints = 0
        self._examples = []

    def proof_search(self, problem, state):
        root = TreeSearchNode(self._node_type([state]))

        node = root
        iterations = 0
        examples = []

        while not (node.is_terminal() or node.is_dead()):
            log.debug(f'State: {node.state_node}')

            mcts = MonteCarloTreeSearch(self._policy, self._max_mcts_nodes, use_policy=True)
            solved, pi, _, it = mcts.evaluate(node)

            if solved:
                break

            log.debug(f'Actions: {list(map(str, node.actions))}')
            log.debug(f'Policy: {pi}')

            best = pi.argmax()

            log.debug(f'Taking action {node.actions[best]}')
            node = node.children()[best]

            iterations += 1
            if iterations >= self._max_searches:
                break

        if solved:
            log.debug('Found solution!')
            log.debug(format_blocks_with_indent(root.reconstruct_proof()))
        else:
            log.debug('Did not find solution.')

        examples = self._policy.extract_examples(root)
        self._examples.extend(examples)
        self._examples = self._examples[-self._max_examples:]

        return ProofSearchResult(problem, solved, root, examples, iterations)

    def train(self, examples, final_goals, solutions, ratio_proven, mle_log: MLELogger): 
        examples = examples or self._examples

        if self._training_its % self._checkpoint_every == 0:
            path = os.path.join(self._checkpoint_dir, f'{self._checkpoints}.pt')
            os.makedirs(os.path.dirname(path), exist_ok=True)
            torch.save(self, path)
            self._checkpoints += 1

        val_loss = None
        if examples:
            example_strs = []
            for e in examples:
                if isinstance(e, dict):
                    example_strs.append(e['str'])
                else:
                    assert isinstance(e, str), f'{type(e)} is not a string.'
                    example_strs.append(e)

            # train policy
            self._policy.train(example_strs, final_goals, self._training_its, ratio_proven, mle_log)

            # calculate validation loss
            # https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
            solutions_flattened = [x for xs in solutions for x in xs]
            val_loss = self._policy.val_loss(solutions_flattened)
        else:
            log.warning("No examples in this iteration.")

        self._training_its += 1
        return val_loss
        return val_loss

def mcts_example(cfg, mle_log: MLELogger):
    problemset = problems.load_problemset('nng')
    root_state = problemset.initialize_problem('a_zero_add')

    if cfg.get('node_type', 'vanilla') == 'vanilla':
        root = TreeSearchNode(LeftmostFirstSearchNode([root_state]))
    elif cfg.node_type == 'holophrasm':
        root = TreeSearchNode(HolophrasmNode([root_state]))
    else:
        raise ValueError('Unknown tree search node type', cfg.node_type)

    p = LMPolicy(cfg.agent.policy, mle_log)
    log.debug(f'State: {root.state_node}')
    mcts = MonteCarloTreeSearch(p, 3000)

    solved, pi, _ = mcts.evaluate(root)

    log.debug(f'Actions: {list(map(str, root.actions))}')
    log.debug(f'MCTS Policy: {pi}')

    if solved:
        log.debug('Found solution!')
        log.debug(format_blocks_with_indent(root.reconstruct_proof()))
    else:
        log.debug('Did not find solution.')

    examples = p.extract_examples(root)

    log.debug(f'{len(examples)} training examples extracted')
    log.debug('\n'.join(examples))
    visualize_search_tree(root, os.path.join(os.path.dirname(__file__), 'mcts_example.dot'))


class ProblemSelector:
    def name(self) -> str:
        raise NotImplementedError

    def select_problem(self, problemset, agent):
        raise NotImplementedError


class RandomProblemSelector:
    def name(self) -> str:
        return 'random'

    def select_problem(self, problemset: 'problems.ProblemSet', agent):
        return random.choice(problemset.problem_names())


class RandomUnsolvedProblemSelector:
    def name(self) -> str:
        return 'random-unsolved'

    def select_problem(self, problemset: 'problems.ProblemSet', agent):
        return random.choice([name
                              for name in problemset.problem_names()
                              if not problemset.is_solved(name)])

def visualize_search_tree(root, path, min_visits=0):
    lines = root.render_dot(min_visits)
    with open(path, 'w') as out:
        content = '\n'.join(lines)
        out.write(f'digraph TreeSearch {{\n{content}\n}}')


def run_proof_search_agent(config, mle_log: MLELogger):
    if config.get('agent_path'):
        log.info(f'Loading from checkpoint {config.agent_path}')
        agent = torch.load(config.agent_path)
        begin = config.skip
        log.debug(f'Begin = {begin}')
    else:
        agent = ProofSearchAgent(config.agent, mle_log)
        begin = 0

    selector = RandomProblemSelector()

    problemset = problems.load_problemset(config.problemset)

    eval_problems = ([config.problem] if 'problem' in config else
                     problemset.problem_names()[:config.max_problems])

    for i, problem in enumerate(eval_problems):
        log.debug(f'Attempting problem: {problem}')
        try:
            result = agent.proof_search(problem, problemset.initialize_problem(problem))
            log.debug(f'Success? {result.success}')
            success_count += int(result.success)
            if result.success:
                problemset.mark_as_solved(problem, add_to_library=config.accumulate_library)

            mle_log.update({'num_attempted_problem': i}, {'cumulative_pass_rate': problemset.cumulative_pass_rate()})
            mle_log.update({'num_attempted_problem': i}, {'train_progress': (i + 1) / config.max_problems})

            agent.train()
        except KeyboardInterrupt:
            raise
        except:
            log.exception('Error during proof search.')

    evaluate_agent(config, mle_log, agent)


def test_agent(config: DictConfig):
    dot_path = config.get('dot_path', 'searchtree.dot')
    agent_path = config.get('agent_path')
    problemset = problems.load_problemset(config.problemset)
    problem = problemset.initialize_problem(config.problem)

    if agent_path is not None:
        agent = torch.load(agent_path)
        if 'mcts_iterations' in config:
            agent._max_mcts_nodes = config.mcts_iterations
        root = agent.proof_search(config.problem, problem).root
    else:
        root = TreeSearchNode(HolophrasmNode([problem]))
        mcts = MonteCarloTreeSearch(UniformPolicy(), config.get('mcts_iterations', 500),
                                    exploration_prefix=config.get('prefix'))
        mcts.evaluate(root)

    visualize_search_tree(root, dot_path, min_visits=config.get('min_visits', 10))
    log.debug(f'Wrote {os.path.abspath(dot_path)}')


def proof_reconstruction_example():
    action_strs = ['intro.',
                   'intro.',
                   'intro.',
                   'a or_elim',
                   '=> [x -> (or x0 x)]; [x0 -> (or x0 x)].',
                   'intro.',
                   'a or_r',
                   '=> .',
                   'intro.',
                   'a or_l',
                   '=> .']

    logic_theory = """
    or : [prop -> prop -> prop].
    or_l : [('p : prop) -> ('q : prop) -> 'p -> (or 'p 'q)].
    or_r : [('p : prop) -> ('q : prop) -> 'q -> (or 'p 'q)].

    or_elim : [('p : prop) -> ('q : prop) -> (or 'p 'q) ->
               ('r : prop) -> ['p -> 'r] -> ['q -> 'r]
               -> 'r].

    #backward or_l infer infer infer.
    #backward or_r infer infer infer.
    #backward or_elim infer infer infer infer subgoal subgoal.
    """

    root = LeftmostFirstSearchNode(
        [peano.PyProofState(logic_theory,
                            ['or_l', 'or_r', 'or_elim'],
                            "[('p : prop) -> ('q : prop) -> (or 'p 'q) -> (or 'q 'p)]",
                            )]
    )

    actions = []
    current = root

    for a in action_strs:
        for ac in current.actions:
            if str(ac) == a:
                actions.append(ac)
                current = current.expand(ac)
                break

    log.debug(f'Proof has {len(actions)} actions.')

    blocks, _ = root.reconstruct_proof(actions)
    log.debug(format_blocks_with_indent(blocks))


def test_proof_search(problemset='lean-library-logic',
                      problem='imp_congr',
                      agent_path=None):
    problemset = problems.load_problemset(problemset)

    theory = open('theories/propositional-logic.p').read()
    theory = open('theories/groups.p').read()
    premises = ['and_i', 'and_el', 'and_er', 'or_il', 'or_ir', 'or_e', 'not_i', 'not_e',
                'exfalso', 'iff_i', 'iff_el', 'iff_er', 'em']
    premises = ['op_assoc', 'op_comm', 'id_l', 'inv_l', 'eq_refl', 'eq_symm', 'rewrite']

    state = peano.PyProofState(theory,
                               premises,
                               "(= (op id id) (inv id))")
                               #"[('a0 : (not (not false))) -> false]")
    root = TreeSearchNode(HolophrasmNode([state]))

    if agent_path is not None:
        pi = torch.load(agent_path)
        if hasattr(pi, '_policy'):
            pi = pi._policy
        pi._lm.eval()
    else:
        pi = None

    node = root
    actions_list = []

    while not node.is_terminal():
        log.debug(f'Node: {str(node.state_node)}')
        log.debug('Actions:')

        node.expand()

        if pi:
            pi.initialize(node)

        actions = [str(c._parent[1]) for c in node.children()]
        if pi:
            action_logprobs = pi._lm.action_logprobs(str(node.state_node), actions)
        else:
            action_logprobs = np.zeros(len(actions))

        for i, c in enumerate(node.children()):
            lp, nlp = action_logprobs[i], action_logprobs[i] / len(actions[i])
            log.debug(f'#{i}. {c._parent[1]} ({lp:.3f}/{nlp:.3f})')

        if not actions:
            log.debug('Dead end: no further actions and not a terminal node.')
            return

        if pi is not None:
            g = node.state_node._proof_states[0].format_goal()
            goal_logprob = pi._lm.goal_logprob(node.state_node._proof_states[0].format_context(), g)
            log.debug(f'Agent logprob for current goal: {goal_logprob} / {goal_logprob / len(g)}')

            goals, scores = pi._lm.sample_provable_goals(
                node.state_node._proof_states[0].format_context(), l=100, n=5)
            log.debug('Agent samples of provable goals:')

            for g, s in zip(goals, scores):
                log.debug(f'{g} -- {s} / {s / len(g)}')

        idx = int(input('Choose action:'))

        node = node.children()[idx]
        actions_list.append(node._parent[1])

    log.debug('Actions:')
    log.debug(repr(actions_list))


def make_agent(config, mle_log: MLELogger):
    if config.get('agent_path'):
        agent = torch.load(config['agent_path'])
    elif config.agent.get('type') == 'curiosity':
        import pretraining
        agent = pretraining.CuriosityGuidedProofSearchAgent(config.agent)
    else:
        agent = ProofSearchAgent(config, mle_log)

    if config.agent.get('lm_path'):
        path = config.agent.get('lm_path')
        log.info(f'Loading LM policy from {path}')
        agent._policy = torch.load(path)

    if config.agent.get('training_set'):
        with open(config.agent.training_set) as f:
            examples = json.load(f)
        strs = [e['str'] for e in examples if e['type'] == 'policy']

        log.debug(f'Training on {len(strs)} goal-directed examples.')

        agent._policy = LMPolicy(config.agent.policy, mle_log)
        agent._policy.train(strs, True)

    return agent


def evaluate_agent(config: DictConfig, mle_log: MLELogger, agent=None):
    if agent is None:
        agent = make_agent(config, mle_log)

    problemset = problems.load_problemset(config.problemset)

    begin = config.get('begin', 0)
    end = config.get('end', len(problemset))

    for problem in problemset.problem_names()[begin:end]:
        log.debug(f'Attempting problem: {problem}')
        try:
            result = agent.proof_search(problem, problemset.initialize_problem(problem))
        except KeyboardInterrupt:
            raise
        except:
            log.exception('Error during proof search agent evaluation.')
            result = ProofSearchResult(problem, False, None, [], 0)
        log.debug(f'Success? {result.success}')

        if result.success:
            problemset.mark_as_solved(problem, add_to_library=False)

    log.debug(f'Solved {len(problemset._solved)}/{len(problemset)}')
    log.debug(f'Solved problems: {", ".join(problemset._solved)}')


def test_preconditions():
    nng = problems.load_problemset('natural-number-game')
    test_ps = problems.ProblemSet(
        theory=nng._theory,
        initial_library=['add_assoc', '+'],
        statements= [
            problems.TheoremStatement('three_nats', "[('a : nat) -> ('b : nat) -> ('c : nat) -> false]")
        ]
    )
    root = LeftmostFirstSearchNode(
        [test_ps.initialize_problem('three_nats')]
    )

    probability = 1

    node = root
    actions_list = []

    while not node.is_terminal():
        log.debug(f'Node: {node}')
        log.debug('Actions:')

        actions = node.actions

        for i, a in enumerate(actions):
            log.debug(f'#{i}. {a}')

        if not actions:
            log.debug('Dead end: no further actions and not a terminal node.')
            return

        idx = int(input('Choose action:'))

        a = actions[idx]
        node = node.expand(a)
        actions_list.append(a)
        probability /= len(actions)

    log.debug(f'Proved! Probability under random policy: {probability}')
    log.debug('Actions:')
    log.debug(repr(actions_list))


def test_probability_under_policy(mle_log: MLELogger):
    nng = problems.load_problemset('natural-number-game')
    pi = LMPolicy(DictConfig({
        'value_prior_weight': 10,
        'max_pos_neg_ratio': 5,
        'batch_size': 20000,
        'train_iterations': 100,
    }), mle_log)

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

    root = TreeSearchNode(HolophrasmNode([nng.initialize_problem('a_zero_add')]))
    #root = TreeSearchNode(HolophrasmNode([peano.PyProofState(
    #    nat_add_theory,
    #    ['eq_symm', 'eq_refl', '+_z', '+_s', 'nat_ind', 'rewrite'],
    #    "[('a0 : nat) -> (= (+ (+ 'a0 'a0) z) (+ (+ 'a0 'a0) z))]",
    #    )]))

    mcts = MonteCarloTreeSearch(pi)
    success, _, _, _ = mcts.evaluate(root)

    if not success:
        log.debug('Failed.')
    else:
        log.debug('Success!')
        prob = root.solution_logprob_under_policy(pi)
        log.debug(f'logprob under policy: {prob}')

        examples = pi.extract_examples(root)
        log.debug(f'{len(examples)} examples.')

        import collections
        types = collections.Counter([e['type'] for e in examples])
        log.debug(f'Number of examples: {types.most_common()}')

        log.debug(os.getcwd())
        for t in types:
            with open(f'examples-{t}.txt', 'w') as out:
                for e in examples:
                    if e['type'] == t:
                        s = e['str']
                        out.write(s.replace('\n', '\\n') + '\n')

        for i in range(10):
            log.debug(f'iteration {i}')
            pi.train([e['str'] for e in examples])
            prob = root.solution_logprob_under_policy(pi)
            log.debug(f'logprob under policy after training: {prob}')
            root = TreeSearchNode(HolophrasmNode([nng.initialize_problem('a_zero_add')]))
            success, _, _, it = mcts.evaluate(root)
            assert success
            log.debug(f'solved in {it} MCTS iterations.')
            examples = pi.extract_examples(root)



@hydra.main(version_base="1.2", config_path="config", config_name="proofsearch")
def main(cfg: DictConfig):
    mle_log = setup_mle_logger(cfg)
    if cfg.task == 'proofsearch':
        run_proof_search_agent(cfg, mle_log)
    elif cfg.task == 'mcts_example':
        mcts_example(cfg, mle_log)
    elif cfg.task == 'interact':
        test_proof_search(problemset=cfg.get('problemset'),
                          problem=cfg.get('problem'),
                          agent_path=cfg.get('agent_path'))
    elif cfg.task == 'test':
        test_probability_under_policy(mle_log)
    elif cfg.task == 'eval':
        evaluate_agent(cfg, mle_log)
    elif cfg.task == 'visualize':
        test_agent(cfg)


if __name__ == '__main__':
    main()

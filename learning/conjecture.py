#!/usr/bin/env python3

import unittest
from dataclasses import dataclass
from typing import Union, Optional
import random
import re
import math

import peano
from util import batch_inference


# Grammar for conjectures:
# Conjecture := Prop
# Prop := App [-> Prop] | Arrow
# App := "(" f arg* ")"
# Atom := name
# Decl := "(" Atom ":" Type ")"
# Arrow := "[" decl* Prop "]"


ALLOW_PROP_AS_TYPE = True


@dataclass
class Context:
    derivation: peano.PyDerivation
    target_type: Optional[str]
    decls: list[(str, str)]

    def with_target_type(self, target: str) -> 'Context':
        return Context(self.derivation, target_type=target, decls=self.decls)

    def next_name(self):
        return "'" + f"a{len(self.decls)}"

    def clone(self):
        return Context(self.derivation.clone(),
                       self.target_type,
                       self.decls.copy())


class Node:
    @staticmethod
    def parse(tokens: list[str], context) -> ('Node', int, list[str]):
        raise NotImplementedError

    def __str__(self) -> str:
        raise NotImplementedError


@dataclass
class Conjecture(Node):
    prop: 'Prop'

    @staticmethod
    def parse(tokens: list[str], context):
        return Prop.parse(tokens, context)

    def __str__(self):
        return str(self.prop)


@dataclass
class Prop(Node):
    prop: Union['App', 'Arrow', 'Atom']

    @staticmethod
    def parse(tokens: list[str], context):
        context = context.with_target_type('prop')
        node, consumed, completions = App.parse(tokens, context)

        if node:
            return Prop(node), consumed, completions

        node, consumed, completions_atom = Atom.parse(tokens, context)

        if consumed:
            return node, consumed, completions_atom

        node_a, consumed_a, completions_a = Arrow.parse(tokens, context)
        return node_a, consumed_a, completions + completions_atom + completions_a

    def __str__(self):
        return str(self.prop)


@dataclass
class App(Node):
    function: 'Atom'
    args: list['Value']

    @staticmethod
    def parse(tokens: list[str], context):
        consumed = 0

        if not tokens:
            _, _, possible_arrows = Atom.parse([],
                                               context.with_target_type(f'-> {context.target_type}'))
            if possible_arrows:
                return None, 0, ['(']
            else:
                # No arrow gives the desired type, so this cannot be an application.
                return None, 0, []

        if tokens[0] == '(':
            consumed += 1
        else:
            return None, 0, []

        fn_node, fn_consumed, completions = Atom.parse(tokens[consumed:],
                                                       context.with_target_type(f'-> {context.target_type}'))
        consumed += fn_consumed

        if not (fn_node and fn_node.name):
            return None, consumed, completions

        fn_input_types, _fn_output_type = context.derivation.arrow_type_signature(fn_node.name)
        n_args = len(fn_input_types)

        # OK, now we know the function - need to just take all the arguments
        arg_nodes = [None] * n_args
        substitutions = []

        for i in range(n_args):
            target_type = fn_input_types[i][1]
            for k, v in substitutions:
                # TODO(gpoesia): use proper non-capturing substitution here.
                target_type = target_type.replace(k, v)

            arg_node, arg_consumed, arg_completions = Value.parse(
                tokens[consumed:],
                context.with_target_type(target_type))

            consumed += arg_consumed

            if arg_node:
                arg_nodes[i] = arg_node
            else:
                return None, consumed, arg_completions

            if fn_input_types[i][0]:
                substitutions.append((fn_input_types[i][0], str(arg_node)))

        if len(tokens) > consumed and tokens[consumed] == ')':
            return App(fn_node, arg_nodes), consumed + 1, []
        if len(tokens) == consumed:
            return None, consumed, [')']
        raise ValueError('Parse error: expected \')\' after App arguments.')


    def __str__(self):
        return '(' + ' '.join(map(str, [self.function] + (self.args or []))) + ')'


@dataclass
class Atom(Node):
    name: str

    @staticmethod
    def is_atom_token(s: str) -> bool:
        return not any(c in s for c in '()[]:')

    @staticmethod
    def parse(tokens: list[str], context):
        if tokens:
            if Atom.is_atom_token(tokens[0]):
                return Atom(tokens[0]), 1, []
            return None, 0, []

        if context.target_type:
            if context.target_type.startswith('-> '):
                target_output_type = context.target_type.lstrip('-> ')
                options = context.derivation.arrows_with_target_type(target_output_type)

                # TODO: Add arrows with the desired target type from context.decls.
            else:
                options = context.derivation.declared_atoms_with_type(context.target_type)

                if not ALLOW_PROP_AS_TYPE and context.target_type == 'type':
                    options = [o for o in options if o != 'prop']

                for name, dtype in context.decls:
                    if (str(dtype) == context.target_type and
                        (name != 'prop' or ALLOW_PROP_AS_TYPE)):
                        options.append(name)

            return None, 0, options

        raise ValueError('Atom.parse: context missing a target type')

    def __str__(self):
        return self.name


@dataclass
class Value(Node):
    value: Union['Atom', 'App']

    @staticmethod
    def parse(tokens: list[str], context):
        node, consumed, completions = Atom.parse(tokens, context)

        if consumed:
            return node, consumed, completions

        node_app, consumed_app, completions_app = App.parse(tokens, context)

        if consumed_app:
            return node_app, consumed_app, completions_app

        return None, 0, completions + completions_app

    @staticmethod
    def parse_with_target_type_options(tokens: list[str], context, target_types):
        completions = []

        for t in target_types:
            node, consumed, completions_t = Value.parse(
                tokens, context.with_target_type(t))

            if node:
                return node, consumed, completions_t

            completions += completions_t

        return node, consumed, completions

    def __str__(self):
        return str(self.value)


@dataclass
class Decl(Node):
    name: str
    dtype: Value

    def __str__(self):
        return f'({self.name} : {self.dtype})'

    @staticmethod
    def parse(tokens: list[str], context):
        if not tokens:
            return None, 0, ['(']

        if tokens[0] != '(':
            return None, 0, []

        consumed, tokens = 1, tokens[1:]

        if not tokens:
            # Since we're not sure yet this is a declaration,
            # don't consume the '('.
            return None, 0, [context.next_name()]

        name, tokens, consumed = tokens[0], tokens[1:], consumed + 1

        # Different name, not a declaration.
        if name != context.next_name():
            return None, 0, []

        # From here onwards we know this is a declaration, since it has
        # the next declaration name.
        if not tokens:
            return None, 1, [' : ']

        tokens, consumed = tokens[1:], consumed + 1

        # Parse either type or prop.
        dtype, consumed_dtype, completions = Value.parse_with_target_type_options(
            tokens, context, ['type', 'prop'])
        tokens, consumed = tokens[consumed_dtype:], consumed + consumed_dtype

        if not dtype:
            return None, consumed, completions

        if not tokens:
            return None, consumed, [')']

        if tokens[0] != ')':
            raise ValueError(f'Parse error: declaration should end with ), not {tokens[0]}')

        context.decls.append((name, dtype))

        return Decl(name, dtype), consumed + 1, []


@dataclass
class Arrow(Node):
    input_types: list['Decl']
    output_type: 'Value'

    def __str__(self):
        return '[' + ' -> '.join(map(str, self.input_types + [self.output_type])) + ']'

    @staticmethod
    def parse(tokens: list[str], context):
        consumed = 0

        if not tokens:
            return None, 0, ['[']

        if tokens[0] == '[':
            tokens, consumed = tokens[1:], 1
        else:
            return None, 0, []

        input_types = []
        output_type = None

        while True:
            decl_node, decl_consumed, decl_completions = Decl.parse(tokens, context)
            consumed, tokens = consumed + decl_consumed, tokens[decl_consumed:]

            if decl_node:
                input_types.append(decl_node)

                if tokens and tokens[0] == '->':
                    tokens = tokens[1:]
                else:
                    return None, consumed, [' -> ']

                continue

            # If either this is the first element of the arrow (empty input_types)
            # or we're in the middle of the Decl, return.
            if decl_consumed or not input_types:
                return None, consumed, decl_completions

            # Otherwise, also try to parse the output type.
            out_node, out_consumed, out_completions = Value.parse(tokens, context)
            consumed, tokens = consumed + out_consumed, tokens[out_consumed:]

            if out_node:
                # We parsed all input types and now also the output type.
                output_type = out_node
                break

            return None, consumed, decl_completions + out_completions

        if not tokens:
            return None, consumed, [']']

        if tokens[0] != ']':
            raise ValueError('Parse error: expected \']\' after Arrow components.')

        return Arrow(input_types, output_type), consumed + 1, []


def tokenize(s):
    for t in '()[]{}:':
        s = s.replace(t, f' {t} ')
    return s.split()


def sorted_by_score(conjectures, lm, prefix):
    scores = lm.score([prefix + c for c in conjectures])
    xy = list(zip(conjectures, scores))
    xy.sort(key=lambda kv: kv[1], reverse=True)
    return [x for x, _ in xy]


def pretty_print_conjecture(conjecture: str) -> str:
    'Converts a conjecture accepted by the completion engine back to concrete Peano syntax.'
    # HACK: In general, this should remove the first argument of '=', which is implicit in Peano,
    # but this works for now since we're not experimenting with polymorphic types.
    conjecture = conjecture.replace('{', '(').replace('}', '}').replace(')(', ') (').strip()
    return re.sub('\\(= \\w+', '(=', conjecture)


MAX_OPEN_PARENS = 8

def sample_conjecture(lm, context, max_it=100):
    generation = ''

    for _ in range(max_it):
        tokens = tokenize(generation)
        node, _, completions = Conjecture.parse(tokens, context.clone())

        if node:
            return generation

        completions = list(set(space_completions(generation, completions)))

        choice = ''

        while completions != ['']:
            # Compute maximum common prefix among all completions.
            max_common_prefix_len = 0

            if not completions:
                # print('Dead end in conjecturing:', generation)
                break

            for l in range(0, len(completions[0])):
                if all(c.startswith(completions[0][:l]) for c in completions):
                    max_common_prefix_len = l
                else:
                    break

            # Add the maximum common prefix to the generation, which doesn't need the LM.
            generation += completions[0][:max_common_prefix_len]
            completions = [c[max_common_prefix_len:] for c in completions]

            if '' in completions:
                break

            # Sample the next character using the LM.
            choices = list(set(c[0] for c in completions))
            choice = random.choices(choices, list(map(math.exp,
                                                      lm.score(choices, mean=False, prefix=generation))))[0]
            generation += choice
            # Filter completions to those starting with the chosen character and drop the character.
            completions = [c[1:] for c in completions if c.startswith(choice)]

    return None

def conjecture_logprob_under_lm(lm, context, conjecture, mean=False):
    generation = ''
    logprob = 0

    while generation != conjecture:
        tokens = tokenize(generation)
        node, _, completions = Conjecture.parse(tokens, context.clone())

        if node:
            break

        completions = list(set(space_completions(generation, completions)))

        choice = ''

        while choice not in completions:
            # Compute maximum common prefix among all completions.
            max_common_prefix_len = 0

            if not completions:
                # print('Dead end in conjecturing:', generation)
                break

            for l in range(0, len(completions[0])):
                if all(c.startswith(completions[0][:l]) for c in completions):
                    max_common_prefix_len = l
                else:
                    break

            # Add the maximum common prefix to the generation, which doesn't need the LM.
            generation += completions[0][:max_common_prefix_len]
            completions = [c[max_common_prefix_len:] for c in completions]

            if '' in completions:
                break

            # Score the next character under the LM
            choices = list(set(c[0] for c in completions))
            choice_in_conjecture = conjecture[len(generation)]

            assert choice_in_conjecture in choices

            logprobs = lm.score(choices, mean=False, prefix=generation)
            partition = sum(math.exp(lp) for lp in logprobs)
            logprob += math.log(math.exp(logprobs[choices.index(choice_in_conjecture)]) / partition)
            generation += choice_in_conjecture
            completions = [c[1:] for c in completions if c.startswith(choice)]

    return logprob / ((len(conjecture) + 1) if mean else 1)


def conjecture_beam_search(lm, context, n_conjectures=100, prefix='', min_it=10, max_it=10, ignored_conjectures=[]):
    candidates = ['']
    complete = set()
    it = 0

    beam_size = 5 * n_conjectures

    while candidates and (it < min_it or len(complete) < n_conjectures) and it < max_it:
        it += 1
        next_candidates = []

        for candidate in candidates:
            tokens = tokenize(candidate)
            node, _, completions = Conjecture.parse(tokens, context.clone())

            if node:
                complete.add(str(node))
            else:
                if not (candidate and candidate[-1] in '()[]{}'):
                    candidate += ' '
                next_candidates.extend([candidate + c
                                        for c in set(completions)
                                        if c != ')' or candidate.count(')') < MAX_OPEN_PARENS
                                        ])

        candidates = sorted_by_score(next_candidates, lm, prefix)

        if len(candidates) > beam_size:
            candidates, discarded = candidates[:beam_size], candidates[beam_size:]
            print('Discarding', len(discarded), 'candidates:', discarded)

    complete = [c for c in complete if c not in ignored_conjectures]
    print('Finished - have', len(complete), 'complete conjectures.')
    print(len(candidates), 'incomplete conjectures:', candidates)
    print('Complete:', complete)
    return [(pretty_print_conjecture(c), c)
            for c in sorted_by_score(complete, lm, prefix)[:n_conjectures]]


class RandomLM:
    def score(self, candidates, mean=True, prefix=''):
        return [random.random() for c in candidates]


class AgentLM:
    def __init__(self, agent, prompt: str):
        self._agent = agent
        self._prompt = prompt

    @batch_inference(10000)
    def score(self, candidates, mean=True, prefix=''):
        return list(self._agent._policy._lm.completion_logprob(
            [self._prompt + prefix] * len(candidates),
            candidates,
            False,
            mean=mean,
        ))


def space_completions(prefix, completions):
    spaced_completions = []
    end_needs_space = prefix and prefix[-1] not in '[( '

    for c in completions:
        if c[0] not in ')]' and end_needs_space and c[-1] != ' ':
            spaced_completions.append(' ' + c)
        else:
            spaced_completions.append(c)

    return spaced_completions

class ConjectureCompletionEngineTest(unittest.TestCase):
    def test_spaced_completions(self):
        prefix = '(='
        completions = ['y', 'z']
        expected = [' y', ' z']
        self.assertEqual(space_completions(prefix, completions), expected)

        prefix = '((('
        completions = expected = [')']
        self.assertEqual(space_completions(prefix, completions), expected)

        prefix = '((+'
        completions = ['(']
        expected = [' (']
        self.assertEqual(space_completions(prefix, completions), expected)

        prefix = "[('a : nat) -> nat"
        completions = expected = [']']
        self.assertEqual(space_completions(prefix, completions), expected)


    def test_nat_equality(self):
        theory = '''nat : type. p : prop. = : [('t : type) -> 't -> 't -> prop]. z : nat. s : [nat -> nat]. h : (= z z).'''

        d = peano.PyDerivation()
        d.incorporate(theory)

        context = Context(d, None, [])
        s = "[('a0 : nat) -> (= nat z z)]"
        tokens = tokenize(s)

        node, _, completions = Conjecture.parse(tokens, context)
        completions = space_completions(s, completions)
        print('Completions:', completions)
        print('Parsed node:', node)
        print(context.decls)

    def test_beam_search(self):
        theory = '''
        nat : type.
        = : [('t : type) -> 't -> 't -> prop].
        z : nat.
        s : [nat -> nat].
        + : [nat -> nat -> nat].
        '''

        d = peano.PyDerivation()
        d.incorporate(theory)

        context = Context(d, None, [])
        lm = RandomLM()

        conjectures = conjecture_beam_search(lm, context, 1000, '', 100)
        print('Conjectures:')

        for i, (c, _) in enumerate(conjectures[:100]):
            print(f'#{i}. {c}')

    def test_sample_conjecture(self):
        # Sample 100 conjectures from a random LM.

        theory = '''
        nat : type.
        = : [('t : type) -> 't -> 't -> prop].
        z : nat.
        s : [nat -> nat].
        + : [nat -> nat -> nat].
        '''

        d = peano.PyDerivation()
        d.incorporate(theory)

        context = Context(d, None, [])
        import proofsearch
        from omegaconf import DictConfig
        agent = proofsearch.ProofSearchAgent(DictConfig({'policy': {'type': 'LM'}}))
        lm = AgentLM(agent, '')

        for _ in range(100):
            print(sample_conjecture(lm, context, '', 100))

    def test_propositional_logic_conjectures(self):
        with open('theories/propositional-logic.p', 'r') as f:
            theory = f.read()

        d = peano.PyDerivation()
        d.incorporate(theory)

        context = Context(d, None, [])
        lm = RandomLM()
        for _ in range(50):
            print(sample_conjecture(lm, context, 50))

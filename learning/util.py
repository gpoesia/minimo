#!/usr/bin/env python3

import collections
import math
import random
import os
import logging
import json
import signal
from contextlib import contextmanager
from functools import wraps

import altair
import torch
import wandb
import numpy as np
from omegaconf import DictConfig, OmegaConf, open_dict
from tqdm import tqdm


PAD = 0
BOS = 1
EOS = 2
POSITIVE = ord(';')
NEGATIVE = ord('$')
EMPTY = '\x03'

def count_parameters(model):
    return sum(math.prod(p.shape) for p in model.parameters())


def format_parameter_count(model):
    n = count_parameters(model)

    if n < 1000:
        return str(n)
    if n < 10**6:
        return f'{n // 10**3}K'
    if n < 10**9:
        return f'{n / 10**6:.1f}M'

    return f'{n / 10**6:.1f}B'


def encode_batch(b: list[str], device: torch.device, bos=True, eos=True) -> torch.LongTensor:
    if not b:
        return torch.tensor([], dtype=torch.long, device=device)

    max_len = max(map(len, b))

    return torch.tensor([[BOS] * bos +
                         list(map(ord, o)) +
                         [EOS] * eos +
                         [PAD] * (max_len - len(o))
                         for o in b],
                        dtype=torch.long,
                        device=device)

def decode_batch(b: torch.LongTensor) -> list[str]:
    return [''.join(chr(c) for c in row if c > EOS) for row in b]


def sample_batch(examples: list[str], batch_size: int, trim_len: int = 500) -> list[str]:
    'Samples a batch of examples with a bounded total number of characters'
    batch = []
    max_size = 0

    while True:
        example = random.choice(examples)
        example_len = min(len(example), trim_len)
        max_size = max(max_size, example_len)

        if max_size * (1 + len(batch)) > batch_size:
            break

        batch.append(example)

    return batch


def batch_strings(s: list[str], batch_size: int) -> list[str]:
    '''Batches a list of strings into small batches with a bounded
    total number of characters in each.'''

    batches = []

    stack = s[::-1]

    while stack:
        batch = []
        max_size = 0

        while stack:
            example = stack.pop()
            max_size = max(max_size, len(example))

            if batch and max_size * (1 + len(batch)) > batch_size:
                stack.append(example)
                break

            batch.append(example)
        batches.append(batch)

    return batches


def log(x):
    'Safe version of log'
    return math.log(1e-50 + max(0, x))

def softmax(logits: torch.Tensor, temperature = 1.0):
    s = logits.exp() / temperature
    return s / s.sum()


def pop_max(l: list, key) -> (object, list):
    if not l:
        return None, l

    i_max = max(range(len(l)), key=lambda i: key(l[i]))
    l[-1], l[i_max] = l[i_max], l[-1]
    return l[-1], l[:-1]


def shuffle_state(s: str) -> str:
    'Perform data augmentation for Peano states by shuffling e-classes and e-nodes'

    eclasses = s.split('; ')
    random.shuffle(eclasses)

    for i in range(len(eclasses)):
        enodes, dtype = eclasses[i].split(' : ')
        # Strip '{' and '}'
        enodes = enodes.lstrip('{').rstrip('}').split('=')
        random.shuffle(enodes)

        eclasses[i] = f'{{{"=".join(enodes)}}} : {dtype}'

    return '; '.join(eclasses)


def parse_sexp(s: str, ptr: int = 0) -> (object, int):
    while ptr < len(s) and s[ptr] == ' ':
        ptr += 1

    if s[ptr] == '(':
        # Read list
        ptr += 1 # Consume (
        l = []
        while s[ptr] != ')':
            elem, ptr = parse_sexp(s, ptr)
            l.append(elem)
        ptr += 1 # Consume )
        return l, ptr
    else:
        # Read atom
        before = ptr
        while ptr < len(s) and s[ptr] not in ' ()':
            ptr += 1
        return s[before:ptr], ptr


def randomize_atoms(sexp, criteria, sample, mapping):
    if isinstance(sexp, str):
        if sexp in mapping:
            return mapping[sexp]

        if criteria(sexp):
            v = str(sample())
            mapping[sexp] = v
            return v

        return sexp
    return [randomize_atoms(s, criteria, sample, mapping) for s in sexp]


def format_sexp(sexp, level=0, indent=0):
    if isinstance(sexp, str):
        return level * indent * ' ' + sexp
    sep = ' ' if not indent else '\n  '
    return ((level * indent * ' ') +
            '(' + sep.join(map(lambda e: format_sexp(e, level + 1, indent), sexp)) + ')')


def toggle_infix(sexp):
    if isinstance(sexp, str):
        return sexp
    children = list(map(toggle_infix, sexp))
    if len(children) == 3:
        return [children[1], children[0], children[2]]
    return children


def randomly_mask_atoms(sexp, probability):
    if isinstance(sexp, str):
        if random.random() < probability:
            return '?'
        return sexp

    return list(map(lambda elem: randomly_mask_atoms(elem, probability), sexp))


def randomly_mask_goal_terms(goal: str, probability=0.1) -> str:
    'Perform data augmentation for Peano goals by masking some sub-terms'

    sexp, _ = parse_sexp(goal)
    sexp = randomly_mask_atoms(sexp, probability)
    return format_sexp(sexp)


def get_device(cfg):
    if cfg is None:
        return torch.device('cpu')

    if isinstance(cfg, int):
        return torch.device(cfg)

    if cfg.get('gpu') is not None:
        return torch.device(cfg.gpu)

    return torch.device('cpu')


def choose_from_list(prompt, l, to_str=str):
    print(prompt)
    for i, e in enumerate(l):
        print(f'{i:2d} - ', to_str(e))

    return l[int(input('> '))]


def setup_wandb(cfg: DictConfig):
    if cfg.job.get("wandb_project"):
        with open_dict(cfg.job):
            cfg.job.cwd = os.getcwd()
        wandb.init(
                project=cfg.job.wandb_project,
                resume=cfg.job.get('resume', False),
                config=OmegaConf.to_container(cfg, resolve=True, throw_on_missing=True))
        for key in logging.Logger.manager.loggerDict.keys():
            if key.startswith('wandb'):
                logging.getLogger(key).setLevel(logging.WARNING)
    else:
        # Disable wandb (i.e., make log() a no-op).
        wandb.log = lambda *args, **kwargs: None


def count_inversions(l: list):
    '''Counts the number of inversions in a list.
    Complexity: O(nk), where n = len(l) and k = len(set(l)); thus,
    works well if k is small.
    '''
    counts = collections.defaultdict(int)
    inversions = 0

    for i, val in enumerate(l):
        for key, cnt in counts.items():
            if key > val:
                inversions += cnt
        counts[val] += 1

    return inversions


def plot_vegalite(template: str, data: list, output_path: str, translations={}):
    with open(f'vega-lite/{template}.json') as f:
        spec = json.load(f)

    spec['data'] = {'values': data}
    spec = translate_object(spec, translations)

    with open(output_path + '.json', 'w') as f:
        json.dump(spec, f)

    # altair.Chart.from_dict(spec).save(output_path) # , scale_factor=5)


def bootstrap_mean_ci(trials, confidence):
    estimates = []

    for i in range(5000):
        estimates.append(np.mean(random.choices(trials, k=len(trials))))

    bounds = ((1 - confidence) / 2, 1 - (1 - confidence) / 2)
    return np.mean(estimates), tuple(np.quantile(estimates, bounds, method='nearest'))


def format_blocks_with_indent(content, level=0, indent=4, header=1, suffix=1):
    if isinstance(content, str):
        return ' ' * (level * indent) + content
    assert isinstance(content, list)
    pieces = []
    for i, l in enumerate(content):
        pieces.append(format_blocks_with_indent(l, level + (i >= header and i < len(content) - suffix),
                                                indent, header))
    return '\n'.join(pieces)

def value_color(value: float) -> str:
    'Given a node value estimate between 0 and 1, returns a color for its node in GraphViz.'

    import coloraide

    BAD = coloraide.Color('#ff837a')
    GOOD = coloraide.Color('#1c7d13')

    c = BAD.mix(GOOD, value).convert('srgb')

    return c.to_string(hex=True)

# Adapted from https://stackoverflow.com/questions/366682/how-to-limit-execution-time-of-a-function-call
@contextmanager
def time_limit(seconds):
    def signal_handler(signum, frame):
        raise TimeoutError("Timed out")
    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)

    try:
        yield
    finally:
        signal.alarm(0)


def save_json(obj, path):
    with open(path, 'w') as f:
        json.dump(obj, f)


def replace(l: tuple, i: int, x: object):
    return l[:i] + (x,) + l[i+1:]


def batch_inference(batch_size: int = 10000, arg_index=0):
    def batch_decorator(method):
        @wraps(method)
        def batched_method(self, *args, **kwargs):
            l = args[arg_index]
            batch, batch_current_size = [], 0
            result = []

            for i in range(len(l) + 1):
                if i < len(l):
                    batch.append(l[i])
                    batch_current_size += len(l[i])

                if (i == len(l) and batch) or batch_current_size >= batch_size:
                    result.extend(method(self,
                                         *replace(args, arg_index, batch),
                                         **kwargs))
                    batch, batch_current_size = [], 0

            return result

        return batched_method
    return batch_decorator

def tqdm_if(verbose):
    return tqdm if verbose else lambda x: x

def translate_object(obj, translations):
    if isinstance(obj, dict):
        new_obj = {}
        for key, value in obj.items():
            if key in translations:
                new_obj[translations[key]] = translate_object(value, translations)
            else:
                new_obj[key] = translate_object(value, translations)
        return new_obj
    elif isinstance(obj, list):
        return [translate_object(item, translations) for item in obj]
    elif isinstance(obj, str):
        return translations.get(obj, obj)
    else:
        return obj

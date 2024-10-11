#!/usr/bin/env python3

import logging

import torch
import transformers
from torch import nn
import torch.nn.functional as F
import wandb
from tqdm import tqdm
import numpy as np

from util import (
    log, softmax, pop_max, batch_strings, encode_batch, decode_batch,
    sample_batch, PAD, EOS, BOS, POSITIVE, NEGATIVE, EMPTY,
    batch_inference
)


logger = logging.getLogger(__name__)


# Left-truncate states to have at most this number of characters.
# This is to avoid overly large inputs to the state embedding model.
MAX_STATE_LENGTH = 200


class TransformerLMPolicy(nn.Module):
    def __init__(self, config):
        super().__init__()

        if torch.cuda.is_available():
            cfg = transformers.GPT2Config(
                vocab_size=128,
                n_layer=config.get('n_layer', 8),
                n_head=config.get('n_head', 8),
                n_embd=config.get('n_embd', 512),
                bos_token_id=BOS,
                eos_token_id=EOS,
                pad_token_id=PAD,
                n_positions=1024)
            device = torch.device(0)
        else:
            # Debugging on a CPU
            cfg = transformers.GPT2Config(
                vocab_size=128,
                n_layer=2,
                n_head=2,
                n_embd=128,
                bos_token_id=BOS,
                eos_token_id=EOS,
                pad_token_id=PAD,
                n_positions=512)
            device = torch.device('cpu')

        self._lm = transformers.GPT2LMHeadModel(cfg).to(device)
        self._optimizer = torch.optim.AdamW(self._lm.parameters(), lr=config.get('lr', 1e-4))

    def get_loss(self, strs):
        _, input_ids = self._strs_to_token_ids(strs, True)
        labels = input_ids.clone()
        labels[labels == PAD] = -100
        attn_mask = input_ids != PAD
        return self._lm.forward(input_ids, attention_mask=attn_mask, labels=labels).loss

    def fit(self, examples, batch_size, n_steps, verbose=False):
        self._lm.train()

        rng = range(n_steps)

        if verbose:
            rng = tqdm(rng)

        for i in rng:
            b = sample_batch(examples, batch_size)
            self._optimizer.zero_grad()
            loss = self.get_loss(b)
            loss.backward()
            wandb.log({'train_loss': loss})
            self._optimizer.step()

        self._lm.eval()

    def gradient_step(self, strs, return_norm=False):
        self._lm.train()
        self._optimizer.zero_grad()
        loss = self.get_loss(strs)
        return_value = loss.item()

        loss.backward()

        if return_norm:
            norm = 0
            for p in self._lm.parameters():
                norm += (p.grad ** 2).sum()
            norm = norm.sqrt()
            return_value = norm.item()

        self._optimizer.step()
        self._lm.eval()

        return return_value

    def estimate_state_values(self, states: list[str]) -> np.array:
        return self._estimate_query_values([self.format_state_query(s) for s in states])

    def estimate_state_action_values(self, state: str, actions: list[str]) -> np.array:
        return self._estimate_query_values([self.format_state_action_query(state, a) for a in actions])

    def estimate_state_and_action_values(self, state: str, actions: list[str], children: list[str]) -> (np.array, np.array):
        st_queries = [self.format_state_query(s) for s in children]
        sa_queries = [self.format_state_action_query(state, a) for a in actions]
        all_queries = st_queries + sa_queries
        ans = self._estimate_query_values(all_queries)
        st_ans = ans[:len(st_queries)]
        sa_ans = ans[len(st_queries):]
        return st_ans, sa_ans

    @batch_inference(10000)
    def _estimate_query_values(self, strs: list[str]) -> np.array:
        l, token_ids = self._strs_to_token_ids(strs)
        attn_mask = token_ids != PAD

        last_id = [x - 1 for x in l]

        assert token_ids.shape[1] < 500
        # assert token_ids.shape[0] * token_ids.shape[1] < 10000

        with torch.no_grad():
            out = self._lm(token_ids, attention_mask=attn_mask)

        assert max(last_id) < out.logits.shape[1]

        last_preds = out.logits[torch.arange(len(strs)), last_id, :]

        pos_logit = last_preds[:, ord('Y')]
        neg_logit = last_preds[:, ord('N')]

        vs = pos_logit.exp() / (pos_logit.exp() + neg_logit.exp())
        return vs.detach().cpu().numpy()

    def format_state_query(self, state, label=''):
        if len(state) > 490:
            state = '[...] ' + state[-490:]
        return f'S: {state}\n???{label}'

    def format_provable_goal(self, context, goal):
        return f'S: {context}\nENTAILS: {goal}'

    def sample_provable_goals(self, context, n=10, l=100):
        prefix = self.format_provable_goal(context, '')
        input_ids = self._strs_to_token_ids([prefix])[1]
        p_len = input_ids.shape[1]
        out = self._lm.generate(input_ids, output_scores=True, return_dict_in_generate=True,
                                max_length=l + len(prefix), num_return_sequences=n, do_sample=True)
        strs = [''.join(map(chr, s[p_len:])).strip('\x00') for s in out['sequences']]
        scores = [0] * len(strs)
        for i in range(len(strs)):
            for j in range(p_len, len(strs[i]) - 2):
                ch = ord(strs[i][j - p_len])
                dist = np.exp(out.scores[j - p_len][i].cpu().numpy())
                logprob = np.log(dist[ch] / dist.sum())
                if np.isinf(logprob):
                    breakpoint()
                scores[i] += logprob
        return strs, scores # seqs, scores

    def goal_logprob(self, context: str, goal: str, aggregation: str = 'sum', step=False) -> float:
        return self.goals_logprob(context, [goal], aggregation, step)

    def goals_logprob(self, context: str, goals: list[str], aggregation: str = 'sum', step=False) -> list[float]:
        for i in range(len(goals)):
            if len(goals[i]) > 400:
                goals[i] = '[...] ' + goal[i][-400:]
        prefix = self.format_provable_goal(context, '')
        g_strs = [self.format_provable_goal(context, g) for g in goals]
        return self.completion_logprob([prefix] * len(goals), g_strs, step)

    def completion_logprob(self, preambles: list[str], completions: list[str],
                           step: bool = False, mean: bool = False):
        complete_strs = [p + s for p, s in zip(preambles, completions)]
        input_ids = self._strs_to_token_ids(complete_strs)[1]
        attn_mask = input_ids != PAD

        # Mask out the preamble for the completion logprob calculation.
        preamble_mask = torch.zeros_like(attn_mask)
        preamble_mask[torch.arange(len(preambles)), [len(p) for p in preambles]] = 1
        preamble_mask = preamble_mask.cumsum(axis=1)[:, :-1]

        out = self._lm(input_ids, attention_mask=attn_mask)
        logprobs = out.logits.log_softmax(-1)

        idx = torch.tensor([([ord(s_i[j]) for j in range(len(s_i))] +
                             [0] * (attn_mask.shape[1] - 1 - len(s_i)))
                            for s_i in complete_strs],
                           dtype=torch.long,
                           device=logprobs.device)

        token_logprobs = logprobs.gather(-1, idx.unsqueeze(-1)).squeeze(-1)
        token_logprobs *= attn_mask[:, 1:]

        if step:
            loss = -token_logprobs.mean()
            self._optimizer.zero_grad()
            loss.backward()
            self._optimizer.step()

        token_logprobs = token_logprobs.detach()
        token_logprobs *= preamble_mask

        logprobs = token_logprobs.cpu().sum(axis=1)

        if mean:
            logprobs /= torch.tensor([len(c) for c in completions])

        return logprobs.tolist()

    def action_logprobs(self, state: str, actions: list[str]) -> list[float]:
        prefix = self.format_state_action_choice(state, '')
        strs = [self.format_state_action_choice(state, a) for a in actions]
        action_input_ids = self._strs_to_token_ids(strs)[1]

        with torch.no_grad():
            out = self._lm(action_input_ids)

        logprobs = F.log_softmax(out.logits, dim=2)
        action_logprobs = []

        for i, a in enumerate(actions):
            chr_logprobs = logprobs[i][range(len(strs[i])), list(map(ord, strs[i]))]
            action_logprobs.append(chr_logprobs[len(prefix):].sum().cpu().numpy())

        return np.array(action_logprobs)

    def sample_actions(self, state, n=10, l=60):
        prefix = self.format_state_action_choice(state, '')
        input_ids = self._strs_to_token_ids([prefix])
        seqs, scores, _, _ = self._lm.generate(input_ids, output_scores=True, return_dict_in_generate=True,
                                               max_length=l, num_beams=n)
        return seqs, scores

    def format_state_action_choice(self, state, action):
        return f'S: {state}\nSTEP: {action}'

    def format_state_action_query(self, state, action, label=''):
        return f'S: {state}\nA: {action}\n???{label}'

    def _strs_to_token_ids(self, strs: list[str], eos=False) -> torch.tensor:
        # strs = [s.replace(' ', '').replace('\n', '') for s in strs[:]]
        # Trim strings if too long.
        for i in range(len(strs)):
            if len(strs[i]) > 490:
                strs[i] = '[...] ' + strs[i][-490:]

        ids = [[BOS] + list(s.encode('ascii')) + eos*[EOS]
               for s in strs]

        lengths = list(map(len, ids))
        max_length = max(lengths)
        ids = [l + (max_length - len(l)) * [PAD] for l in ids]

        assert 0 <= np.min(ids) and np.max(ids) < 128
        return lengths, torch.tensor(ids, device=self._lm.device)


def make_policy(config):
    if 'type' not in config:
        raise ValueError(f'Policy config must have a \'type\'')
    if config.type == 'TransformerLM':
        return TransformerLMPolicy(config)
    raise ValueError(f'Unknown policy type {config.type}')

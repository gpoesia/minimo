#!/usr/bin/env python3

import io
from dataclasses import dataclass
from typing import Optional
import traceback
import os

import torch
from omegaconf import DictConfig
from celery import Celery

import peano
import proofsearch
import policy
import hindsight

@dataclass
class StudentResult:
    error: Optional[str]
    success: bool
    problem: str
    solution_actions: Optional[list[str]]
    proof: Optional[list[str]]
    extracted_examples: list[str]
    hindsight_examples: list[hindsight.HindsightExample]
    iterations: int
    logprob: float


@dataclass
class BackgroundTheory:
    theory: str
    premises: list[str]


redis_url = f'redis://{os.environ.get("REDIS", "localhost")}'
app = Celery('worker', backend=redis_url, broker=redis_url)
app.conf.task_serializer = 'pickle'
app.conf.result_serializer = 'pickle'
app.conf.accept_content = ['application/json', 'application/x-python-serialize']


@app.task
def try_prove(agent_dump: bytes, theory: BackgroundTheory, statement: str) -> StudentResult:
    with io.BytesIO(agent_dump) as f:
        agent = torch.load(f, weights_only=False)

    print('Proving', statement, 'on', agent._policy._lm._lm.device)

    state = peano.PyProofState(theory.theory,
                               theory.premises,
                               statement)

    try:
        agent_result = agent.proof_search(statement, state)

        if agent_result.success:
            proof = agent_result.root.state_node.reconstruct_proof(
                agent_result.root.get_solution_actions())
            solution_actions = agent_result.root.get_solution_actions()
            logprob = agent_result.root.solution_logprob_under_policy(agent._policy, solution_actions)
        else:
            solution_actions, proof, logprob = None, None, None

        examples = []
        # Policy examples for the proved goal.
        examples.extend(agent._policy.extract_examples(root=agent_result.root))
        # Hindsight examples (policy + conjecturing).
        hindsight_examples = hindsight.extract_hindsight_examples(
                agent_result.root,
                theory.theory,
                theory.premises,
                agent._policy)

        return StudentResult(
            None,
            agent_result.success,
            statement,
            list(map(str, solution_actions)) if solution_actions else None,
            proof,
            agent_result.examples,
            hindsight_examples,
            agent_result.iterations,
            logprob,
        )
    except BaseException as e:
        tb = traceback.format_exception(e)
        print('Error in try_prove!')
        print(tb)
        return StudentResult(tb, False, statement, None, None, [],
                             None, None, None)

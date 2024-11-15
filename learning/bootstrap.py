#!/usr/bin/env python3

"""Implements the conjecture-prove bootstrapping learning loop."""

import asyncio
import os
import io
import json
import datetime

import hydra
from omegaconf import DictConfig
import torch
import numpy as np
from tqdm import tqdm

import peano
import worker
from worker import StudentResult  # noqa
from hindsight import HindsightExample  # noqa
from util import format_blocks_with_indent, sample_batch, setup_wandb, value_color, save_json
from conjecture import AgentLM, Context, sample_conjecture
from proofsearch import make_agent


def now() -> str:
    return '[' + datetime.datetime.now().isoformat() + ']'


FAIL = "fail"


DISTRIBUTED = os.environ.get('DISTRIBUTED', False)


def submit_task(agent_dump: bytes, theory: worker.BackgroundTheory, statement: str):
    if DISTRIBUTED:
        return worker.try_prove.apply_async((agent_dump, theory, statement))
    else:
        return worker.try_prove.run(agent_dump, theory, statement)


def get_task_result(task):
    if DISTRIBUTED:
        return task.get()
    else:
        return task


async def teacher_loop(cfg: DictConfig):
    print('Running in', 'distributed mode.' if DISTRIBUTED else 'single-process mode.')

    agent = make_agent(cfg)

    with open(os.path.join(os.path.dirname(__file__), 'theories', cfg.theory.name + '.p')) as f:
        theory = f.read()

    difficulty_buckets = sorted([list(cfg.difficulty_buckets[i].items())[0]
                                 for i in range(len(cfg.difficulty_buckets))],
                                key=lambda kv: kv[1])

    premises = cfg.theory.premises

    d = peano.PyDerivation()
    d.incorporate(theory)
    proven_conjectures = []
    seen_hindsight_goals = set()
    proofs = []
    outcomes = []

    continue_dir = cfg.get('continue')
    start_iteration = 0

    if continue_dir is not None:
        os.chdir(continue_dir)
        print('Continuing run from', continue_dir)
        # Find largest iteration number such that i.pt exists.
        i = 0
        while os.path.exists(f'{i}.pt'):
            i += 1
        i -= 1
        start_iteration = i
        agent = torch.load(f'{i}.pt')
        print('Loaded agent from', f'{i}.pt')
        # Load examples and outcomes.
        if i > 0:
            with open(f'outcomes_{i-1}.json', 'r') as f:
                outcomes = json.load(f)
                proven_conjectures = [o['problem'] for o in outcomes
                                      if o['hindsight'] is False and
                                         o['proof'] is not None]
                seen_hindsight_goals = {o['problem'] for o in outcomes
                                        if o['hindsight'] and o['proof'] is not None}

        print('Loaded', len(proven_conjectures), 'proven conjectures from previous run.')


    if cfg.get('freeze_conjecturer', False):
        print('Ablation: Freezing conjecturer.')


    with open('log.jsonl', 'w') as log:
        for i in range(start_iteration, cfg.iterations):
            torch.save(agent, f'{i}.pt')

            context = Context(d, None, [])
            # 1- Run conjecturing model to obtain N conjectures.
            print(now(), f'Iteration #{i}: making conjectures...')

            progress_bar = tqdm(total=cfg.n_conjectures)

            conjectures = []

            while len(conjectures) < cfg.n_conjectures:
                proposal = sample_conjecture(AgentLM(agent, 'Conj:(hard) '), context)

                if proposal and proposal not in conjectures + proven_conjectures:
                    # Contract conjectures to make them Peano-parseable.
                    contracted_proposal = d.contract(proposal)
                    if contracted_proposal not in conjectures + proven_conjectures:
                        conjectures.append(contracted_proposal)
                        progress_bar.update(1)

            progress_bar.close()


            print(now(), 'done, have', len(conjectures), 'conjectures')
            print(conjectures)

            log.write(json.dumps({'iteration': i,
                                  'msg': f'It #{i}: posing {len(conjectures)} conjectures.',
                                  'conjectures': conjectures}))
            log.write('\n')
            log.flush()

            # 2- Try to prove each of the conjectures
            tasks = []

            # Dump current agent.
            buff = io.BytesIO()
            torch.save(agent, buff)
            agent_dump = buff.getvalue()

            print('Submitting tasks...')
            for conjecture in tqdm(conjectures, miniters=1):
                tasks.append(submit_task(
                    agent_dump,
                    worker.BackgroundTheory(theory, premises),
                    conjecture))

            # 3- Train model on proofs and outcome of conjectures (easy, hard, timeout)
            examples = []
            student_results = []

            print('Collecting', len(tasks), 'results from workers.')

            for task in tqdm(tasks, miniters=1):
                student_result = get_task_result(task)

                if student_result.error:
                    print('Error in prover process!')
                    print(student_result.error)
                    continue

                student_results.append(student_result)

            success_logprobs = []

            # 3a- Look at all the success logprobs and compute the easy/hard threhsold.
            for student_result in student_results:
                if student_result.success:
                    success_logprobs.append(student_result.logprob)

                outcomes.append({'iteration': i,
                                 'problem': student_result.problem,
                                 'proof': student_result.proof,
                                 'logprob': student_result.logprob,
                                 'actions': student_result.solution_actions,
                                 'hindsight': False
                                 })

                for h in student_result.hindsight_examples:
                    outcomes.append({'iteration': i,
                                     'problem': h.statement,
                                     'proof': h.proof,
                                     'logprob': h.logprob,
                                     'actions': h.solution_actions,
                                     'hindsight': True
                                     })

            if not success_logprobs:
                print(f'No solutions found in iteration {i} - stopping learning loop...')
                break

            thresholds = [np.percentile(success_logprobs, p)
                          for _, p in difficulty_buckets]

            print('Thresholds:',
                  list(zip([k for k, _ in difficulty_buckets], thresholds)),
                  'min =', np.min(success_logprobs),
                  'max =', np.max(success_logprobs))

            # 3b- Classify problems into easy/hard.
            for student_result in student_results:
                # Outcome is the name of the first difficulty bucket that is larger than the logprob.
                if student_result.success:
                    outcome = next(k
                                   for i, (k, _) in enumerate(difficulty_buckets)
                                   if (student_result.logprob <= thresholds[i] or
                                       i + 1 == len(difficulty_buckets)))
                else:
                    outcome = FAIL

                if not cfg.get('freeze_conjecturer', False):
                    examples.append(f'Conj:({outcome}) ' + d.elaborate(student_result.problem))

                if student_result.success:
                    proven_conjectures.append(student_result.problem)
                    proofs.append(student_result.proof)

                examples.extend(student_result.extracted_examples)

                if cfg.train_policy_on_hindsight_examples:
                    for h in student_result.hindsight_examples:
                        if h.goal not in seen_hindsight_goals:
                            outcome = next(k
                                           for i, (k, _) in enumerate(difficulty_buckets)
                                           if h.logprob <= thresholds[i] or i + 1 == len(difficulty_buckets))

                            if not cfg.get('freeze_conjecturer', False):
                                examples.append(f'Conj:({outcome}) ' + d.elaborate(student_result.problem))
                            examples.extend(h.examples)
                            seen_hindsight_goals.add(h.goal)

            log.write(json.dumps({'iteration': i,
                                  'msg': f'Training on {len(examples)} examples.'}))
            log.write('\n')

            # 3c- Train model on conjecturing and proof search examples.
            if i + 1 < cfg.iterations:
                print(len(examples), 'accumulated training examples.')
                agent.train(examples)

            save_json(examples, f'examples_{i}.json')
            save_json(outcomes, f'outcomes_{i}.json')
            torch.save(student_results, f'results_{i}.json')


@hydra.main(version_base="1.2", config_path="config", config_name="bootstrap")
def main(cfg: DictConfig):
    print('Running from:', os.getcwd())
    setup_wandb(cfg)
    if cfg.task == 'teacher':
        asyncio.run(teacher_loop(cfg))

if __name__ == '__main__':
    main()

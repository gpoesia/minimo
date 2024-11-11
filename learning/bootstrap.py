#!/usr/bin/env python3

"""Implements the conjecture-prove bootstrapping learning loop."""

import asyncio
import os
import io
import json
import datetime
import random

import hydra
import logging
from omegaconf import DictConfig, OmegaConf
import torch
import numpy as np
from tqdm import tqdm

import peano
import worker
from worker import StudentResult  # noqa
from hindsight import HindsightExample  # noqa
from util import format_blocks_with_indent, sample_batch, setup_mle_logger, value_color, save_json, load_final_goals
from conjecture import AgentLM, Context, sample_conjecture
from proofsearch import make_agent

from mle_logging import MLELogger
from mle_logging import MLELogger

log = logging.getLogger(__name__)

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



async def teacher_loop(cfg: DictConfig, mle_log: MLELogger):
    log.info('Running in %s', 'distributed mode.' if DISTRIBUTED else 'single-process mode.')
    agent = make_agent(cfg, mle_log)

    # load goals from file and format them
    # FIXME(f.srambical): check whether the goal set is correctly formatted (check the first few finetuning examples)
    final_goals_formatted, final_solutions = load_final_goals(os.path.join(os.path.dirname(__file__), '../goals', cfg.goals + '.json'))
    final_goals = ["Conj:(hard) " + g for g in final_goals_formatted]

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
        log.info('Continuing run from %s', continue_dir)
        # Find largest iteration number such that i.pt exists.
        i = 0
        while os.path.exists(f'{i}.pt'):
            i += 1
        i -= 1
        start_iteration = i
        agent = torch.load(f'{i}.pt')
        log.info('Loaded agent from %s', f'{i}.pt')
        # Load examples and outcomes.
        if i > 0:
            with open(f'outcomes_{i-1}.json', 'r') as f:
                outcomes = json.load(f)
                proven_conjectures = [o['problem'] for o in outcomes
                                      if o['hindsight'] is False and
                                         o['proof'] is not None]
                seen_hindsight_goals = {o['problem'] for o in outcomes
                                        if o['hindsight'] and o['proof'] is not None}

        log.info('Loaded %d proven conjectures from previous run.', len(proven_conjectures))


    if cfg.get('freeze_conjecturer', False):
        log.info('Ablation: Freezing conjecturer.')


    with open('log.jsonl', 'w') as log_file:
        for i in range(start_iteration, cfg.agent.policy.total_iterations):
            context = Context(d, None, [])

            # Dump current agent.
            buff = io.BytesIO()
            torch.save(agent, buff)
            agent_dump = buff.getvalue()

            # Check if and how many conjectures out of the final goal set could be proven by current policy
            student_results_final = prove_conjectures(agent_dump, final_goals_formatted, theory, premises)
            success_logprobs_final, outcomes_final = get_log_probs(student_results_final, outcomes, i)
            log.info('Final goals proven: %d out of %d', len(success_logprobs_final), len(final_goals))
            final_goals_proven = len(success_logprobs_final)

            # terminate the learning loop if all final goals are proven
            if len(success_logprobs_final) == len(final_goals):
                log.info('All final goals proven - stopping learning loop...')
                mle_log.update({'num_iterations': i},
                           {'final_goals_proven': final_goals_proven})
                break

            # 1- Run conjecturing model to obtain N conjectures.
            log.info('Iteration #%d: making conjectures...', i)

            progress_bar = tqdm(total=cfg.n_conjectures)

            conjectures = []

            conjectured_final_goals = []
            while len(conjectures) < cfg.n_conjectures:
                proposal = sample_conjecture(AgentLM(agent, 'Conj:(hard) '), context)

                if proposal and proposal not in conjectures + proven_conjectures:
                    conjectures.append(proposal)
                    progress_bar.update(1)
                    if proposal in final_goals_formatted:
                        log.info('Conjectured a final goal: %s in iteration %d', proposal, i)
                        conjectured_final_goals.append(proposal)

            progress_bar.close()

            # Contract conjectures to make them Peano-parseable.
            conjectures = [d.contract(c) for c in conjectures]

            log.info('Done making %d conjectures', len(conjectures))
            log.info('Conjectures: %s', conjectures)

            log_file.write(json.dumps({'iteration': i,
                                  'msg': f'It #{i}: posing {len(conjectures)} conjectures.',
                                  'conjectures': conjectures}))
            log_file.write('\n')
            log_file.flush()

            # 2- Try to prove each of the conjectures
            examples = []
            student_results= prove_conjectures(agent_dump, conjectures, theory, premises)

            # 3- Train model on proofs and outcome of conjectures (easy, hard, timeout)
            # 3a- Look at all the success logprobs and compute the easy/hard threhsold.
            success_logprobs, outcomes = get_log_probs(student_results, outcomes, i)
            
            ratio_proven = len(success_logprobs)/len(conjectures)
            log.info('%d out of %d conjectures proven. ratio = %f', 
                        len(success_logprobs), len(conjectures), ratio_proven)

            if not success_logprobs:
                log.warning('No solutions found in iteration %d - continuing to next iteration...', i)
                continue

            # Add output of proving final goals to the list of proven conjectures
            student_results.extend(student_results_final)
            outcomes.extend(outcomes_final)

            thresholds = [np.percentile(success_logprobs, p)
                          for _, p in difficulty_buckets]


            log.debug('Thresholds: %s, min = %f, max = %f',
                        list(zip([k for k, _ in difficulty_buckets], thresholds)),
                        np.min(success_logprobs),
                        np.max(success_logprobs))

            hard_sol_log_probs = [logprob for logprob in success_logprobs if logprob >= thresholds[0]]
            mean_hard_sol_log_prob = np.mean(hard_sol_log_probs) if hard_sol_log_probs else 0
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

            log_file.write(json.dumps({'iteration': i,
                                  'msg': f'Training on {len(examples)} examples.'}))
            log_file.write('\n')

            # 3c- Train model on conjecturing and proof search examples.
            if i + 1 < cfg.agent.policy.total_iterations:
                print(len(examples), 'accumulated training examples.')
                val_loss = agent.train(examples=examples, final_goals=final_goals, solutions=final_solutions, ratio_proven=ratio_proven, log=log)
                log.update({'num_iterations': i},
                           {'val_loss': val_loss,
                            'final_goals_proven': final_goals_proven,
                            'ratio_proven': ratio_proven,
                            'mean_hard_sol_log_probs': mean_hard_sol_log_prob},
                            extra_obj={'conjectured_final_goals': conjectured_final_goals})

            mle_log.save()
            save_json(outcomes, f'outcomes_{i}.json')

            save_json(examples, f'examples_{i}.json')
            # torch.save(student_results, f'results_{i}.json')


def prove_conjectures(agent_dump, conjectures, theory, premises):
    tasks = []
    log.info('Submitting tasks...')
    for conjecture in tqdm(conjectures, miniters=1):
        tasks.append(submit_task(
            agent_dump,
            worker.BackgroundTheory(theory, premises),
            conjecture))

    student_results = []

    log.info('Collecting %d results from workers.', len(tasks))

    for task in tqdm(tasks, miniters=1):
        student_result = get_task_result(task)

        if student_result.error:
            log.error('Error in prover process!')
            log.error(student_result.error)
            continue

        student_results.append(student_result)
    return student_results


def get_log_probs(student_results, outcomes, i):

    success_logprobs = []

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

    return success_logprobs, outcomes



@hydra.main(version_base="1.2", config_path="config", config_name="bootstrap")
def main(cfg: DictConfig):
    log.info('Running from: %s', os.getcwd())
    
    seed = cfg.seed
    torch.manual_seed(seed)
    random.seed(seed)
    np.random.seed(seed)

    setup_mle_logger(cfg)
    if cfg.task == 'teacher':
        asyncio.run(teacher_loop(cfg))

if __name__ == '__main__':
    main()

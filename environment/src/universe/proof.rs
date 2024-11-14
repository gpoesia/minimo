use std::sync::Arc;
use std::fmt;
use itertools::Itertools;
use crate::universe::{Derivation, Term, Unifier, Context};
use crate::universe::term::{TermParser, parse_term, parse_definition, Rule, Definition, Annotation, Location,
                            is_parameter_name};
use std::iter::once;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use pest::Parser;
use pest::iterators::Pair;
use pest::error::{Error as PestError};


#[derive(Clone, Debug)]
pub struct Proof {
    pub name: String,
    pub prop: Option<Arc<Term>>,
    pub actions: Vec<ProofScriptAction>
}

#[derive(Debug, Clone)]
pub enum ProofError {
    ProofNotFound(String),
    IntroFailed(String, Vec<Arc<Term>>),
    StepFailed(&'static str, Arc<Term>, String, Vec<Arc<Term>>),
    GenericError(String),
    GoalCheckFailed(String, Arc<Term>, Vec<Arc<Term>>),
    GoalMissing(&'static str, Arc<Term>, String, Vec<Arc<Term>>),
    IncompleteProof(&'static str, Derivation)
}

impl Proof {
    pub fn name(&self) -> &String {
        &self.name
    }

    pub fn execute(&self, u: &mut Derivation) -> Result<(), ProofError> {
        if let Some(prop) = &self.prop {
            u.set_goals(vec![prop.clone()]);
            let goal_name = u.context().get_fresh_name(&"goal".to_string());
            u.define_subterms(prop, false, &mut vec![], &mut vec![goal_name]);
        }

        execute_proof_actions(u, &self.actions)
    }
}


fn execute_proof_actions(u: &mut Derivation, actions: &[ProofScriptAction]) -> Result<(), ProofError> {
    let mut proven_goals = vec![];

    for (i, instr) in actions.iter().enumerate() {
        match &instr.action {
            ProofScriptActionType::Halt() => {
                break;
            },
            ProofScriptActionType::Definition(name, def) => {
                u.define(name.clone(), def.clone(), false);
            },
            ProofScriptActionType::Construct { name, type_, value, arrow } => {
                let defs = u.application_results(&arrow, &None, &vec![]);
                let mut found : bool = false;

                for d in defs.iter() {
                    let dtype = d.dtype.eval(u.context());
                    let type_matches = match type_ {
                        None => true,
                        Some(t) => u.context().are_equivalent(t, &dtype),
                    };
                    let value_matches = match (value, &d.value) {
                        (None, _) => true,
                        (Some(t1), Some(t2)) => u.context().are_equivalent(t1, t2),
                        _ => false,
                    };
                    if type_matches && value_matches {
                        match name {
                            None => { u.define(u.context().get_fresh_name(&"_".to_string()), d.clone(), true); }
                            Some(name) => { u.define(name.clone(), d.clone(), true); }
                        }

                        found = true;

                        let goals = &u.context().goals;

                        if goals.len() > proven_goals.len() && u.context().are_equivalent(&dtype, &goals[proven_goals.len()]) {
                            proven_goals.push(dtype);
                        }

                        break;
                    }
                }

                if !found {
                    return Err(ProofError::StepFailed(
                        &"construct",
                        match &value { Some(v) => v.clone(), None => type_.clone().unwrap() },
                        arrow.clone(),
                        defs.iter().map(|d| (if d.is_prop(u.context()) { d.dtype.clone() }
                                             else { d.value.clone().unwrap() })).collect()
                    ))
                }
            },
            ProofScriptActionType::Intro(name, dtype) => {
                match execute_intro(u, name) {
                    Ok(g) => {
                        match g {
                            Some((_, actual_dtype, new_goal)) => {
                                if !u.context().are_equivalent(dtype, &actual_dtype) {
                                    return Err(ProofError::GenericError(
                                        format!("introduced variable has type {}, not {}", actual_dtype, dtype),
                                    ));
                                }
                                u.set_goals(vec![new_goal]);
                            }
                            None => { u.set_goals(vec![]); }
                        }
                    },
                    Err(e) => { return Err(e); }
                }
            },
            ProofScriptActionType::CheckGoal(goal) => {
                let goals = &u.context().goals.clone();

                if goals.len() != 1 {
                    return Err(ProofError::GoalCheckFailed(
                        format!("{} open proof goals.", goals.len()),
                        goal.clone(),
                        goals.clone(),
                    ));
                }

                if !u.context().are_equivalent(&goals[0], goal) {
                    // FIXME(gpoesia): test for alpha-equivalence.
                    return Err(ProofError::GoalCheckFailed(
                        "Expected and actual proof goal differ.".to_string(),
                        goal.clone(),
                        goals.clone(),
                    ));
                }
            },
            ProofScriptActionType::Apply(name) => {
                let ctx = u.context();
                let goals = &ctx.goals;

                if goals.len() != 1 {
                    return Err(ProofError::GenericError(format!("can only apply on a single goal.")));
                }

                match u.context().lookup(&name) {
                    None => { return Err(ProofError::GenericError(format!("No arrow {} to apply", name))) }
                    Some(def) => {
                        match def.dtype.as_ref() {
                            Term::Arrow { input_types: it, output_type: ot } => {
                                let goal = &goals[0];
                                let unifiers = ot.ndunify(goal, &mut ctx.clone());

                                let mut goals_options = vec![];

                                if unifiers.is_empty() {
                                    return Err(ProofError::GenericError(
                                            format!("Could not unify:\nOutput type:{}\nGoal:{}", ot, goal)))
                                }

                                for u in unifiers.iter() {
                                    enumerate_apply_goals(ctx, u, it, &vec![], 0, &mut vec![], &mut goals_options);
                                }

                                // 1- Collect the vector of goals in the next actions
                                let mut chosen_goals = vec![];
                                for a in actions[i+1..].iter() {
                                    match &a.action {
                                        ProofScriptActionType::ProveGoal(subgoal, _) => chosen_goals.push(subgoal.clone()),
                                        _ => { return Err(ProofError::GenericError(
                                            format!("You can only have goal {{ }} blocks after an apply."))) }
                                    }
                                }

                                // 2- Find that vector in goals_options.
                                let mut found = false;
                                for option in goals_options.iter() {
                                    // NOTE: This is equivalent to iter::eq_by, but that is still in nightly.
                                    if option.len() == chosen_goals.len() &&
                                        option.iter().zip(chosen_goals.iter())
                                                     .map(|(g1, g2)| ctx.are_equivalent(g1, g2)).all(|b| b) {
                                        found = true;
                                        break;
                                    }
                                }

                                // 3- If not found, ProofError
                                if !found {
                                    return Err(ProofError::GenericError(
                                        format!("Did not find chosen goals after apply. Candidates: {}",
                                                goals_options.iter().map(|x| x.iter().map(|y| y.to_string()).join(" | ")).join(", ")
                                    )));
                                }

                                // 4- If found, set that as the goal and continue.
                                u.set_goals(chosen_goals);
                            },
                            _ => {
                                return Err(ProofError::GenericError(format!("{} is not an arrow.", name)))
                            },
                        }
                    }
                }
            },
            ProofScriptActionType::ProveGoal(subgoal, subproof) => {
                let mut sub_u = u.clone();
                sub_u.set_goals(vec![subgoal.clone()]);
                let goal_name = sub_u.context().get_fresh_name(&"goal".to_string());
                sub_u.define_subterms(subgoal, false, &mut vec![], &mut vec![goal_name]);

                match execute_proof_actions(&mut sub_u, &subproof) {
                    Ok(_) => { proven_goals.push(subgoal.clone()); },
                    Err(e) => { return Err(ProofError::GenericError(format!("subgoal {}: {}", subgoal, e))) }
                }
            },
            ProofScriptActionType::Have(subgoal, subproof) => {
                let mut sub_u = u.clone();
                sub_u.set_goals(vec![subgoal.clone()]);
                let goal_name = sub_u.context().get_fresh_name(&"goal".to_string());
                sub_u.define_subterms(subgoal, false, &mut vec![], &mut vec![goal_name]);

                match execute_proof_actions(&mut sub_u, subproof) {
                    Ok(_) => { u.define(u.context().get_fresh_name(&"_".to_string()), Definition::new_opaque(subgoal.clone()), true); },
                    Err(e) => { return Err(ProofError::GenericError(format!("have {}: {}", subgoal, e))) }
                }
            }
        }
    }

    // If there are unproven goals.
    let final_goals = &u.context().goals;
    if final_goals.len() > proven_goals.len() {
        Err(ProofError::IncompleteProof("Proof goal is still open", u.clone()))
    } else {
        Ok(())
    }
}

fn execute_intro(u: &mut Derivation, name: &String) -> Result<Option<(String, Arc<Term>, Arc<Term>)>, ProofError> {
    if u.context().goals.len() != 1 {
        return Err(ProofError::IntroFailed(
            "Can only intro when there's a single goal.".to_string(),
            u.context().goals.clone(),
        ));
    }

    let goal = &u.context().goals[0];

    if let Term::Arrow { input_types, output_type } = goal.eval(u.context()).as_ref() {
        // NOTE(gpoesia): This can be generalized: intro could work out of order.
        let name = u.context().get_fresh_name(name);
        let name_atom = Term::Atom { name: name.clone() }.rc();

        // 1- Add new definition to context
        let (pname, dtype) = match input_types[0].as_ref() {
            Term::Declaration { name, dtype } => (Some(name.clone()), dtype.clone()),
            _ => (None, input_types[0].clone()),
        };

        u.define(name.clone(), Definition { dtype: dtype.clone(), value: None, location: None }, false);

        // 2- Make new goal:
        // 2a- Remove first input
        let mut new_input_types : Vec<Arc<Term>> = input_types[1..].to_vec();
        let mut new_output_type = output_type.clone();

        // 2b- Substitute new name in others
        if let Some(pname) = pname {
            for it in new_input_types.iter_mut() {
                *it = it.replace(&pname, &name_atom);
            }
            new_output_type = new_output_type.replace(&pname, &name_atom);
        }

        // 2c- Change goal.
        let new_goal_is_arrow = !new_input_types.is_empty();

        if new_goal_is_arrow {
            Ok(Some((name, dtype, Term::Arrow {
                input_types: new_input_types,
                output_type: new_output_type,
            }.rc())))
        } else {
            // NOTE: This should probably be done every time the goal changes,
            // for all closed subterms.
            let goal_name = u.context().get_fresh_name(&"goal".to_string());
            u.define_subterms(&new_output_type, false, &mut vec![], &mut vec![goal_name]);

            // New goal was closed.
            if u.inhabited(&new_output_type).is_some() {
                Ok(None)
            } else {
                Ok(Some((name, dtype, new_output_type)))
            }
        }
    } else {
        Err(ProofError::IntroFailed(
            "Can only intro when the goal is an arrow.".to_string(),
            vec![goal.clone()],
        ))
    }
}

fn enumerate_apply_goals(context: &Context,
                         unifier: &Unifier,
                         input_types: &Vec<Arc<Term>>,
                         must_infer: &Vec<bool>,
                         current_index: usize,
                         current_goals: &mut Vec<Arc<Term>>,
                         result: &mut Vec<Vec<Arc<Term>>>) {

    if current_index == input_types.len() {
        result.push(current_goals.clone());
        return;
    }

    let next_input = &input_types[current_index];

    match next_input.as_ref() {
        Term::Declaration { name, dtype } => {
            if let Some(_) = unifier.get(name) {
                enumerate_apply_goals(context, unifier, input_types, must_infer, current_index + 1, current_goals, result);
            } else {
                // `name` is not bound to anything yet;
                // we need to find suitable options for filling in this parameter of type dtype.
                let mut u = unifier.clone();

                let dtype = dtype.apply_unifier(unifier);

                for cname in context.inhabitants(&dtype).drain(0..) {
                    u.insert(name.clone(), Term::Atom { name: cname }.rc());

                    enumerate_apply_goals(context, &u, input_types, must_infer,
                                          current_index + 1, current_goals, result);
                }
            }
        },
        _ => {
            let goal = next_input.apply_unifier(unifier).eval(context);

            if goal.free_variables().len() > 0 {
                return;
            }

            let is_goal_open = context.inhabitant(&goal).is_none();

            if is_goal_open {
                // If action annotation says this goal must be inferred and it wasn't, cut this branch.
                if *must_infer.get(current_index).unwrap_or(&false) {
                    return;
                }

                current_goals.push(goal);
            }

            enumerate_apply_goals(context, unifier, input_types, must_infer, current_index + 1, current_goals, result);

            if is_goal_open {
                current_goals.pop();
            }
        }
    }
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ProofScriptAction {
    action : ProofScriptActionType,
    location : Option<Location>
}

#[derive(Debug, Clone)]
pub enum ProofScriptActionType {
    Definition(String, Definition),
    Construct { name: Option<String>, type_: Option<Arc<Term>>, value: Option<Arc<Term>>, arrow: String },
    Apply(String),
    Intro(String, Arc<Term>),
    CheckGoal(Arc<Term>),
    ProveGoal(Arc<Term>, Vec<ProofScriptAction>),
    Have(Arc<Term>, Vec<ProofScriptAction>),
    Halt(),
}

pub(super) fn parse_proof(pair: Pair<Rule>) -> Proof {
    let rule = pair.as_rule();
    let mut sub : Vec<Pair<Rule>> = pair.into_inner().collect();

    assert!(rule == Rule::verify || rule == Rule::proof);
    assert!(sub.len() >= 2);

    let name = sub[0].as_str();

    if sub.len() == 2 {
        // Verify block (proof without a goal).
        let actions = sub.remove(1).into_inner().map(parse_proof_action).collect();
        Proof { name: String::from(name), prop: None, actions }
    } else {
        // Regular proof block.
        assert_eq!(sub.len(), 3);
        let prop = parse_term(sub.remove(1), &mut HashMap::new());
        let actions = sub.remove(1).into_inner()
                                   .filter(|x| !matches!(x.as_rule(), Rule::using))
                                   .map(parse_proof_action).collect();
        Proof { name: String::from(name), prop: Some(prop), actions }
    }
}

fn parse_proof_action(pair: Pair<Rule>) -> ProofScriptAction {
    let rule = pair.as_rule();
    let span = pair.as_span();
    let line = span.start_pos().line_col().0;
    let mut sub : Vec<Pair<Rule>> = pair.into_inner().collect();
    let action_type = match rule {
        Rule::construct => {
            let name = sub[0].as_str().to_string();
            let type_ = parse_term(sub.remove(1), &mut HashMap::new());
            let value = parse_term(sub.remove(1), &mut HashMap::new());
            let arrow = sub[1].as_str().to_string();
            ProofScriptActionType::Construct{ name: Some(name), type_: Some(type_),
                                          value: Some(value), arrow }
        },
        Rule::halt => {
            ProofScriptActionType::Halt()
        },
        Rule::show => {
            let ttype = parse_term(sub.remove(0), &mut HashMap::new());
            let arrow = sub[0].as_str();
            ProofScriptActionType::Construct{ name: None, type_: Some(ttype), value: None, arrow: arrow.to_string() }
        },
        Rule::apply => {
            ProofScriptActionType::Apply(String::from(sub[0].as_str()))
        },
        Rule::intro => {
            ProofScriptActionType::Intro(String::from(sub[0].as_str()),
                               parse_term(sub.remove(1), &mut HashMap::new()))
        },
        Rule::check_goal => {
            ProofScriptActionType::CheckGoal(parse_term(sub.remove(0), &mut HashMap::new()))
        },
        Rule::prove_goal => {
            let goal_term = parse_term(sub.remove(0), &mut HashMap::new());
            let actions = sub.remove(0).into_inner().map(parse_proof_action).collect();
            ProofScriptActionType::ProveGoal(goal_term, actions)
        },
        Rule::have => {
            let goal_term = parse_term(sub.remove(0), &mut HashMap::new());
            let actions = sub.remove(0).into_inner().map(parse_proof_action).collect();
            ProofScriptActionType::Have(goal_term, actions)
        },
        Rule::definition => {
            let (name, def) = parse_definition(sub);
            ProofScriptActionType::Definition(name, def)
        },
        _ => unreachable!("Unhandled rule {:?}", rule)
    };
    let loc = Location { line_number: Some(line), file_name: None};
    ProofScriptAction { action : action_type, location : Some(loc)}
}

impl fmt::Display for ProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofError::ProofNotFound(name) => write!(f,
                                                      "Proof '{}' not found.",
                                                      name),
            ProofError::StepFailed(step_type, target_term, action, action_results) => {
                write!(f, "'{}' step failed: action {} did not {} {}\nAction {}ed {} results:",
                       step_type, action, step_type, target_term, step_type, action_results.len()
                )?;

                for (i, t) in action_results.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", t)?;
                }

                Ok(())
            },

            ProofError::IntroFailed(errors, goals) => {
                write!(f, "intro step failed: {}\nProof goals:", errors)?;

                for (i, t) in goals.iter().enumerate() {
                    write!(f, "{}- {}", i, t)?;
                }

                Ok(())
            },

            ProofError::GoalCheckFailed(message, expected, actual) => {
                write!(f, "check_goal step failed: {}\nExpected: {}\nActual open proof goals:",
                      message, expected)?;

                for (i, t) in actual.iter().enumerate() {
                    write!(f, "{}- {}", i, t)?;
                }

                Ok(())
            },

            ProofError::GenericError(message) => {
                write!(f, "proof error: {}", message)?;
                Ok(())
            },

            ProofError::IncompleteProof(message, u) => {
                write!(f, "{}: {}", message, u.context().goals[0])?;
                Ok(())
            },

            _ => panic!(),
        }
    }
}

#[derive(Clone, Eq)]
pub enum ProofAction {
    // Hypothetical step.
    Intro,

    // Forward steps.
    Construct(String),
    SelectConstruction(bool, Arc<Term>, Arc<Term>),

    // Backward steps.
    Apply(String),
    SelectGoals(Vec<Arc<Term>>),
}

impl PartialEq for ProofAction {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ProofAction::Intro, ProofAction::Intro) => true,
            (ProofAction::Construct(a), ProofAction::Construct(b)) => a == b,

            // Assume proof irrelevance for actions.
            (ProofAction::SelectConstruction(true, dtype, _),
             ProofAction::SelectConstruction(true, dtype2, _)) => dtype == dtype2,
            (ProofAction::SelectConstruction(false, _, value),
             ProofAction::SelectConstruction(false, _, value2)) => value == value2,

            (ProofAction::Apply(a), ProofAction::Apply(b)) => a == b,
            (ProofAction::SelectGoals(a), ProofAction::SelectGoals(b)) => a == b,
            _ => false,
        }
    }
}

impl Hash for ProofAction {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            ProofAction::Intro => { 0.hash(state); },
            ProofAction::Construct(a) => { 1.hash(state); a.hash(state); },
            ProofAction::SelectConstruction(dtype_is_prop, dtype, value) => {
                2.hash(state);
                dtype_is_prop.hash(state);
                if *dtype_is_prop { dtype.hash(state) } else { value.hash(state) };
            },
            ProofAction::Apply(a) => { 3.hash(state); a.hash(state); },
            ProofAction::SelectGoals(gs) => { 4.hash(state); gs.hash(state); },
        }
    }
}


impl fmt::Display for ProofAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            ProofAction::Intro => write!(f, "intro."),
            ProofAction::Construct(a) => write!(f, "c {}", a),
            ProofAction::SelectConstruction(dtype_is_prop, dtype, value)
                => write!(f, "=> {}.", if *dtype_is_prop { dtype } else { value }),
            ProofAction::Apply(a) => write!(f, "a {}", a),
            ProofAction::SelectGoals(gs) => write!(f, "=> {}.", gs.iter().map(|g| g.to_string()).join("; ")),
        }
    }
}

#[derive(Clone)]
pub struct ProofState {
    pub derivation: Derivation,
    history: Vec<ProofAction>,
    construction_history: Vec<Option<String>>,
    // Objects that can be used in the proof.
    premises: Vec<String>,
}

impl ProofState {
    pub fn new(premises: Vec<String>, goal: Arc<Term>) -> ProofState {
        let mut d = Derivation::new();
        d.set_goals(vec![goal]);

        ProofState {
            derivation: d,
            history: vec![],
            construction_history: vec![],
            premises,
        }
    }

    pub fn premises(&self) -> &Vec<String> {
        &self.premises
    }

    pub fn load(self: &mut ProofState, theory: &str) -> Result<(), String> {
        match theory.parse::<Context>() {
            Ok(ctx) => {
                self.derivation.incorporate(&ctx);
                for g in self.derivation.context_.goals.clone().iter() {
                    let goal_name = self.derivation.context_.get_fresh_name(&"goal".to_string());
                    self.derivation.define_subterms(g, false, &mut vec![], &mut vec![goal_name]);
                }
                Ok(())
            },
            Err(e) => { Err(format!("Parse error: {}", e)) },
        }
    }

    pub fn actions(&self) -> Vec<ProofAction> {
        if let Some(action) = self.history.last() {
            match &action {
                // Backward step: unify conclusion with the goal.
                ProofAction::Apply(arrow) => {
                    match self.derivation.context().lookup(&arrow) {
                        None => { vec![] },
                        Some(def) => {
                            match def.dtype.as_ref() {
                                Term::Arrow { input_types: it, output_type: ot } => {
                                    let goal = self.goal();
                                    let unifiers = ot.ndunify(&goal, &mut self.derivation.context().clone());

                                    let mut goals_options = vec![];
                                    let must_infer = match self.derivation.context().lookup_backward_annotation(&arrow) {
                                        Some(Annotation::BackwardAction { arrow: _, must_infer }) => must_infer,
                                        _ => vec![],
                                    };

                                    for u in unifiers.iter() {
                                        enumerate_apply_goals(self.derivation.context(), u, it, &must_infer,
                                                            0, &mut vec![], &mut goals_options);
                                    }

                                    goals_options.drain(0..).map(|gs| { ProofAction::SelectGoals(gs) }).collect()
                                },
                                _ => vec![]
                            }
                        }
                    }
                },
                // Forward step:
                ProofAction::Construct(arrow) => {
                    let preconditions = match self.derivation.context().lookup_forward_annotation(&arrow) {
                        Some(Annotation::ForwardAction { arrow: _, preconditions }) => preconditions,
                        _ => vec![],
                    };

                    let mut defs = self.derivation.application_results_with_preconditions(&arrow, &None, &preconditions, &vec![]);
                    defs.drain(0..).filter_map(|d| {
                        if !self.derivation.is_redundant(&d.dtype, &d.value) {
                            Some(ProofAction::SelectConstruction(
                                d.dtype.is_prop(self.derivation.context()),
                                d.dtype,
                                d.value.unwrap()))
                        } else {
                            None
                        }
                    }).collect()
                },
                _ => {
                    let mut actions = vec![];

                    let g = self.goal();

                    if g.is_arrow(self.derivation.context()) {
                        actions.push(ProofAction::Intro);
                    }

                    for p in &self.premises {
                        let mut found_annotations = false;

                        if self.derivation.context().lookup_forward_annotation(&p).is_some() {
                            actions.push(ProofAction::Construct(p.clone()));
                            found_annotations = true;
                        }

                        if self.derivation.context().lookup_backward_annotation(&p).is_some() {
                            actions.push(ProofAction::Apply(p.clone()));
                            found_annotations = true;
                        }

                        // If no annotations, let use action backwards.
                        if !found_annotations {
                            actions.push(ProofAction::Apply(p.clone()));
                            actions.push(ProofAction::Construct(p.clone()));
                        }
                    }

                    actions
                }
            }
        } else {
            {
                let mut actions = vec![];

                let g = self.goal();

                if g.is_arrow(self.derivation.context()) {
                    actions.push(ProofAction::Intro);
                }

                for p in &self.premises {
                    let mut found_annotations = false;

                    if self.derivation.context().lookup_forward_annotation(&p).is_some() {
                        actions.push(ProofAction::Construct(p.clone()));
                        found_annotations = true;
                    }

                    if self.derivation.context().lookup_backward_annotation(&p).is_some() {
                        actions.push(ProofAction::Apply(p.clone()));
                        found_annotations = true;
                    }

                    // If no annotations, let use action backwards.
                    if !found_annotations {
                        actions.push(ProofAction::Apply(p.clone()));
                        actions.push(ProofAction::Construct(p.clone()));
                    }
                }

                actions
            }
        }
    }

    pub fn goal(&self) -> Arc<Term> {
        let gs = &self.derivation.context().goals;
        assert!(gs.len() == 1, "Invariant violated: each ProofState should have a single goal.");
        gs[0].clone()
    }

    pub fn set_goal(&mut self, new_goal: Arc<Term>) {
        self.derivation.context_.set_goals(vec![new_goal]);
    }

    pub fn execute_action(&self, action: &ProofAction) -> Vec<ProofState> {
        let mut ps = self.clone();
        ps.history.push(action.clone());

        match action {
            ProofAction::Intro => {
                match execute_intro(&mut ps.derivation, &"x".to_string()) {
                    Ok(Some((name, dtype, g))) => {
                        ps.derivation.set_goals(vec![g]);
                        if dtype.is_arrow(&ps.derivation.context_) {
                            ps.premises.push(name.clone());
                        }
                        ps.construction_history.push(Some(name));
                        vec![ps]
                    },
                    Ok(None) => vec![],
                    Err(e) => panic!("Precondition to intro violated: {}", e),
                }
            },
            ProofAction::Apply(_) => { ps.construction_history.push(None); vec![ps] },
            ProofAction::Construct(_) => { ps.construction_history.push(None); vec![ps] },

            ProofAction::SelectGoals(goals) => {
                goals.iter().map(|g| {
                    let mut ps_g = ps.clone();
                    ps_g.construction_history.push(None);
                    ps_g.derivation.set_goals(vec![g.clone()]);
                    let goal_name = ps_g.derivation.context().get_fresh_name(&"goal".to_string());
                    ps_g.derivation.define_subterms(&g, false, &mut vec![], &mut vec![goal_name]);
                    ps_g
                }).collect()
            },
            ProofAction::SelectConstruction(_dtype_is_prop, dtype, value) => {
                if let Some(g) = self.derivation.context().goals.get(0) {
                    if self.derivation.context().are_equivalent(&dtype, g) {
                        // Construction closes the goal.
                        return vec![];
                    }
                }

                let name = ps.derivation.context().get_fresh_name(&"p".to_string());
                ps.derivation.define(name.clone(),
                                     Definition::new_concrete(dtype.clone(), value.clone()),
                                     false);

                if dtype.is_arrow(&ps.derivation.context()) {
                    ps.premises.push(name.clone());
                }

                ps.construction_history.push(Some(name));

                vec![ps]
            },
        }
    }

    pub fn generating_arguments(&self, name: &String) -> Option<Vec<String>> {
        if let Some(def) = self.derivation.lookup(name) {
            if let Some(v) = &def.value {
                if let Term::Application { function, arguments } = v.as_ref() {
                    return Some(once(function).chain(arguments.iter()).map(|v| v.to_string()).collect());
                }
            }
        }
        None
    }

    pub fn is_context_empty(&self) -> bool {
        let ctx = self.derivation.context();
        for name in ctx.insertion_order.iter() {
            if (name.starts_with('x') || name.starts_with('p')) && !name.contains("@") && !ctx.is_intrinsic_name(name) {
                return false;
            }
        }

        true
    }

    pub fn format_context(&self) -> String {
        let mut s = String::from("{ ");
        let mut first = true;

        let ctx = self.derivation.context();

        for name in ctx.insertion_order.iter() {
            if (name.starts_with('x') || name.starts_with('p')) && !name.contains("@") && !ctx.is_intrinsic_name(name) {
                let def = ctx.lookup(name).unwrap();

                if !first {
                    s.push_str(", ");
                }

                s.push_str(&format!("{} : {}", name, def.dtype));

                if !def.is_prop(ctx) {
                    if let Some(v) = &def.value {
                        s.push_str(&format!("= {}", v));
                    }
                }

                first = false;
            }
        }

        s.push_str(" }");

        s
    }

    pub fn names_in_context(&self) -> Vec<String> {
        let ctx = self.derivation.context();
        let mut names = vec![];

        for name in ctx.insertion_order.iter() {
            if (name.starts_with('x') || name.starts_with('p')) && !name.contains("@") {
                names.push(name.clone());
            }
        }

        names
    }

    pub fn format_goal(&self) -> String {
        self.goal().to_string()
    }

    pub fn format_action_prefix(&self) -> String {
        if let Some(action) = self.history.last() {
            match action {
                ProofAction::Apply(a) => format!("apply {}", a),
                ProofAction::Construct(a) => format!("construct {}", a),
                _ => String::new(),
            }
        } else {
            String::new()
        }
    }

    pub fn last_prop_constructed(&self) -> Option<String> {
        if let Some(action) = self.history.last() {
            match &action {
                ProofAction::SelectConstruction(true, _, dtype) => Some(dtype.to_string()),
                _ => None,
            }
        } else {
            None
        }
    }

    pub fn construction_from_last_action(&self) -> Option<String> {
        match self.construction_history.last() {
            Some(v) => v.clone(),
            _ => None,
        }
    }

    pub fn construction_history(&self) -> &Vec<Option<String>> {
        &self.construction_history
    }

    pub fn lookup(&self, name: &String) -> Option<&Definition> {
        self.derivation.lookup(name)
    }
}

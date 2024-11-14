use std::collections::{HashSet};
use pyo3::prelude::*;
use pyo3::exceptions::PyValueError;
use pyo3::Python;
use crate::universe::{Context, Derivation, Definition, Term, ProofState, ProofAction};

#[pyclass]
struct PyDerivation {
    pub universe: Derivation,
}

#[pyclass]
struct PyDefinition {
    pub def: Definition,
    pub action: String,
}

#[pymethods]
impl PyDefinition {
    pub fn __str__(&self) -> String {
        format!(
            "{} : {}",
            match &self.def.value {
                None => String::from("_"),
                Some(v) => v.to_string()
            },
            self.def.dtype.to_string()
        )
    }

    pub fn generating_action(&self) -> &str {
        &self.action
    }

    pub fn generating_arguments(&self) -> Option<Vec<String>> {
        match &self.def.value {
            Some(v) => match v.as_ref() {
                Term::Application { function: _, arguments } => {
                    Some(arguments.iter().map(|v| v.to_string()).collect())
                },
                _ => None,
            },
            None => None,
        }
    }

    pub fn dependencies(&self) -> Vec<String> {
        match &self.def.value {
            Some(v) => v.free_atoms().iter().map(|v| v.clone()).collect(),
            None => vec![],
        }
    }

    pub fn clean_dtype(&self, u: &PyDerivation) -> String {
        self.def.dtype.in_context(&u.universe.context()).to_string()
    }

    pub fn __repr__(&self) -> String {
        self.__str__()
    }

    pub fn get_type(&self) -> String {
        self.def.dtype.to_string()
    }

    pub fn get_value(&self) -> Option<String> {
        self.def.value.as_ref().map(|v| v.to_string())
    }
}

#[pymethods]
impl PyDerivation {
    #[new]
    pub fn new() -> PyDerivation {
        PyDerivation {
            universe: Derivation::new()
        }
    }

    pub fn actions(&self) -> Vec<String> {
        self.universe.actions().map(|a| a.clone()).collect()
    }

    pub fn apply(&self, action: String, scope: Option<Vec<String>>,
                 predetermined: Option<Vec<Option<String>>>) -> Vec<PyDefinition> {
        self.universe.application_results(&action, &scope.map(|v| v.into_iter().collect()),
                                          &(predetermined.unwrap_or(vec![])))
            .into_iter().map(|d| PyDefinition { def: d, action: action.clone() }).collect()
    }

    pub fn next_id(&mut self) -> usize {
        self.universe.next_term_id()
    }

    pub fn peek_next_id(&self) -> usize {
        self.universe.peek_next_term_id()
    }

    pub fn fast_forward_next_id(&mut self, i: usize) {
        self.universe.fast_forward_next_term_id(i)
    }

    pub fn apply_with(&self, action: String, param_name: String) -> Vec<PyDefinition> {
        self.universe.apply_with(&action, &param_name)
            .into_iter().map(|d| PyDefinition { def: d, action: action.clone() }).collect()
    }

    pub fn define(&mut self, name: String, d: &PyDefinition) -> Vec<String> {
        self.universe.define(name, d.def.clone(), false)
    }

    pub fn lookup(&self, name: String) -> Option<PyDefinition> {
        match self.universe.lookup(&name) {
            None => None,
            Some(def) => Some(PyDefinition { def: def.clone(), action: String::new() })
        }
    }

    pub fn elaborate(&self, term: String) -> PyResult<String> {
        match term.parse::<Term>() {
            Ok(t) => Ok(t.rc().elaborate(&self.universe.context()).to_string()),
            Err(e) => Err(PyValueError::new_err(format!("Failed to parse term: {}", e)))
        }
    }

    pub fn contract(&self, term: String) -> PyResult<String> {
        match term.parse::<Term>() {
            Ok(t) => Ok(t.rc().contract().to_string()),
            Err(e) => Err(PyValueError::new_err(format!("Failed to parse term: {}", e)))
        }
    }

    pub fn is_prop(&self, d: &PyDefinition) -> bool {
        d.def.is_prop(&self.universe.context_)
    }

    pub fn incorporate(&mut self, context: &str) -> PyResult<bool> {
        match context.parse() {
            Ok(context) => {
                self.universe.incorporate(&context);
                Ok(true)
            },
            Err(e) => Err(PyValueError::new_err(format!("Failed to parse context: {}", e)))
        }
    }

    pub fn clone(&self) -> PyDerivation {
        PyDerivation {
            universe: self.universe.clone(),
        }
    }

    pub fn state(&self, ignore: Option<HashSet<String>>) -> Vec<(String, String, Option<String>, bool, Vec<String>)> {
        let mut s = Vec::new();

        for name in self.universe.context_.insertion_order.iter() {
            if ignore.as_ref().map_or(false, |s| s.contains(name)) {
                continue;
            }

            let def = self.universe.context_.lookup(name).unwrap();

            let dependencies = match &def.value {
                Some(v) => v.free_atoms().iter().map(|v| v.clone()).collect(),
                None => vec![],
            };

            s.push((name.clone(),
                    def.dtype.to_string(),
                    def.value.as_ref().map(|v| v.to_string()),
                    def.is_prop(&self.universe.context_),
                    dependencies));
        }

        s
    }

    pub fn value_of(&self, def: &PyDefinition) -> String {
        value_of(&def.def, &self.universe.context_)
    }

    pub fn arrow_type_signature(&self, name: String) -> Option<(Vec<(String, String)>, String)> {
        if let Some(def) = self.universe.context().lookup(&name) {
            if let Term::Arrow { input_types, output_type } = def.dtype.as_ref() {
                return Some((input_types.iter().map(|t| match t.as_ref() {
                    Term::Declaration { name, dtype } => (name.to_string(), dtype.to_string()),
                    _ => (String::new(), t.to_string())
                }).collect(),
                output_type.to_string()))
            }
        }
        None
    }

    pub fn declared_atoms_with_type(&self, target: String) -> PyResult<Vec<String>> {
        match target.parse::<Term>() {
            Ok(target) => {
                let target = target.rc();

                Ok(self.universe.context().insertion_order.iter().filter_map(|name| {
                    if !name.contains('@') {
                        let def = self.universe.context().lookup(name).unwrap();
                        if self.universe.context().are_equivalent(&target, &def.dtype) {
                            return Some(match &def.value {
                                Some(v) => v.to_string(),
                                None => name.clone(),
                            });
                        }
                    }
                    None
                }).collect())
            },
            Err(e) => Err(PyValueError::new_err(format!("Error parsing type: {}", e)))
        }

    }

    pub fn arrows_with_target_type(&self, target: String) -> PyResult<Vec<String>> {
        match target.parse::<Term>() {
            Ok(target) => {
                let target = target.rc();

                Ok(self.universe.context().insertion_order.iter().filter_map(|name| {
                    if !name.contains('@') {
                        let def = self.universe.context().lookup(name).unwrap();

                        match def.dtype.as_ref() {
                            Term::Arrow { input_types: _, output_type } if output_type == &target =>
                                Some(name.clone()),
                            _ => None,
                        }
                    } else {
                        None
                    }
                }).collect())
            },
            Err(e) => Err(PyValueError::new_err(format!("Error parsing type: {}", e)))
        }

    }
}

fn value_of(def: &Definition, ctx: &Context) -> String {
    if def.is_prop(ctx) {
        def.dtype.in_context(ctx).to_string()
    } else {
        match &def.value {
            Some(v) => v.in_context(ctx).to_string(),
            None => String::new()
        }
    }
}


#[pyclass]
struct PyProofState {
    pub proof_state: ProofState
}

#[pymethods]
impl PyProofState {
    #[new]
    pub fn new(
        theory: &str,
        premises: Vec<String>,
        goal: &str
    ) -> PyResult<Self> {
        match goal.parse::<Term>() {
            Ok(g) => {
                let mut ps = ProofState::new(premises, g.rc());

                match ps.load(theory) {
                    Err(e) => Err(PyValueError::new_err(format!("Error parsing theory: {}", e))),
                    Ok(_) => Ok(PyProofState { proof_state: ps }),
                }
            },
            Err(e) => Err(PyValueError::new_err(format!("Error parsing goal: {}", e)))
        }
    }

    pub fn premises(&self) -> Vec<String> {
        self.proof_state.premises().to_vec()
    }

    pub fn is_prop(&self, name: String) -> Option<bool> {
        let u = &self.proof_state.derivation;

        if let Some(def) = u.lookup(&name) {
            Some(def.is_prop(&u.context()))
        } else {
            None
        }
    }

    pub fn names_in_context(&self) -> Vec<String> {
        self.proof_state.names_in_context().to_vec()
    }

    pub fn actions(&self) -> Vec<PyProofAction> {
        // Deduplicate the actions first.
        let mut seen = HashSet::new();
        self.proof_state
            .actions()
            .drain(0..)
            .filter_map(|a| {
                if seen.contains(&a) {
                    None
                } else {
                    seen.insert(a.clone());
                    Some(PyProofAction { proof_action: a })
                }
            })
            .collect()
    }

    pub fn clone(&self) -> PyProofState {
        PyProofState { proof_state: self.proof_state.clone() }
    }

    pub fn format_context(&self) -> String {
        self.proof_state.format_context()
    }

    pub fn is_context_empty(&self) -> bool {
        self.proof_state.is_context_empty()
    }

    pub fn format_action_prefix(&self) -> String {
        self.proof_state.format_action_prefix()
    }

    pub fn format_goal(&self) -> String {
        self.proof_state.format_goal()
    }

    pub fn execute_action(&self, a: &PyProofAction) -> Vec<PyProofState> {
        self.proof_state
            .execute_action(&a.proof_action)
            .drain(0..)
            .map(|ps| PyProofState { proof_state: ps })
            .collect()
    }

    pub fn construction_from_last_action(&self) -> Option<String> {
        self.proof_state.construction_from_last_action()
    }

    pub fn last_proven_proposition(&self) -> Option<String> {
        if let Some(name) = self.proof_state.construction_from_last_action() {
            if let Some(def) = self.proof_state.derivation.lookup(&name) {
                if def.is_prop(self.proof_state.derivation.context()) {
                    return Some(def.dtype.to_string())
                }
            }
        }
        None
    }

    pub fn construction_history(&self) -> Vec<Option<String>> {
        self.proof_state.construction_history().clone()
    }

    pub fn generating_arguments(&self, name: String) -> Option<Vec<String>> {
        self.proof_state.generating_arguments(&name)
    }

    pub fn lookup(&self, name: String) -> Option<PyDefinition> {
        match self.proof_state.lookup(&name) {
            None => None,
            Some(def) => Some(PyDefinition { def: def.clone(), action: String::new() })
        }
    }

    pub fn format_object(&self, name: String) -> Option<String> {
        match self.proof_state.lookup(&name) {
            None => None,
            Some(def) => {
                if def.is_prop(self.proof_state.derivation.context()) {
                    Some(def.dtype.to_string())
                } else {
                    match &def.value {
                        None => Some(name),
                        Some(v) => Some(v.to_string()),
                    }
                }
            }
        }
    }

    pub fn goal(&self) -> String {
        self.proof_state.goal().to_string()
    }

    pub fn next_goal_parameter(&self) -> Option<String> {
        match self.proof_state.goal().as_ref() {
            Term::Arrow { input_types, output_type: _ } => {
                match input_types[0].as_ref() {
                    Term::Declaration { name, dtype: _ } => Some(name.clone()),
                    _ => None,
                }
            },
            _ => None,
        }
    }

    pub fn rewrite_goal_conclusion(&mut self,
                                   conclusion: String,
                                   substitutions: Vec<(String, String)>,
                                   inputs_kept: usize) -> PyResult<String> {
        match conclusion.parse::<Term>() {
            Ok(g) => {
                // Ignore inputs from the goal if it's an arrow, only leaving `inputs_kept` inputs.
                let mut new_goal = match self.proof_state.goal().as_ref() {
                    Term::Arrow { input_types, output_type: _ } => {
                        if inputs_kept == 0 {
                            g.rc()
                        } else {
                            // Take the first `inputs_kept` input types and the output type.
                            // This is 1 instead of inputs_kept for a convoluted reason.
                            // The only intent of this method is to be called during hindsight relabeling,
                            // and in hindsight_relabel (in Python) that method keeps track of rewritten
                            // inputs as it traverses the proof path upwards, and it expects that
                            // this method will just handle the very first input that was put in the goal
                            // by an intro action.
                            let kept_inputs = input_types.iter().take(1);
                            match g {
                                // If the new goal is an arrow, concat the input types and keep the new goal output type.
                                Term::Arrow { input_types: g_input_types, output_type: g_output_type } => {
                                    Term::Arrow { input_types: kept_inputs.chain(
                                        g_input_types.iter()).cloned().collect(),
                                                  output_type: g_output_type.rc()
                                    }.rc()
                                },
                                // If the new goal is not an arrow, just rewrite the conclusion.
                                _ => Term::Arrow { input_types: kept_inputs.cloned().collect(), output_type: g.rc() }.rc(),
                            }
                        }
                    },
                    _ => g.rc(),
                };
                for (old, new) in substitutions.iter() {
                    new_goal = new_goal.replace(old, &Term::Atom { name: new.clone() }.rc());
                }

                self.proof_state.set_goal(new_goal);
                Ok(self.goal())
            },
            Err(e) => Err(PyValueError::new_err(format!("Failed to parse new goal {}: {}", conclusion, e))),
        }
    }
}

#[derive(Eq, PartialEq)]
#[pyclass]
struct PyProofAction {
    pub proof_action: ProofAction
}

#[pymethods]
impl PyProofAction {
    pub fn __str__(&self) -> String {
        self.proof_action.to_string()
    }

    pub fn __repr__(&self) -> String {
        self.proof_action.to_string()
    }

    pub fn __eq__(&self, rhs: &PyProofAction) -> bool {
        self.proof_action == rhs.proof_action
    }

    pub fn is_intro(&self) -> bool {
        matches!(self.proof_action, ProofAction::Intro)
    }

    pub fn is_construct(&self) -> bool {
        matches!(self.proof_action, ProofAction::Construct(_))
    }

    pub fn is_apply(&self) -> bool {
        matches!(self.proof_action, ProofAction::Apply(_))
    }

    pub fn selected_construction(&self) -> Option<(String, String)> {
        if let ProofAction::SelectConstruction(_, dtype, value) = &self.proof_action {
            Some((dtype.to_string(), value.to_string()))
        } else {
            None
        }
    }
}

#[pyfunction]
fn unify(t1: String, t2: String) -> PyResult<Vec<(String, String)>> {
    match (t1.parse::<Term>(), t2.parse::<Term>()) {
        (Ok(t1), Ok(t2)) => {
            let mut ctx = Context::new();
            let unifiers = t1.rc().ndunify(&t2.rc(), &mut ctx);
            Ok(match unifiers.get(0) {
                Some(u) => u.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
                None => vec![],
            })
        },
        (Err(e), _) => Err(PyValueError::new_err(e.to_string())),
        (_, Err(e)) => Err(PyValueError::new_err(e.to_string())),
    }
}

#[pymodule]
fn peano(_py: Python<'_>, m: &PyModule) -> PyResult<()> {
    m.add_class::<PyDefinition>()?;
    m.add_class::<PyDerivation>()?;
    m.add_class::<PyProofState>()?;
    m.add_class::<PyProofAction>()?;
    m.add_function(wrap_pyfunction!(unify, m)?)?;
    Ok(())
}

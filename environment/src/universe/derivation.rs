use std::option::Option;
use std::sync::Arc;
use std::collections::hash_set::{HashSet, Iter};
use std::collections::hash_map::HashMap;
use std::io;
use std::path::Path;
use std::iter::{Chain, once};
use std::ops::Add;

use num_rational::Rational64;

use super::universe::{Scope};
use super::term::{Context, Term, Definition, is_parameter_name, is_intrinsic_application, ProofResultNames, Unifier};
use super::proof::{Proof, ProofError};

const REAL_TYPE_CONST: &str = &"real";
const PATH_EXPR_SEPARATOR: &str = "@";
const LOCAL_DEFINITION_PREFIX: &str = &"!tac"; // Terms that are local to a tactic.

#[derive(Clone, Debug)]
pub struct Derivation {
    pub context_: Context,
    next_id: usize,
    inhabited_types: HashMap<Arc<Term>, Vec<String>>,
    existing_values: HashMap<Arc<Term>, String>,
}

// Returns whether the string contains a valid `real` constant.
// For now, we only handle rationals in built-in operations.
// In the future, we'll likely get rid of builtin `eval` and this will no longer exist.
fn is_real_const(s: &str) -> bool {
    s.parse::<Rational64>().is_ok()
}

// Returns true if the argument satisfies the argument expression.
fn argument_satisfies(arg: &str, arg_expr: &Option<String>) -> bool {
    match arg_expr {
        None => true,
        Some(e) => {
            match e.split_once('@') {
                Some((name, loc)) => {
                    if loc == "*" {
                        arg.starts_with(&format!("{}@", name))
                    } else {
                        arg == e
                    }
                },
                None => { arg == e }
            }
        }
    }
}

impl Derivation {
    pub fn get_type_constant(&self) -> &Arc<Term> {
        self.context().get_type_constant()
    }

    pub fn get_prop_constant(&self) -> &Arc<Term> {
        self.context().get_prop_constant()
    }

    pub fn incorporate(&mut self, context: &Context) {
        for name in context.insertion_order.iter() {
            if let Some(def) = context.lookup(name) {
                self.define(name.clone(), def.clone(), false);
            }
        }

        for proof in context.proofs.iter() {
            self.context_mut().add_proof(proof.clone());
        }

        for annotation in context.annotations.iter() {
            Arc::make_mut(&mut self.context_mut().annotations).push(annotation.clone());
        }
    }

    pub fn actions(&self) -> Iter<'_, String> {
        self.context().actions()
    }

    pub fn proofs(&self) -> ProofResultNames {
        self.context().proofs()
    }

    pub fn execute_proof(&self, name: &String) -> Result<(), ProofError> {
        for v in self.context().proofs.iter() {
            if v.name() == name {
                return v.execute(&mut self.clone());
            }
        }
        Err(ProofError::ProofNotFound(name.clone()))
    }

    pub fn set_goals(&mut self, goals: Vec<Arc<Term>>) {
        self.context_.goals = goals;
    }

    pub fn dump_context(&self) -> String {
        self.context().to_string()
    }

    pub fn new() -> Derivation {
        Derivation {
            context_: Context::new_with_builtins(&["eval", "rewrite", "eq_symm", "eq_refl"]),
            next_id: 0,
            inhabited_types: HashMap::new(),
            existing_values: HashMap::new(),
        }
    }

    pub fn size(&self) -> usize {
        self.context_.insertion_order.len()
    }

    pub fn next_term_id(&mut self) -> usize {
        self.next_id += 1;
        self.next_id
    }

    pub fn fast_forward_next_term_id(&mut self, i: usize) {
        if i > self.next_id {
            self.next_id = i;
        }
    }

    pub fn peek_next_term_id(&self) -> usize {
        self.next_id
    }

    pub fn lookup(&self, name: &String) -> Option<&Definition> {
        self.context_.lookup(name)
    }

    fn apply_builtin_eval(&self, new_terms: &mut Vec<Definition>, args: &Vec<Option<String>>,
                          scope: &Option<Scope>) {

        for eq_name in self.context_.insertion_order.iter() {
            if !out_of_scope(eq_name, scope) && argument_satisfies(eq_name, args.get(0).unwrap_or(&None)) {
                if let Some(def) = self.context_.lookup(eq_name) {
                    self.apply_builtin_eval_with(&eq_name, def, new_terms);
                }
            }
        }
    }

    fn apply_builtin_eq_refl(&self, new_terms: &mut Vec<Definition>, args: &Vec<Option<String>>,
                             scope: &Option<Scope>) {
        let mut seen_before = HashSet::new();

        for name in self.context_.insertion_order.iter() {
            if !out_of_scope(name, scope) && argument_satisfies(name, args.get(0).unwrap_or(&None)) {
                let val = Term::Atom { name: name.clone() }.rc().eval(&self.context_);
                if seen_before.insert(val) {
                    let def = self.context_.lookup(name).unwrap();
                    self.apply_builtin_eq_refl_with(name, def, new_terms);
                }
            }
        }
    }

    fn apply_builtin_eq_symm(&self, new_terms: &mut Vec<Definition>, args: &Vec<Option<String>>,
                             scope: &Option<Scope>) {
        for name in self.context_.insertion_order.iter() {
            if !out_of_scope(name, scope) && argument_satisfies(name, args.get(0).unwrap_or(&None)) {
                let def = self.context_.lookup(name).unwrap();
                self.apply_builtin_eq_symm_with(name, def, new_terms);
            }
        }
    }

    fn apply_builtin_rewrite(&self, new_terms: &mut Vec<Definition>, args: &Vec<Option<String>>,
                             scope: &Option<Scope>) {
        for name in self.context_.insertion_order.iter() {
            if out_of_scope(name, scope) || !argument_satisfies(name, args.get(0).unwrap_or(&None)) { continue; }

            let def = self.context_.lookup(name).unwrap();

            if let Some((t1, t2)) = def.dtype.extract_equality() {
                if t1 != t2 {
                    // NOTE: This might be avoided if we maintain the invariant that
                    // defined terms are already fully beta-reduced.
                    let t1 = t1.eval(&self.context_);
                    let t2 = t2.eval(&self.context_);

                    for prop_name in self.context_.insertion_order.iter() {
                        if out_of_scope(prop_name, scope) || !argument_satisfies(name, args.get(1).unwrap_or(&None)) { continue; }

                        let prop_def = self.context_.lookup(prop_name).unwrap();

                        if prop_def.is_prop(&self.context_) {
                            let prop_dtype = prop_def.dtype.eval(&self.context_);
                            self.rewrite_in(prop_name, &prop_dtype, &t1, &t2, name, new_terms);
                        }
                    }
                }
            }
        }
    }

    fn nondeterministically_apply_arrow(&self,
                                        arrow_object: &Arc<Term>,
                                        input_types: &Vec<Arc<Term>>,
                                        output_type: &Arc<Term>,
                                        inputs: &mut Vec<Arc<Term>>,
                                        predetermined: &Vec<Option<String>>,
                                        substitutions: &mut HashMap<String, String>,
                                        ghost_arguments: usize,
                                        scope: &Option<Scope>,
                                        results: &mut Vec<(Arc<Term>, Arc<Term>)>) {
        let next = inputs.len();

        // If we have filled up all arguments.
        if next == input_types.len() {
            results.push((
                Term::Application {
                    function: arrow_object.clone(),
                    arguments: inputs[ghost_arguments..].to_vec(),
                }.rc(),
                output_type.eval(&self.context_)));
            return;
        }

        // Otherwise, we pick the next argument.
        let (value_pattern, param_type) = match input_types[next].as_ref() {
            Term::PatternDeclaration { pattern, dtype } => (Some(pattern.clone()), dtype.clone()),
            Term::Declaration { name, dtype } => (Some(Term::Atom { name: substitutions.get(name).unwrap_or(name).clone() }
                                                       .rc().eval(&self.context_)),
                                                  dtype.clone()),
            _ => (None, input_types[next].clone()),
        };

        let mut seen_values = HashSet::new();

        for name in self.context_.insertion_order.iter() {
            if out_of_scope(name, scope) {
                continue;
            }

            if !argument_satisfies(name, predetermined.get(next).unwrap_or(&None)) {
                continue;
            }

            let def = self.context_.lookup(name).unwrap();
            let val_name = Term::Atom { name: name.clone() }.rc();
            let val = val_name.eval(&self.context_);

            if seen_values.contains(&val) {
                continue;
            }

            seen_values.insert(val.clone());

            let mut unifier = Unifier::new();

            // If this parameter has a value_pattern, def must have a value and unify with it.
            if let Some(p) = &value_pattern {
                if !p.unify_params(&val, &mut unifier) {
                    continue;
                }
            }


            if param_type.unify_params(&def.dtype, &mut unifier) {
                // `val` can be used as this argument. Make the necessary substitutions to
                // other parameter types (if any, i.e., if this is a dependent arrow) and
                // keep going.

                let mut remaining_types : Vec<Arc<Term>> = input_types.clone();
                let mut output_type = output_type.clone();

                for (name, value) in unifier.iter() {
                    match self.existing_values.get(value) {
                        Some(name_for_value) => {
                            substitutions.insert(name.clone(), name_for_value.clone());
                        },
                        None => {
                        }
                    }
                    for i in (inputs.len() + 1)..input_types.len() {
                        remaining_types[i] = remaining_types[i].replace(name, value);
                    }
                    output_type = output_type.replace(name, value);
                }

                inputs.push(val_name);

                self.nondeterministically_apply_arrow(
                    arrow_object, &remaining_types, &output_type, inputs, predetermined,
                    substitutions, ghost_arguments, scope, results);

                for (name, _value) in unifier.iter() {
                    substitutions.remove(name);
                }

                inputs.pop();
            }
        }
    }

    pub fn apply_with(&self, action: &String, param_name: &String) -> Vec<Definition> {
        let mut new_terms = Vec::new();

        match (self.context_.lookup(action), self.context_.lookup(param_name)) {
            (_, None) => { },
            (None, Some(def)) => {
                match action.as_str() {
                    "eval" => { self.apply_builtin_eval_with(param_name, def, &mut new_terms); }
                    "eq_refl" => { self.apply_builtin_eq_refl_with(param_name, def, &mut new_terms); }
                    "eq_symm" => { self.apply_builtin_eq_symm_with(param_name, def, &mut new_terms); }
                    "rewrite" => { self.apply_builtin_rewrite_with(param_name, def, &mut new_terms); }
                    _ => {}
                }
            },
            (Some(action_def), Some(def)) => {
                match action_def.dtype.as_ref() {
                    Term::Arrow { input_types, output_type } => {
                        // Try putting the given value in each of the parameter slots.
                        for (i, input_type) in input_types.iter().enumerate() {
                            let val = Term::Atom { name: param_name.clone() }.rc().eval(&self.context_);

                            let mut unifier = Unifier::new();

                            let (value_pattern, param_type) = match input_type.as_ref() {
                                Term::PatternDeclaration { pattern, dtype } => (Some(pattern.clone()), dtype.clone()),
                                _ => (None, input_type.clone())
                            };

                            // If this parameter has a value_pattern, def must have a value and unify with it.
                            if let Some(p) = &value_pattern {
                                if !p.unify_params(&val, &mut unifier) {
                                    continue;
                                }
                            }

                            if !param_type.unify_params(&def.dtype, &mut unifier) {
                                continue;
                            }

                            let mut fixed_params = Vec::new();
                            for (j, _t) in input_types.iter().enumerate() {
                                if i == j {
                                    fixed_params.push(Some(param_name.clone()));
                                } else {
                                    fixed_params.push(None);
                                }
                            }

                            let mut results = Vec::new();
                            self.nondeterministically_apply_arrow(
                                &Arc::new(Term::Atom { name: action.clone() }),
                                input_types,
                                output_type,
                                &mut Vec::new(),
                                &fixed_params,
                                &mut HashMap::new(),
                                0,
                                &None,
                                &mut results
                            );

                            for (r, t) in results.into_iter() {
                                new_terms.push(Definition { dtype: t,
                                                            value: Some(r), location: None });
                            }
                        }
                    },
                    _ => {}
                }
            },
        }

        new_terms
    }

    fn apply_builtin_eval_with(&self, obj_name: &String, def: &Definition, new_terms: &mut Vec<Definition>) {
        if def.is_prop(&self.context_) {
            return;
        }

        if let Some(val) = &def.value {
            /* Numeric evaluation */
            if let Term::Application { function, arguments } = val.as_ref() {
                if let Term::Atom { name } = &function.as_ref() {
                    if arguments.len() == 2 && (name == "+" || name == "-" ||
                                                name == "/" || name == "*") {
                        let lhs = arguments[0].to_string().parse();
                        let rhs = arguments[1].to_string().parse();

                        if let (Ok(n1), Ok(n2)) = (lhs, rhs) {
                            if let Some(result) = apply_builtin_binary_op(n1, n2, name) {
                                let eq_type = Arc::new(Term::Application {
                                    function: Arc::new(Term::Atom { name: String::from("=") }),
                                    arguments: vec![
                                        val.clone(),
                                        Arc::new(Term::Atom { name: result.to_string() }),
                                    ]
                                });

                                new_terms.push(Definition {
                                    dtype: eq_type,
                                    value: Some(Arc::new(Term::Application {
                                        function: Arc::new(Term::Atom { name: String::from("eval") }),
                                        arguments: vec![Arc::new(Term::Atom { name: obj_name.clone() })],
                                    })),
                                    location: None,
                                });
                            }
                        }
                    }
                }
            }

            /* Lambda evaluation */
            if !is_intrinsic_application(val) {
                let evaluated_term = val.eval(&self.context_);
                if evaluated_term != *val {
                    new_terms.push(Definition {
                        dtype: Arc::new(Term::Application {
                            function: Arc::new(Term::Atom { name: String::from("=") }),
                            arguments: vec![val.clone(), evaluated_term.clone()],
                        }),
                        value: Some(Arc::new(Term::Application {
                            function: Arc::new(Term::Atom { name: String::from("eval") }),
                            arguments: vec![Arc::new(Term::Atom { name: obj_name.clone() })],
                        })),
                        location: None,
                    });
                }
            }
        }
    }

    fn apply_builtin_eq_refl_with(&self, name: &String, def: &Definition, new_terms: &mut Vec<Definition>) {
        if def.is_prop(&self.context_) || def.is_type(&self.context_) || def.is_arrow(&self.context_) {
            return;
        }

        let val = match &def.value {
            Some(v) => v.clone(),
            None => Arc::new(Term::Atom { name: name.clone() })
        };

        let eq_type = Arc::new(Term::Application {
            function: Arc::new(Term::Atom { name: String::from("=") }),
            arguments: vec![val.clone(), val]
        });

        new_terms.push(Definition {
            dtype: eq_type,
            value: Some(Arc::new(Term::Application {
                function: Arc::new(Term::Atom { name: String::from("eq_refl") }),
                arguments: vec![Arc::new(Term::Atom { name: name.clone() })],
            })),
            location: None,
        });
    }

    fn apply_builtin_eq_symm_with(&self, name: &String, def: &Definition, new_terms: &mut Vec<Definition>) {
        if let Some((t1, t2)) = def.dtype.extract_equality() {
            if t1 == t2 {
                return;
            }

            let eq_type = Arc::new(Term::Application {
                function: Arc::new(Term::Atom { name: String::from("=") }),
                arguments: vec![t2, t1]
            });
            new_terms.push(Definition {
                dtype: eq_type,
                value: Some(Arc::new(Term::Application {
                    function: Arc::new(Term::Atom { name: String::from("eq_symm") }),
                    arguments: vec![Arc::new(Term::Atom { name: name.clone() })],
                })),
                location: None,
            });
        }
    }

    fn apply_builtin_rewrite_with(&self, name: &String, def: &Definition, new_terms: &mut Vec<Definition>) {
        // If def is an equality, try using it to rewrite in other props.
        if let Some((t1, t2)) = def.dtype.extract_equality() {
            if t1 != t2 {
                for prop_name in self.context_.insertion_order.iter() {
                    let prop_def = self.context_.lookup(prop_name).unwrap();
                    if prop_def.is_prop(&self.context_) {
                        self.rewrite_in(&prop_name, &prop_def.dtype, &t1, &t2, name, new_terms);
                    }
                }
            }
        }

        // If def is a prop, try using other equalities to rewrite it.
        if def.is_prop(&self.context_) {
            for eq_name in self.context_.insertion_order.iter() {
                let eq_def = self.context_.lookup(eq_name).unwrap();
                if let Some((t1, t2)) = eq_def.dtype.extract_equality() {
                    if t1 != t2 {
                        self.rewrite_in(&name, &def.dtype, &t1, &t2, eq_name, new_terms);
                    }
                }
            }
        }
    }

    fn rewrite_in(&self,
                  prop_name: &String,
                  prop_type: &Arc<Term>,
                  t1: &Arc<Term>,
                  t2: &Arc<Term>,
                  eq_name: &String,
                  new_terms: &mut Vec<Definition>) {
        for (rw, loc) in rewrite_all(&prop_type, &t1, &t2, String::new()).into_iter() {
            new_terms.push(
                Definition {
                    dtype: rw,
                    value: Some(Arc::new(Term::Application {
                        function: Arc::new(Term::Atom { name: String::from("rewrite") }),
                        arguments: vec![
                            Arc::new(Term::Atom { name: eq_name.clone() }),
                            Arc::new(Term::Atom { name: format!("{}@type{}", prop_name, loc) }),
                        ],
                    })),
                    location: None,
                }
            );
        }
    }

    // Returns whether there already exists an object in the context with the same value
    // (or same type, in case the type is a prop, because of proof irrelevance).
    pub fn is_redundant(&self, dtype: &Arc<Term>, value: &Option<Arc<Term>>) -> bool {
        if dtype.is_prop(&self.context_) {
            // Proof irrelevance - check for anything with this same type.
            self.inhabited_types.contains_key(dtype)
        } else {
            match value {
                Some(val) => self.existing_values.contains_key(val),
                None => false,
            }
        }
    }

    pub fn define_subterms(&mut self, t: &Arc<Term>, is_root: bool,
                           subterm_names: &mut Vec<String>,
                           path: &mut Vec<String>) {
        let is_builtin_app = is_intrinsic_application(t);

        let is_real_atom = match t.as_ref() {
            Term::Atom { name } => {
                let real_type = Arc::new(Term::Atom { name: String::from(REAL_TYPE_CONST) });
                if is_real_const(name) && !self.is_redundant(&real_type, &Some(t.clone())) {
                    println!("DEPRECATED: atom {} being interpreted as rational literal", name);
                    self.existing_values.entry(t.clone()).or_insert_with(|| name.clone());
                    self.inhabited_types.entry(real_type.clone()).or_insert_with(Vec::new).push(name.clone());
                    self.context_.define(name.clone(),
                                         Definition { dtype: real_type,
                                                      value: None, location: None });
                    true
                } else {
                    false
                }
            },
            Term::Application { function, arguments } if !is_builtin_app => {
                path.push(String::from("0"));
                self.define_subterms(function, false, subterm_names, path);
                path.pop();

                for (i, t) in arguments.iter().enumerate() {
                    path.push((i+1).to_string());
                    self.define_subterms(t, false, subterm_names, path);
                    path.pop();
                }

                false
            },
            _ => false,
        };

        if !is_real_atom && !is_builtin_app {
            let dname = path.join(PATH_EXPR_SEPARATOR);
            self.existing_values.entry(t.clone()).or_insert_with(|| dname.clone());

            if !is_root {
                let dtype = t.get_type(&self.context_);
                self.inhabited_types.entry(dtype.clone()).or_insert_with(Vec::new).push(dname.clone());
                self.context_.define(dname.clone(),
                                     Definition { dtype,
                                                  value: Some(t.clone()), location: None });
                subterm_names.push(dname);
            }
        }
    }
}

impl Derivation {
    pub fn define(&mut self, name: String, def: Definition, rename: bool) -> Vec<String> {
        let name = if rename {
            format!("{}{}", name, self.next_term_id())
        } else {
            name
        };

        if cfg!(debug_assertions) {
            println!("define {} : {}{}", name, &def.dtype, match &def.value {
                Some(v) => format!(" = {}", v),
                None => String::new(),
            });
        }

        let mut subterm_names = vec![];

        self.define_subterms(&def.dtype, false, &mut subterm_names, &mut vec![name.clone(), String::from("type")]);

        if let Some(value) = &def.value {
            self.define_subterms(&value.eval(&self.context_), true, &mut subterm_names, &mut vec![name.clone()]);
            self.existing_values.entry(value.clone()).or_insert_with(|| name.clone());
        }

        self.existing_values.entry(Term::Atom { name: name.clone() }.rc()).or_insert_with(|| name.clone());
        self.inhabited_types.entry(def.dtype.clone()).or_insert_with(Vec::new).push(name.clone());

        self.context_.define(name, def);

        subterm_names
    }

    pub fn incorporate_definitions(&mut self, defs: &Vec<Definition>, name_prefix: &str) {
        for d in defs.iter() {
            self.define(name_prefix.to_string(), d.clone(), true);
        }
    }

    // Applies an action and checks whether it constructs the target object.
    // If it does, adds that object to the universe, returning Ok.
    // Otherwise, returns an Err with all the objects that were constructed by the action.
    pub fn construct_by(&mut self, action: &String, target: &Term) -> Result<(), Vec<Definition>> {
        let results = self.application_results(action, &None, &vec![]);

        for def in results.iter() {
            if let Some(value) = &def.value {
                if target == value.as_ref() {
                    self.define(format!("r_{}_", action), def.clone(), true);
                    return Ok(())
                }
            }
        }

        Err(results)
    }

    // Applies an action and checks whether it constructs an object of the target type (typically a prop).
    // If it does, adds that object to the universe, returning Ok.
    // Otherwise, returns an Err with all the objects that were constructed by the action.
    pub fn show_by(&mut self, action: &String, target_type: &Term) -> Result<(), Vec<Definition>> {
        let results = self.application_results(action, &None, &vec![]);
        let target_type = Arc::new(target_type.clone());
        let target_type_e = target_type.eval(&self.context_);

        for def in results.iter() {
            if target_type_e == def.dtype.eval(&self.context_) {
                self.define(format!("r_{}_", action), def.clone(), true);
                return Ok(())
            }
        }

        Err(results)
    }

    // Applies an action with all possible distinct arguments.
    // Returns a vector with all produced results.
    pub fn application_results(&self, action: &String,
                               scope: &Option<Scope>,
                               predetermined: &Vec<Option<String>>) -> Vec<Definition> {
        self.application_results_with_preconditions(action, scope, &vec![], predetermined)
    }

    // Applies an action with all possible distinct arguments.
    // For each of the preconditions, we first find arguments that satisfy
    // those, and then enumerate ways to fill in the arrow's formal parameters.
    // Returns a vector with all generated results.
    pub fn application_results_with_preconditions(
        &self, action: &String,
        scope: &Option<Scope>,
        preconditions: &Vec<Arc<Term>>,
        predetermined: &Vec<Option<String>>) -> Vec<Definition> {
        let mut new_terms = Vec::new();

        match self.context_.lookup(action) {
            None => {
                match action.as_str() {
                    "eval" => { self.apply_builtin_eval(&mut new_terms, predetermined, scope); }
                    "eq_refl" => { self.apply_builtin_eq_refl(&mut new_terms, predetermined, scope); }
                    "eq_symm" => { self.apply_builtin_eq_symm(&mut new_terms, predetermined, scope); }
                    "rewrite" => { self.apply_builtin_rewrite(&mut new_terms, predetermined, scope); }
                    _ => { println!("WARNING: No arrow {} in context.", action); }
                }
            },
            Some(action_def) => {
                if let Term::Arrow { input_types, output_type } = action_def.dtype.as_ref() {
                    let mut results = Vec::new();

                    // Augment input types with new PatternDeclarations corresponding to the preconditions.
                    let augmented_input_types = preconditions.iter().chain(input_types).cloned().collect();

                    self.nondeterministically_apply_arrow(
                        &Arc::new(Term::Atom { name: action.clone() }),
                        &augmented_input_types,
                        output_type,
                        &mut Vec::new(),
                        predetermined,
                        &mut HashMap::new(),
                        preconditions.len(),
                        scope,
                        &mut results,
                    );

                    for (r, t) in results.into_iter() {
                        new_terms.push(Definition { dtype: t,
                                                    value: Some(r), location: None });
                    }
                }
            },
        }

        new_terms
    }

    // Checks if a type is inhabited in the current context, i.e., if we have any object
    // of that type. For proof objects, this amounts to knowing whether we have a proof
    // of the corresponding proposition. If so, returns the name of an object of the given type.
    pub fn inhabited(&self, term_type: &Arc<Term>) -> Option<String> {
        for name in self.context_.insertion_order.iter() {
            if let Some(def) = self.context_.lookup(&name) {
                if &def.dtype == term_type {
                    return Some(name.clone())
                }
            }
        }
        None
    }

    pub fn context(&self) -> &Context {
        &self.context_
    }

    pub fn context_mut(&mut self) -> &mut Context {
        &mut self.context_
    }
}

fn apply_builtin_binary_op(n1: Rational64, n2: Rational64, op: &str) -> Option<Rational64> {
    match op {
        "+" => { Some(n1 + n2) },
        "-" => { Some(n1 - n2) },
        "*" => { Some(n1 * n2) },
        "/" if *n2.numer() != 0 => { Some(n1 / n2) },
        "/" => None,
        _ => panic!("Unknown builtin binary operator {}", op)
    }
}

// NOTE: This is a potentially conservative rewrite since we don't want to introduce occurrences
// of bound variables, so here we don't recurse into arrows or lambdas. This is not limiting for
// now, but something to think about for the future.
fn rewrite_all(term: &Arc<Term>, source: &Arc<Term>, target: &Arc<Term>,
               location: String) -> Vec<(Arc<Term>, String)> {
    let mut results = Vec::new();

    if term == source {
        results.push((target.clone(), location));
        return results;
    }

    if let Term::Application { function, arguments } = term.as_ref() {
        for (alt, loc) in rewrite_all(function, source, target, format!("{}@0", location)).into_iter() {
            results.push((Arc::new(Term::Application {
                function: alt,
                arguments: arguments.clone(),
            }), loc));
        }

        for i in 0..arguments.len() {
            for (alt, loc) in rewrite_all(&arguments[i], source, target,
                                          format!("{}@{}", location, i+1)).into_iter() {
                results.push((Arc::new(Term::Application {
                    function: function.clone(),
                    arguments: arguments[..i].iter()
                                             .chain(once(&alt))
                                             .chain(arguments[i+1..].iter())
                                             .cloned()
                                             .collect()
                }), loc));
            }
        }
    }

    results
}

fn out_of_scope(name: &str, scope: &Option<Scope>) -> bool {
    if name.starts_with(LOCAL_DEFINITION_PREFIX) {
        match scope {
            Some(s) => !s.contains(&String::from(name.split(PATH_EXPR_SEPARATOR)
                                                 .next().unwrap())),
            None => true,
        }
    } else {
        false
    }
}


#[cfg(test)]
pub mod tests {
    use crate::universe::{Derivation, Context, Term, Definition};
    use std::sync::Arc;
    use num_rational::Rational64;

    #[test]
    fn test_create_derivation() {
        let mut u = Derivation::new();

        let a = u.actions().collect::<Vec<&String>>();

        // Should have 'eval' and equality axioms.
        assert_eq!(a.len(), 4);

        u.define("nat".to_string(), Definition::new_opaque(u.get_type_constant().clone()), false);
        u.define("z".to_string(), Definition::new_opaque(Arc::new("nat".parse().unwrap())), false);
        u.define("s".to_string(), Definition::new_opaque(Arc::new("[nat -> nat]".parse().unwrap())), false);

        let a = u.actions().collect::<Vec<&String>>();
        assert_eq!(a.len(), 5);

        u.define("ss".to_string(), Definition::new_concrete(Arc::new("[nat -> nat]".parse().unwrap()),
                                                            Arc::new("lambda (n : nat) (s (s n))"
                                                                    .parse().unwrap())),
                 false);
        let a = u.actions().collect::<Vec<&String>>();
        assert_eq!(a.len(), 6);
    }

    #[test]
    fn test_simple_transitivity_proof() {
        let nat_theory: Context = "
        nat : type.
        z : nat.
        s : [nat -> nat].

        leq : [nat -> nat -> prop].

        leq_n_n : [('n : nat) -> (leq 'n 'n)].
        leq_s : [('n : nat) -> ('m : nat) -> (leq 'n 'm) -> (leq 'n (s 'm))].
        "
        .parse()
        .unwrap();
        let mut u = Derivation::new();
        u.incorporate(&nat_theory);

        assert!(u.construct_by(&"s".to_string(), &"(s z)".parse().unwrap()).is_ok());
        assert!(u.construct_by(&"s".to_string(), &"(s (s z))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"leq_n_n".to_string(), &"(leq z z)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"leq_s".to_string(), &"(leq z (s z))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"leq_s".to_string(), &"(leq z (s (s z)))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"leq_s".to_string(), &"(leq z (s (s (s z))))".parse().unwrap()).is_ok());
    }

    #[test]
    fn test_eval() {
        let real_theory: Context = "
        real : type.
        + : [real -> real -> real].
        * : [real -> real -> real].
        a : real = (+ 2 2).
        b : real = (* 2/3 9).
        "
        .parse()
        .unwrap();
        let mut u = Derivation::new();
        u.incorporate(&real_theory);

        assert!(u.show_by(&"eval".to_string(), &"(= (+ 2 2) 4)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"eval".to_string(), &"(= (* 2/3 9) 6)".parse().unwrap()).is_ok());
    }

    #[test]
    fn test_equation_solution() {
        let real_theory: Context = "
        real : type.

        = : [(t : type) -> t -> t -> type].
        + : [real -> real -> real].
        - : [real -> real -> real].
        * : [real -> real -> real].

        +_comm : [('a : real) -> ('b : real) -> (= (+ 'a 'b) (+ 'b 'a))].
        +-_assoc : [('a : real) -> ('b : real) -> ('c : real) -> (= (- (+ 'a 'b) 'c) (+ 'a (- 'b 'c)))].
        +0_id : [('a : real) -> (= (+ 'a 0) 'a)].

        x : real.
        y : real.

        x_eq : (= (+ x 3) 10).
        y_eq : (= y (* x x)).
        "
        .parse()
        .unwrap();

        let mut u = Derivation::new();
        u.incorporate(&real_theory);

        assert!(u.construct_by(&"-".to_string(), &"(- (+ x 3) 3)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"+-_assoc".to_string(), &"(= (- (+ x 3) 3) (+ x (- 3 3)))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"eval".to_string(), &"(= (- 3 3) 0)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= (- (+ x 3) 3) (+ x 0))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"+0_id".to_string(), &"(= (+ x 0) x)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= (- (+ x 3) 3) x)".parse().unwrap()).is_ok());
        assert!(u.construct_by(&"-".to_string(), &"(- 10 3)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"eq_refl".to_string(), &"(= (- (+ x 3) 3) (- (+ x 3) 3))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= x (- (+ x 3) 3))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= x (- 10 3))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"eval".to_string(), &"(= (- 10 3) 7)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= x 7)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= y (* 7 x))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= y (* 7 7))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"eval".to_string(), &"(= (* 7 7) 49)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= y 49)".parse().unwrap()).is_ok());
    }

    #[test]
    fn test_equation_solution_with_pattern_declarations() {
        let real_theory: Context = "
        real : type.

        = : [(t : type) -> t -> t -> type].
        + : [real -> real -> real].
        - : [real -> real -> real].
        * : [real -> real -> real].

        +_comm : [((+ 'a 'b) : real) -> (= (+ 'a 'b) (+ 'b 'a))].
        +-_assoc : [((- (+ 'a 'b) 'c) : real) -> (= (- (+ 'a 'b) 'c) (+ 'a (- 'b 'c)))].
        +0_id : [((+ 'a 0) : real) -> (= (+ 'a 0) 'a)].

        x : real.
        y : real.

        x_eq : (= (+ x 3) 10).
        y_eq : (= y (* x x)).
        "
        .parse()
        .unwrap();

        let mut u = Derivation::new();
        u.incorporate(&real_theory);

        assert!(u.construct_by(&"-".to_string(), &"(- (+ x 3) 3)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"+-_assoc".to_string(), &"(= (- (+ x 3) 3) (+ x (- 3 3)))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"eval".to_string(), &"(= (- 3 3) 0)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= (- (+ x 3) 3) (+ x 0))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"+0_id".to_string(), &"(= (+ x 0) x)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= (- (+ x 3) 3) x)".parse().unwrap()).is_ok());
        assert!(u.construct_by(&"-".to_string(), &"(- 10 3)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"eq_refl".to_string(), &"(= (- (+ x 3) 3) (- (+ x 3) 3))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= x (- (+ x 3) 3))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= x (- 10 3))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"eval".to_string(), &"(= (- 10 3) 7)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= x 7)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= y (* 7 x))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= y (* 7 7))".parse().unwrap()).is_ok());
        assert!(u.show_by(&"eval".to_string(), &"(= (* 7 7) 49)".parse().unwrap()).is_ok());
        assert!(u.show_by(&"rewrite".to_string(), &"(= y 49)".parse().unwrap()).is_ok());
    }

    #[test]
    fn test_arrow_with_pattern_declaration() {
        let real_theory: Context = "
        real : type.

        = : [('t : type) -> 't -> 't -> prop].
        + : [real -> real -> real].
        * : [real -> real -> real].

        /* This arrow can only be applied to an existing (+ 'a 0) term */
        +0_id : [((+ 'a 0) : real) -> (= (+ 'a 0) 'a)].

        x : real.
        y : real.

        x_eq : (= (+ (* 2 x) 0) 2).
        y_eq : (= y (* x x)).
        "
        .parse()
        .unwrap();

        let mut u = Derivation::new();
        u.incorporate(&real_theory);

        // This should work.
        assert!(u.show_by(&"+0_id".to_string(), &"(= (+ (* 2 x) 0) (* 2 x))".parse().unwrap()).is_ok());
        // This should not - there's no (+ x 0) anywhere!
        assert!(u.show_by(&"+0_id".to_string(), &"(= (+ x 0) x)".parse().unwrap()).is_err());
        // Nor any (+ (* 2 y) 0) anywhere.
        assert!(u.show_by(&"+0_id".to_string(), &"(= (+ (* 2 y) 0) (* 2 y))".parse().unwrap()).is_err());

    }

    #[test]
    fn test_apply_with() {
        let real_theory: Context = "
        real : type.

        = : [('t : type) -> 't -> 't -> prop].
        + : [real -> real -> real].

        +0_id : [((+ 'a 0) : real) -> (= (+ 'a 0) 'a)].

        let yes : real = (+ (+ 1 2) 0). /* Arrow applies. */
        let no : real = (+ 2 3). /* Arrow does not apply. */
        "
        .parse()
        .unwrap();

        let mut u = Derivation::new();
        u.incorporate(&real_theory);

        // This should work.
        assert_eq!(u.apply_with(&"+0_id".to_string(), &"yes".to_string()).len(), 1);
        assert_eq!(u.apply_with(&"+0_id".to_string(), &"no".to_string()).len(), 0);
    }

    #[test]
    fn test_exists_elim() {
        let context : Context = concat!(
            "nat : type.",
            "+ : [nat -> nat -> nat].",
            "exists : [('t : type) -> ('p : ['t -> prop]) -> prop].",
            "ex_wit : [('t : type) -> ('p : ['t -> prop]) -> (exists 't 'p) -> 't].",
            "ex_elim : [('t : type) -> ('p : ['t -> prop]) -> ('e : (exists 't 'p)) -> ('p (ex_wit 't 'p 'e))].",
            "x : nat. x0 : nat. x1 : (exists nat (lambda ('c : nat) (= (+ x 'c) x0))).")
            .parse().unwrap();

        let mut u = Derivation::new();
        u.incorporate(&context);

        let results = u.application_results_with_preconditions(
            &"ex_elim".to_string(), &None,
            &vec![Term::PatternDeclaration {
                pattern: "'e".parse::<Term>().unwrap().rc(),
                dtype: "(exists 't 'p)".parse::<Term>().unwrap().rc(),
            }.rc()],
            &vec![]);

        assert_eq!(results.len(), 1);
    }
}

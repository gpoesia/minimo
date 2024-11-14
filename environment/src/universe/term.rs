use std::sync::Arc;
use std::vec::Vec;
use std::borrow::BorrowMut;
use std::collections::{HashMap, HashSet};
use std::collections::hash_set::Iter;
use std::fmt;
use std::fs;
use std::path::Path;
use std::iter::{Filter, Map, once};
use core::str::FromStr;
use itertools::Itertools;

use pest::Parser;
use pest::iterators::Pair;
use pest::error::{Error as PestError, ErrorVariant as PestErrorVariant};
use smallset::SmallSet;

use linear_map::{linear_map, LinearMap};

use crate::universe::proof::{Proof, ProofAction, parse_proof};

const TYPE: &str = "type";
const PROP: &str = "prop";

// Prefix added to the names of all lambda and arrow parameters.
// This is used to simplify the test of whether a term has free variables.
const PARAMETER_PREFIX: &str = "'";
pub type VarSet = SmallSet<[String; 5]>;
pub type Unifier = LinearMap<String, Arc<Term>>;
pub type TermLocation = Vec<usize>;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Location {
    pub file_name: Option<String>,
    pub line_number: Option<usize>,
}

#[derive(Clone, Debug)]
pub enum Annotation {
    ForwardAction { arrow: String, preconditions: Vec<Arc<Term>> },
    BackwardAction { arrow: String, must_infer: Vec<bool> },
}

#[derive(Clone, Debug)]
pub struct Context {
    type_const: Arc<Term>, // The global constant `type` used to define other types.
    prop_const: Arc<Term>, // The global constant `prop,` which is a type used to define propositions.
    definitions: HashMap<String, Vec<Definition>>, // Map of names to definitions.
    pub insertion_order: Vec<String>, // Order in which definitions were added.
    arrows: HashSet<String>, // Set of global definitions that are arrows.

    pub goals: Vec<Arc<Term>>, // Set of open proof goals.

    pub(super) annotations: Arc<Vec<Annotation>>, // Set of open proof goals.
    pub(super) proofs: Arc<Vec<Proof>>, // List of proofs.
}

pub type ProofResultNames<'a> = Map<std::slice::Iter<'a, Proof>,
                                    fn(&Proof) -> &String>;


#[derive(Clone, Debug, PartialEq)]
pub struct Definition {
    pub dtype: Arc<Term>,
    pub value: Option<Arc<Term>>,
    pub location: Option<Location>
}

impl Definition {
    pub fn new_concrete(dtype: Arc<Term>, value: Arc<Term>) -> Definition {
        Definition { dtype, value: Some(value), location: None }
    }

    pub fn new_opaque(dtype: Arc<Term>) -> Definition {
        Definition { dtype, value: None, location: None }
    }

    pub fn is_prop(&self, ctx: &Context) -> bool {
        &self.dtype.get_type(ctx) == ctx.get_prop_constant() || self.dtype.is_equality()
    }

    pub fn is_type(&self, ctx: &Context) -> bool {
        &self.dtype == ctx.get_type_constant()
    }

    pub fn is_arrow(&self, ctx: &Context) -> bool {
        self.dtype.is_arrow(ctx)
    }
}

#[derive(Parser)]
#[grammar = "universe/term.pest"]
pub(super) struct TermParser;

impl Context {
    pub fn new() -> Context {
        Context::new_with_builtins(&vec![])
    }

    pub fn new_with_builtins(builtin_arrows: &[&str]) -> Context {
        let type_const = Arc::new(Term::Atom { name: TYPE.to_string() });
        let prop_const = Arc::new(Term::Atom {name: PROP.to_string() });
        let type_const_def = Definition { dtype: type_const.clone(), value: None, location: None };
        let mut c = Context { definitions: HashMap::new(),
                              insertion_order: Vec::new(),
                              type_const,
                              prop_const,
                              arrows: HashSet::new(),
                              proofs: Vec::new().into(),
                              annotations: Vec::new().into(),
                              goals: Vec::new(),
                            };
        c.definitions.insert(TYPE.to_string(), vec![type_const_def.clone()]);
        c.definitions.insert(PROP.to_string(), vec![type_const_def]);

        c.insertion_order.push(PROP.to_string());
        builtin_arrows.iter().for_each(|v| { c.arrows.insert(String::from(*v)); });

        c
    }

    pub fn defining_term(&self, name: &String) -> Arc<Term> {
        if let Some(def) = self.lookup(name) {
            let dtype = def.dtype.eval(self);

            // Proof object - return the proposition.
            if dtype.is_prop(self) {
                return dtype;
            }

            // Regular object with a value - return the beta-reduced value.
            if let Some(val) = &def.value {
                return val.eval(self);
            }
        }

        // Opaque value - return the identifier itself.
        Term::Atom { name: name.clone() }.rc()
    }

    pub fn is_intrinsic_name(&self, name: &str) -> bool {
        name == TYPE || name == PROP
    }

    pub fn lookup(&self, name: &String) -> Option<&Definition> {
        if let Some(v) = self.definitions.get(name) {
            return v.last()
        }
        None
    }

    pub fn inhabitant(&self, ttype: &Arc<Term>) -> Option<&String> {
        for (k, v) in self.definitions.iter() {
            if let Some(def) = v.last() {
                if def.dtype.eval(self) == ttype.eval(self) {
                    return Some(k)
                }
            }
        }
        None
    }

    pub fn inhabitants(&self, ttype: &Arc<Term>) -> Vec<String> {
        let ttype = ttype.eval(self);
        let mut seen_before = HashSet::<Arc<Term>>::new();

        self.definitions.iter().filter_map(|(k, v)| {
            if let Some(def) = v.last() {
                let val = def.dtype.eval(self);
                let defining_val = self.defining_term(k);

                if val == ttype {
                    if !seen_before.contains(&defining_val) {
                        seen_before.insert(defining_val);
                        Some(k.clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }).collect()
    }

    pub fn define_push(&mut self, name: String, def: Definition) {
        if let Term::Arrow { input_types: _, output_type: _ } = def.dtype.as_ref() {
            self.arrows.insert(name.clone());
        }

        if let Some(v) = self.definitions.get_mut(&name) {
            v.push(def);
        } else {
            self.insertion_order.push(name.clone());
            self.definitions.insert(name, vec!(def));
        }
    }

    pub fn define(&mut self, name: String, def: Definition) {
        if let Term::Arrow { input_types: _, output_type: _ } = def.dtype.as_ref() {
            self.arrows.insert(name.clone());
        }

        if let Some(v) = self.definitions.get_mut(&name) {
            let idx = v.len() - 1;
            v[idx] = def;
        } else {
            self.insertion_order.push(name.clone());
            self.definitions.insert(name, vec!(def));
        }
    }

    pub fn add_proof(&mut self, proof: Proof) {
        if let Some(prop) = &proof.prop {
            self.define(proof.name.clone(), Definition::new_opaque(prop.clone()));
        }

        Arc::make_mut(&mut self.proofs).push(proof);
    }

    pub fn incorporate(&mut self, ctx: Context) {
        for name in ctx.insertion_order.iter() {
            if let Some(def) = ctx.lookup(name) {
                self.define(name.clone(), def.clone());
            }
        }

        for proof in ctx.proofs.iter() {
            self.add_proof(proof.clone());
        }

        for annotation in ctx.annotations.iter() {
            Arc::make_mut(&mut self.annotations).push(annotation.clone());
        }

    }

    pub fn proofs(&self) -> ProofResultNames<'_> {
        self.proofs.iter().map(Proof::name)
    }

    // Sets a new value to a previously defined name.
    // FIXME This should not change its type, although that is not checked here.
    pub fn set(&mut self, name: &String, value: Arc<Term>) {
        if let Some(v) = self.definitions.get_mut(name) {
            let idx = v.len() - 1;
            v[idx].value = Some(value);
        }
    }

    pub fn actions(&self) -> Iter<'_, String> {
        self.arrows.iter()
    }

    pub fn destroy(&mut self, name: &String) {
        self.definitions.remove(name);
    }

    pub fn with_goals(&self, new_goals: Vec<Arc<Term>>) -> Context {
        Context { goals: new_goals, ..self.clone() }
    }

    pub fn set_goals(&mut self, new_goals: Vec<Arc<Term>>) {
        self.goals = new_goals;
    }

    // Removes objects from insertion_order that have been destroied, to speed-up iteration.
    pub fn rebuild(&mut self) {
        self.insertion_order = self.insertion_order
                                   .drain(0..)
                                   .filter(|p| self.definitions.contains_key(p))
                                   .collect();
    }

    pub fn get_type_constant(&self) -> &Arc<Term> {
        &self.type_const
    }

    pub fn get_prop_constant(&self) -> &Arc<Term> {
        &self.prop_const
    }

    pub fn size(&self) -> usize {
        self.definitions.len()
    }

    pub fn get_fresh_name(&self, prefix: &String) -> String {
        let mut name = prefix.clone();
        let mut i = 0;

        while self.definitions.get(&name).is_some() {
            name = format!("{}{}", prefix, i);
            i += 1;
        }

        name
    }

    // Tests alpha-beta equivalency (term equality modulo evaluation and renaming of bound variables).
    pub fn are_equivalent(&self, t1: &Arc<Term>, t2: &Arc<Term>) -> bool {
        alpha_equivalent(&t1.eval(self), &t2.eval(self), &mut vec![])
    }

    pub fn lookup_forward_annotation(&self, arrow_name: &str) -> Option<Annotation> {
        for a in self.annotations.iter() {
            if let Annotation::ForwardAction { arrow, preconditions: _ } = &a {
                if arrow == arrow_name {
                    return Some(a.clone());
                }
            }
        }

        None
    }

    pub fn lookup_backward_annotation(&self, arrow_name: &str) -> Option<Annotation> {
        for a in self.annotations.iter() {
            if let Annotation::BackwardAction { arrow, must_infer: _ } = &a {
                if arrow == arrow_name {
                    return Some(a.clone());
                }
            }
        }

        None
    }
}

static mut IMPORT_STACK : Vec<String> = Vec::new();
static mut IMPORTED_SET : Vec<String> = Vec::new();

pub fn load_context(path: &str) -> Result<Context, String> {
    match fs::read_to_string(path) {
        Err(err) => {
            Err(err.to_string())
        },
        Ok(content) => {
            unsafe {
                IMPORT_STACK.clear();
                IMPORTED_SET.clear();

                let p = Path::new(path).canonicalize().unwrap();
                IMPORT_STACK.push(p.display().to_string());
            }
            match content.parse::<Context>() {
                Err(err) => {
                    Err(err.to_string())
                },
                Ok(ctx) => {
                    Ok(ctx)
                }
            }
        }
    }
}

impl FromStr for Context {
    type Err = PestError<Rule>;

    fn from_str(s : &str) -> Result<Context, PestError<Rule>> {
        unsafe {
            match IMPORT_STACK.last() {
                None => { IMPORT_STACK.push(".".to_string()); },
                Some(path) => { IMPORTED_SET.push(path.clone()); },
            }
        }

        let root = TermParser::parse(Rule::context, s)?.next().unwrap();
        let mut c = Context::new();
        let mut v: Vec<_> = root.into_inner().collect();
        for element in v.drain(0..) {
            let span = element.as_span();
            let line = span.start_pos().line_col().0;
            match element.as_rule() {
                Rule::definition => {
                    let (name, mut def) = parse_definition(element.into_inner().collect());
                    let loc = Location { line_number: Some(line), file_name: None};
                    def.location = Some(loc);
                    c.define(name, def);
                },
                Rule::verify | Rule::proof => {
                    let proof = parse_proof(element);
                    c.add_proof(proof);
                },
                Rule::forward => {
                    let mut children : Vec<Pair<Rule>> = element.into_inner().collect();
                    Arc::make_mut(&mut c.annotations).push(Annotation::ForwardAction {
                        arrow: children[0].as_str().to_string(),
                        preconditions: children.drain(1..)
                            .map(|r| parse_term(r, &mut HashMap::new()))
                            .collect()
                    });
                },
                Rule::backward => {
                    let children : Vec<Pair<Rule>> = element.into_inner().collect();
                    Arc::make_mut(&mut c.annotations).push(Annotation::BackwardAction {
                        arrow: children[0].as_str().to_string(),
                        must_infer: children[1..]
                            .iter()
                            .map(|r| r.as_rule() == Rule::INFER)
                            .collect()
                    });
                }
                Rule::import => {
                    let children : Vec<Pair<Rule>> = element.into_inner().collect();
                    let import_path = children[0].as_str();
                    let import_path = &import_path[1..import_path.len() - 1];
                    let complete_path = unsafe { Path::new(IMPORT_STACK.last().unwrap())
                                                 .with_file_name(import_path).display().to_string() };
                    let complete_path = Path::new(&complete_path);
                    if complete_path.is_file() {
                        match complete_path.canonicalize() {
                            Ok(canonical) => {
                                let p = canonical.display().to_string();
                                unsafe {
                                    if !IMPORTED_SET.contains(&p) {
                                        IMPORT_STACK.push(p.clone());
                                        if cfg!(debug_assertions) {
                                            println!("Loading {}", p);
                                        }
                                        let content = fs::read_to_string(p).unwrap();
                                        let ctx: Context = content.parse()?;
                                        IMPORT_STACK.pop();
                                        c.incorporate(ctx);
                                    }
                                }
                            },
                            Err(e) => {
                                return Err(PestError::<Rule>::new_from_span(
                                    PestErrorVariant::<Rule>::CustomError {
                                        message: format!("{} not found ({}).", complete_path.display(), e)
                                    },
                                    span))
                            },
                        }
                    }
                },
                Rule::EOI => { continue; },
                Rule::using => { continue; },
                r => unreachable!("Unhandled parse rule {:?}.", r),
            }
        }
        
        Ok(c)
    }
}

fn alpha_equivalent_sequences(it1: &mut dyn Iterator<Item=&Arc<Term>>,
                              it2: &mut dyn Iterator<Item=&Arc<Term>>,
                              renaming: &mut Vec<(String, String)>) -> bool {
    loop {
        match (it1.next(), it2.next()) {
            (Some(e1), Some(e2)) => {
                if !alpha_equivalent(e1, e2, renaming) {
                    return false;
                }
            },
            (None, None) => { return true },
            _ => { return false; }
        }
    }
}

fn alpha_equivalent(t1: &Arc<Term>, t2: &Arc<Term>, renaming: &mut Vec<(String, String)>) -> bool {
    match (t1.as_ref(), t2.as_ref()) {
        (Term::Atom { name: n1 },
         Term::Atom { name: n2 }) => {
            if is_parameter_name(n1) {
                for (from, to) in renaming.iter().rev() {
                    if from == n1 {
                        return to == n2;
                    }
                }
                false
            } else {
                n1 == n2
            }
        }
        (Term::Declaration { name: n1, dtype: dt1 },
         Term::Declaration { name: n2, dtype: dt2 }) => {
            if alpha_equivalent(dt1, dt2, renaming) {
                renaming.push((n1.clone(), n2.clone()));
                true
            } else {
                false
            }
        },
        (Term::Arrow { input_types: i1, output_type: o1},
         Term::Arrow { input_types: i2, output_type: o2}) => {
            let before = renaming.len();
            let answer = alpha_equivalent_sequences(&mut i1.iter().chain(once(o1)),
                                                    &mut i2.iter().chain(once(o2)),
                                                    renaming);
            renaming.truncate(before);
            answer
        },
        (Term::Lambda { parameters: p1, body: b1 },
         Term::Lambda { parameters: p2, body: b2 }) => {
            let before = renaming.len();
            let answer = alpha_equivalent_sequences(&mut p1.iter().chain(once(b1)),
                                                    &mut p2.iter().chain(once(b2)),
                                                    renaming);
            renaming.truncate(before);
            answer
        },
        (Term::Application { function: f1, arguments: a1 },
         Term::Application { function: f2, arguments: a2 }) => {
            alpha_equivalent(f1, f2, renaming) &&
                alpha_equivalent_sequences(&mut a1.iter(), &mut a2.iter(), renaming)
        },
        _ => false
    }
}

pub(super) fn parse_definition(mut sub: Vec<Pair<Rule>>) -> (String, Definition) {
    // A `definition` is either a named declaration or an "assume" declaration,
    // which is essentially an unnamed declaration of a proof object.
    if sub[0].as_rule() == Rule::assume {
        assert_eq!(sub.len(), 1, "'assume' definition branch has a single child (the prop term).");
        let name = format!("__pobj{}", sub[0].as_span().split().0.pos());
        let mut sub_children : Vec<Arc<Term>> = sub.remove(0).into_inner()
            .map(|p| parse_term(p, &mut HashMap::new()))
            .collect();
        assert_eq!(sub_children.len(), 1, "'assume' rule has a single child (the prop term).");
        (name, Definition { dtype: sub_children.remove(0), value: None, location: None })
    } else {
        // Regular (named) declaration).
        let mut children : Vec<Arc<Term>> = sub.drain(0..)
            .map(|p| parse_term(p, &mut HashMap::new()))
            .collect();
        let value = if children.len() == 2 { children.pop() } else { None };

        if let Term::Declaration { name, dtype } = children[0].as_ref() {
            let def = Definition { dtype: dtype.clone(), value: value, location: None };
            return (name.clone(), def);
        }
        unreachable!("First child of a definition must be a declaration");
    }
}

impl ToString for Context {
    fn to_string(&self) -> String {
        let mut s = String::new();

        s.push_str(format!("// {} definitions.\n", self.definitions.len()).as_str());

        for name in self.insertion_order.iter() {
            if let Some(def) = self.lookup(name) {
                s += &format!("{} : {}", name, def.dtype);

                if let Some(val) = &def.value {
                    s += &format!(" = {}", val);
                }

                s.push_str(".\n")
            }
        }
        s
    }
}


#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub enum Term {
    Declaration { name: String, dtype: Arc<Term> },
    PatternDeclaration { pattern: Arc<Term>, dtype: Arc<Term> },
    Atom { name: String },
    Arrow { input_types: Vec<Arc<Term>>, output_type: Arc<Term> },
    Lambda { parameters: Vec<Arc<Term>>, body: Arc<Term> },
    Application { function: Arc<Term>, arguments: Vec<Arc<Term>> },
}

fn rename_param_declarations(t: &mut Arc<Term>) -> VarSet {
    match t.clone().as_ref() {
        Term::Declaration { name, dtype } if !name.starts_with(PARAMETER_PREFIX) => {
            *t = Arc::new(Term::Declaration { name: format!("{}{}", PARAMETER_PREFIX, name),
                                             dtype: dtype.clone() });
            SmallSet::from_iter([name.clone()])
        },
        _ => { SmallSet::new() }
    }
}

pub(super) fn parse_term(pair: Pair<Rule>, decls: &mut HashMap<String, usize>) -> Arc<Term> {
    let rule = pair.as_rule();
    let s = pair.as_str();
    let mut sub : Vec<Pair<Rule>> = pair.into_inner().collect();

    match rule {
        Rule::lambda => {
            let mut params : Vec<Arc<Term>> = Vec::new();
            let mut param_names : Vec<String> = Vec::new();

            for s in sub.drain(0..sub.len() - 1) {
                let mut p = parse_term(s, decls);
                for name in rename_param_declarations(&mut p).iter() {
                    param_names.push(name.clone());
                    *decls.entry(name.clone()).or_insert(0) += 1;
                }
                params.push(p);
            }

            let body = parse_term(sub.pop().unwrap(), decls);

            // Append special prefix to all lambda parameters.
            let t = Arc::new(Term::Lambda {
                parameters: params,
                body: body,
            });

            for p in param_names {
                *decls.get_mut(&p).unwrap() -= 1;
            }

            t
        },
        Rule::declaration => {
            let mut children : Vec<Arc<Term>> = sub.drain(0..).map(|p| parse_term(p, decls)).collect();
            assert_eq!(children.len(), 2, "Declaration should have two children: pattern and type.");
            let dtype = children.pop().unwrap();
            let atom = children.pop().unwrap();
            if let Term::Atom { name } = Arc::try_unwrap(atom).unwrap() {
                Arc::new(Term::Declaration { name, dtype })
            } else {
                panic!("First child of a Declaration node should be an atom.")
            }
        },
        Rule::pattern_declaration => {
            let mut children : Vec<Arc<Term>> = sub.drain(0..).map(|p| parse_term(p, decls)).collect();
            assert_eq!(children.len(), 2, "Declaration should have two children: pattern and type.");
            let dtype = children.pop().unwrap();
            let pattern = children.pop().unwrap();
            Arc::new(Term::PatternDeclaration { pattern, dtype })
        },
        Rule::atom => {
            Arc::new(Term::Atom { name: format!("{}{}",
                                               if *decls.get(s).unwrap_or(&0) > 0 { PARAMETER_PREFIX }
                                               else { "" },
                                               s) })
        },
        Rule::arrow => {
            let mut input_types : Vec<Arc<Term>> = Vec::new();
            let mut param_names : Vec<String> = Vec::new();

            for s in sub.drain(0..sub.len() - 1) {
                let mut p = parse_term(s, decls);
                for name in rename_param_declarations(&mut p).iter() {
                    param_names.push(name.clone());
                    *decls.entry(name.clone()).or_insert(0) += 1;
                }
                input_types.push(p);
            }

            let output_type = parse_term(sub.pop().unwrap(), decls);

            for p in param_names {
                *decls.get_mut(&p).unwrap() -= 1;
            }

            Arc::new(Term::Arrow { input_types, output_type })
        },
        Rule::application => {
            let arguments : Vec<Arc<Term>> = sub.drain(1..).map(|p| parse_term(p, decls)).collect();
            let function = parse_term(sub.pop().unwrap(), decls);
            Arc::new(Term::Application { function, arguments })
        },
        _ => unreachable!(),
    }
}

impl<'a> Term {
    pub fn rc(&self) -> Arc<Term> {
        Arc::new(self.clone())
    }

    pub fn in_context(self: &'a Arc<Term>, context: &'a Context) -> TermInContext<'a> {
        TermInContext { term: self, context }
    }

    pub fn new_equality(lhs: Arc<Term>, rhs: Arc<Term>) -> Arc<Term> {
        Arc::new(
            Term::Application {
                function: Arc::new(Term::Atom { name: "=".to_string() }),
                arguments: vec![lhs, rhs]
            }
        )
    }

    pub fn is_prop(self: &Arc<Term>, ctx: &Context) -> bool {
        self.is_equality() || &self.get_type(ctx).get_type(ctx) == ctx.get_prop_constant()
    }

    pub fn is_arrow(self: &Arc<Term>, ctx: &Context) -> bool {
        matches!(self.eval(ctx).as_ref(),
                 Term::Arrow { input_types: _, output_type: _ })
    }

    pub fn free_variables(self: &Arc<Term>) -> VarSet {
        match self.as_ref() {
            Term::Declaration { name: _, dtype } => dtype.free_variables(),
            Term::PatternDeclaration { pattern, dtype } => {
                let mut s = pattern.free_variables();
                for p in dtype.free_variables().iter() {
                    s.insert(p.clone());
                }
                s
            },
            Term::Atom { name } => {
                if name.starts_with(PARAMETER_PREFIX) {
                    SmallSet::from_iter([name.clone()])
                } else {
                    SmallSet::new()
                }
            },
            Term::Application { function, arguments } => {
                let mut s = function.free_variables();
                for a in arguments {
                    for p in a.free_variables().iter() {
                        s.insert(p.clone());
                    }
                }
                s
            },
            Term::Arrow { input_types, output_type } => {
                let mut s = output_type.free_variables();
                for t in input_types {
                    if let Term::Declaration { name, dtype: _ } = t.as_ref() {
                        s.remove(name);
                    }
                }
                s
            },
            Term::Lambda { parameters, body } => {
                let mut s = body.free_variables();
                for t in parameters {
                    if let Term::Declaration { name, dtype: _ } = t.as_ref() {
                        s.remove(name);
                    }
                }
                s
            }
        }
    }

    pub fn free_atoms(self: &Arc<Term>) -> VarSet {
        match self.as_ref() {
            Term::Declaration { name: _, dtype } => dtype.free_atoms(),
            Term::PatternDeclaration { pattern, dtype } => {
                let mut s = pattern.free_variables();
                for p in dtype.free_variables().iter() {
                    s.insert(p.clone());
                }
                s
            },
            Term::Atom { name } => {
                SmallSet::from_iter([name.clone()])
            },
            Term::Application { function, arguments } => {
                let mut s = function.free_atoms();
                for a in arguments {
                    for p in a.free_atoms().iter() {
                        s.insert(p.clone());
                    }
                }
                s
            },
            Term::Arrow { input_types, output_type } => {
                let mut s = output_type.free_atoms();
                for t in input_types {
                    if let Term::Declaration { name, dtype: _ } = t.as_ref() {
                        s.remove(name);
                    }
                }
                s
            },
            Term::Lambda { parameters, body } => {
                let mut s = body.free_atoms();
                for t in parameters {
                    if let Term::Declaration { name, dtype: _ } = t.as_ref() {
                        s.remove(name);
                    }
                }
                s
            }
        }
    }

    pub fn get_type(self: &Arc<Term>, ctx: &Context) -> Arc<Term> {
        match self.as_ref() {
            Term::Declaration { name: _, dtype } => dtype.clone(),
            Term::PatternDeclaration { pattern: _, dtype } => dtype.clone(),
            Term::Atom { name } => {
                if let Some(def) = ctx.lookup(name) {
                    return def.dtype.clone();
                }
                panic!("'{}' undeclared", name)
            },
            Term::Arrow { input_types: it, output_type: ot } => {
                // An arrow type is a proposition type if its output_type is a proposition type.
                // Otherwise, it's a function, and it has type "type".
                let mut aug_ctx = ctx.clone();
                for t in it.iter() {
                    if let Term::Declaration { name, dtype } = t.as_ref() {
                        aug_ctx.define(name.clone(), Definition::new_opaque(dtype.clone()));
                    }
                }
                if &ot.eval(&aug_ctx).get_type(&aug_ctx) == ctx.get_prop_constant() {
                    ctx.get_prop_constant().clone()
                } else {
                    ctx.get_type_constant().clone()
                }
            },
            Term::Lambda { parameters, body } => {
                // NOTE(gpoesia): This is as inefficient as it can be right now since it clones
                // the entire context, but it's not a bottleneck for now (this case is quite rare).
                // The nicer long-term solution would be to have a way for contexts to have
                // an optional parent context, so that here we can create a sub-context where &ctx
                // is just pointed to. This might involve a small war with the borrow checker, or
                // standardize Context to also be reference-counted like Terms.
                let mut ctx2 = ctx.clone();

                for p in parameters.iter() {
                    match p.as_ref() {
                        Term::Declaration { name, dtype } => {
                            ctx2.define(name.clone(), Definition::new_opaque(dtype.clone()));
                        },
                        _ => panic!("lambda parameter is not a declaration.")
                    }
                }

                Arc::new(Term::Arrow {
                    input_types: parameters.iter().map(|p| p.get_type(&ctx2)).collect(),
                    output_type: body.get_type(&ctx2)
                })
            },
            Term::Application { function, arguments } => {
                // HACK: Intrinsic.
                if let Term::Atom { name } = function.as_ref() {
                    if name == "=" {
                        return ctx.get_prop_constant().clone();
                    }
                }

                match function.get_type(ctx).as_ref() {
                    Term::Arrow { input_types, output_type } => {
                        let mut input_types = input_types.clone();
                        let mut output_type = output_type.clone();

                        for (i, arg) in arguments.iter().enumerate() {
                            let (types_before, types_after) = input_types.split_at_mut(i+1);
                            let v_ctx = arg.eval(ctx);
                            let v_type = arg.get_type(ctx);

                            let (value_pattern, param_type) = match types_before[i].as_ref() {
                                Term::PatternDeclaration { pattern, dtype } =>
                                    (Some(pattern.clone()), dtype.clone()),
                                Term::Declaration { name, dtype } =>
                                    (Some(Term::Atom { name: name.clone() }.rc()), dtype.clone()),
                                _ => (None, types_before[i].clone()),
                            };

                            let mut unifier = Unifier::new();

                            if let Some(p) = &value_pattern {
                                if !p.unify_params(&v_ctx, &mut unifier) {
                                    panic!("Ill-typed term {}: value did not unify.", self);
                                }
                            }

                            if !param_type.unify_params(&v_type, &mut unifier) {
                                panic!("Ill-typed term {}: parameter type {} and value type {} did not unify.", self, param_type, v_type);
                            }

                            for (name, value) in unifier.iter() {
                                for j in 0..types_after.len() {
                                    types_after[j] = types_after[j].replace(name, value).eval(ctx);
                                }
                                output_type = output_type.replace(name, value).eval(ctx);
                            }
                        }

                        if arguments.len() == input_types.len() {
                            output_type
                        } else {
                            Arc::new(Term::Arrow { input_types, output_type })
                        }
                    },
                    _ => panic!("Ill-typed expression {}: applying arguments to a non-arrow.", self)
                }
            }
        }
    }

    pub fn eval(self: &Arc<Term>, ctx: &Context) -> Arc<Term> {
        match self.as_ref() {
            Term::Declaration { name, dtype } => {
                Arc::new(Term::Declaration { name: name.clone(),
                                            dtype: dtype.eval(ctx) })
            },
            Term::PatternDeclaration { pattern, dtype } => {
                Arc::new(Term::PatternDeclaration { pattern: pattern.eval(ctx),
                                                   dtype: dtype.eval(ctx) })
            },
            Term::Atom { name } => {
                if let Some(def) = ctx.lookup(name) {
                    match &def.value {
                        Some(value) if !is_intrinsic_application(value) => value.eval(ctx),
                        _ => { self.clone() },
                    }
                } else {
                    self.clone()
                }
            },
            Term::Arrow { input_types, output_type } => Term::Arrow {
                input_types: input_types.iter().map(|t| t.eval(ctx)).collect(),
                output_type: output_type.eval(ctx),
            }.rc(),
            Term::Lambda { parameters: _, body: _ } => self.clone(),
            Term::Application { function, arguments } => {
                let f = function.eval(ctx);

                if let Term::Lambda { parameters, body } = f.as_ref() {
                    let mut p = parameters.clone();
                    let mut b = body.clone();

                    for (i, a) in arguments.iter().enumerate() {
                        if let Term::Declaration { name, dtype: _ } = parameters[i].as_ref() {
                            let arg = a.eval(ctx);
                            b = b.replace(name, &arg);

                            for j in (i+1)..parameters.len() {
                                p[j] = p[j].replace(name, &arg);
                            }
                        } else {
                            panic!("Lambda parameter should be a Term::Declaration")
                        }
                    }

                    let remaining = &p[arguments.len()..];
                    if !remaining.is_empty() {
                        return Arc::new(Term::Lambda { parameters: remaining.to_vec(), body: b });
                    }
                    return b;
                } else if let Term::Application { function, arguments: first_args } = f.as_ref() {
                    let mut v = first_args.clone();
                    v.append(&mut arguments.clone());
                    return Arc::new(Term::Application { function: function.clone(), arguments: v });
                }

                Arc::new(Term::Application {
                    function: function.clone(),
                    arguments: arguments.clone().iter().map(|v| v.eval(ctx)).collect()
                })
            }
        }
    }

    pub fn apply_unifier(self: &Arc<Term>, u: &Unifier) -> Arc<Term> {
        let mut t = self.clone();
        for (name, val) in u.iter() {
            t = t.replace(name, val);
        }
        t
    }

    pub fn replace(self: &Arc<Term>, r_name: &String, r_value: &Arc<Term>) -> Arc<Term> {
        match self.as_ref() {
            Term::Declaration { name, dtype } => {
                Arc::new(Term::Declaration {
                    name: if name == r_name {
                        r_value.unwrap_parameter_term().unwrap_or(name.clone())
                    } else {
                        name.clone()
                    },
                    dtype: dtype.replace(r_name, r_value),
                })
            },
            Term::PatternDeclaration { pattern, dtype } => {
                let self_params = self.free_variables();
                if self_params.contains(r_name) {
                    return self.clone()
                }
                Arc::new(Term::PatternDeclaration {
                    pattern: pattern.replace(r_name, r_value),
                    dtype: dtype.replace(r_name, r_value),
                })
            },
            Term::Atom { name } => {
                if name == r_name {
                    r_value.clone()
                } else {
                    self.clone()
                }
            },
            Term::Arrow { input_types, output_type } => {
                // If arrow parameters shadow the substitution, return unchanged.
                for p in input_types.iter() {
                    if let Term::Declaration { name, dtype: _, } = p.as_ref() {
                        if name == r_name {
                            return self.clone();
                        }
                    }
                }

                Arc::new(Term::Arrow {
                    input_types: input_types.clone().iter().map(|v| v.replace(r_name, r_value)).collect(),
                    output_type: output_type.replace(r_name, r_value),
                })
            },
            Term::Lambda { parameters, body } => {
                // If any lambda parameters shadow the substitution, then return self unchanged.
                for p in parameters.iter() {
                    if let Term::Declaration { name, dtype: _, } = p.as_ref() {
                        if name == r_name {
                            return self.clone()
                        }
                    }
                }
                // Otherwise, substitute in each declaration (r_name might occur in parameter types)
                // and in the body.
                let mut parameters = parameters.clone();
                for i in 0..parameters.len() {
                    parameters[i] = parameters[i].replace(r_name, r_value);
                }
                Arc::new(Term::Lambda { parameters, body: body.replace(r_name, r_value) })
            },
            Term::Application { function, arguments } => {
                Arc::new(Term::Application {
                    function: function.replace(r_name, r_value),
                    arguments: arguments.clone().iter().map(|a| a.replace(r_name, r_value)).collect()
                })
            },
        }
    }

    // Tries to unify the parameters (e.g., $a) in `self` with the concrete terms in `concrete`.
    // If succeeds, returns the unification map in `mapping`, and returns true. Otherwise,
    // returns false, and the partial mapping should be ignored.
    pub fn unify_params(self: &Arc<Term>, concrete: &Arc<Term>, mapping: &mut Unifier) -> bool {
        match (self.as_ref(), concrete.as_ref()) {
            // self is an atom which is a parameter name.
            (Term::Atom { name: pname }, t) if is_parameter_name(pname) => {
                match mapping.entry(pname.clone()) {
                    // If occupied, return whether t and the current value can be unified.
                    linear_map::Entry::Occupied(e) => { e.get().as_ref() == t },
                    // Otherwise, unify this parameter with the concrete value.
                    linear_map::Entry::Vacant(e) => { e.insert(concrete.clone()); true},
                }
            },
            // self is an atom which is not a parameter name; only unifies if they match.
            (Term::Atom { name: n1 }, Term::Atom { name: n2 }) => { n1 == n2 },
            // self is an application.
            (Term::Application { function: f1, arguments: a1 },
             Term::Application { function: f2, arguments: a2 }) => {
                if a1.len() != a2.len() || !f1.unify_params(f2, mapping) {
                    return false;
                }

                for (arg1, arg2) in a1.iter().zip(a2.iter()) {
                    if !arg1.unify_params(arg2, mapping) {
                        return false;
                    }
                }

                true
            },

            // self is an arrow.
            (Term::Arrow { input_types: i1, output_type: o1 },
             Term::Arrow { input_types: i2, output_type: o2 }) => {
                if i1.len() != i2.len() || !o1.unify_params(o2, mapping) {
                    return false;
                }

                for (t1, t2) in i1.iter().zip(i2.iter()) {
                    if !t1.unify_params(t2, mapping) {
                        return false;
                    }
                }

                true
            },
            _ => alpha_equivalent(self, concrete, &mut vec![]),
        }
    }

    fn unwrap_parameter_term(self: &Arc<Term>) -> Option<String> {
        match self.as_ref() {
            Term::Atom { name } if is_parameter_name(name) => { Some(name.clone()) }
            _ => None,
        }
    }

    pub fn ndunify(self: &Arc<Term>, concrete: &Arc<Term>, context: &mut Context)
                   -> Vec<Unifier> {

        match (self.as_ref(), concrete.as_ref()) {
            (Term::Atom { name: pname }, _) if is_parameter_name(pname) => {
                vec![linear_map!{pname.clone() => concrete.clone()}]
            },

            (Term::Declaration { name: pname, dtype: pdtype },
             Term::Declaration { name: cname, dtype: cdtype }) => {
                let mut dtype_unifiers = pdtype.ndunify(cdtype, context);
                context.define(cname.clone(), Definition::new_opaque(cdtype.clone()));

                dtype_unifiers.drain(0..).filter_map(|mut u| {
                    match u.entry(pname.clone()) {
                        linear_map::Entry::Occupied(e) => {
                            match e.get().as_ref() {
                                Term::Atom { name} if name == cname => { Some(u) }
                                _ => None
                            }
                        },
                        linear_map::Entry::Vacant(e) => {
                            e.insert(Term::Atom { name: cname.clone() }.rc());
                            Some(u)
                        }
                    }
                }).collect::<Vec<Unifier>>()
            },
            (Term::Arrow { input_types: ip, output_type: op },
             Term::Arrow { input_types: ic, output_type: oc }) => {
                if ip.len() > ic.len() {
                    // println!("More pattern inputs than concrete inputs - impossible.");
                    return vec![];
                }

                // println!("OK, {} pattern inputs and {} concrete inputs.", ip.len(), ic.len());

                let input_type_unifiers = ip[0].ndunify(&ic[0], context);

                // println!("{} unifiers for first input.", input_type_unifiers.len());

                let mut results = vec![];

                for u in input_type_unifiers.iter() {
                    let remaining_p = if ip.len() == 1 {
                        op.clone()
                    } else {
                        Term::Arrow { input_types: ip[1..].to_vec(),
                                      output_type: op.clone() }.rc()
                    };

                    let remaining_c = if ic.len() == 1 {
                        oc.clone()
                    } else {
                        Term::Arrow { input_types: ic[1..].to_vec(),
                                      output_type: oc.clone() }.rc()
                    };

                    let remaining_p = remaining_p.apply_unifier(u);

                    // println!("Trying to unify {} and {}", remaining_p, remaining_c);

                    results.extend(remaining_p.ndunify(&remaining_c, context).drain(0..).map(|mut v| {
                        v.extend(u.clone().drain());
                        v
                    }));
                }

                results
            },
            (Term::Application { function: pf, arguments: pa }, ct) => {
                match pf.unwrap_parameter_term() {
                    None => {
                        match ct {
                            Term::Application { function: cf, arguments: ca } => {
                                if pa.len() != ca.len() {
                                    return vec![];
                                }

                                let mut unifiers = pf.ndunify(cf, context);

                                for i in 0..pa.len() {
                                    let mut next_unifiers = vec![];

                                    for u in unifiers.iter() {
                                        let uarg = pa[i].apply_unifier(u);
                                        let mut nus = uarg.ndunify(&ca[i], context);

                                        for mut nu in nus.drain(0..) {
                                            nu.extend(u.clone().drain());
                                            next_unifiers.push(nu)
                                        }
                                    }

                                    unifiers = next_unifiers;
                                }

                                unifiers
                            },
                            _ => vec![],
                        }
                    },
                    Some(predicate_name) => {
                        // We have a flex-rigid equation: we need to synthesize
                        // a predicate, so we're in the higher-order unification case.
                        // This is the most important and subtle case of this function
                        // (and in the proof system kernel in general).
                        // Algorithm:
                        // 1- Find all occurrences of each of the flex-side arguments in ca.

                        // println!("Found a flex-rigid case.");

                        let mut abstractable_locations = Vec::<(usize, TermLocation)>::new();
                        let mut unifiers = vec![];

                        let mut param_terms = vec![];
                        let mut parameter_decls = vec![];
                        let mut param_set = VarSet::new();

                        for (i, a) in pa.iter().enumerate() {
                            abstractable_locations.extend(
                                concrete.find_all(a).drain(0..).map(|x| (i, x)));
                            // FIXME(gpoesia): should be a fresh name in the context?
                            let name = format!("{}{}", PARAMETER_PREFIX, i);
                            param_set.insert(name.clone());
                            param_terms.push(Term::Atom { name: name.clone() }.rc());

                            parameter_decls.push(Term::Declaration {
                                name,
                                dtype: pa[i].get_type(context),
                            }.rc());
                        }

                        // 2- For each subset of the occurrences:
                        for ss in vec![abstractable_locations].iter() { // .powerset() {
                            // 2a- Replace the chosen occurrences by a free parameter
                            let mut candidate = concrete.clone();

                            // println!("Candidate: substitute at {:?}", ss);

                            for (idx, loc) in ss {
                                // println!("Before {} {:?}: {}", idx, loc, candidate);
                                candidate = candidate.replace_at(&loc, &param_terms[*idx]);
                                // println!("After {} {:?}: {}", idx, loc, candidate);
                            }

                            let mut free_vars = candidate.free_variables();
                            for v in param_set.iter() {
                                free_vars.remove(v);
                            }

                            if free_vars.len() > 0 {
                                // println!("Has free variables: {:?}", free_vars);
                                continue;
                            }

                            // 2b- Lambda-close the resulting term and add a result for
                            //     `pf` to be the resulting lambda
                            let mut u = Unifier::new();
                            u.insert(predicate_name.clone(), Term::Lambda {
                                parameters: parameter_decls.clone(),
                                body: candidate,
                            }.rc());
                            unifiers.push(u);
                        }

                        // 3- Return all computed candidate lambdas.
                        unifiers
                    },
                }
            },
            (t1, t2) => {
                if t1 == t2 { vec![Unifier::new()] } else { vec![] }
            }
        }
    }

    pub fn is_equality(self: &Term) -> bool {
        if let Term::Application { function, arguments: _ } = &self {
            if let Term::Atom { name } = function.as_ref() {
                if name == "=" {
                    return true;
                }
            }
        }
        false
    }

    fn find_all(self: &Arc<Term>, target: &Arc<Term>) -> Vec<TermLocation> {
        if self == target {
            return vec![vec![]];
        }

        let mut results = vec![];

        match self.as_ref() {
            Term::Arrow { input_types, output_type } => {
                for i in 0..input_types.len() {
                    for mut v in input_types[i].find_all(target).drain(0..) {
                        v.push(i);
                        results.push(v);
                    }
                }
                for mut v in output_type.find_all(target).drain(0..) {
                    v.push(input_types.len());
                    results.push(v);
                }
            },
            Term::Lambda { parameters, body } => {
                for i in 0..parameters.len() {
                    for mut v in parameters[i].find_all(target).drain(0..) {
                        v.push(i);
                        results.push(v);
                    }
                }
                for mut v in body.find_all(target).drain(0..) {
                    v.push(parameters.len());
                    results.push(v);
                }
            },
            Term::Application { function, arguments } => {
                for mut v in function.find_all(target).drain(0..) {
                    v.push(0);
                    results.push(v);
                }

                for i in 0..arguments.len() {
                    for mut v in arguments[i].find_all(target).drain(0..) {
                        v.push(i + 1);
                        results.push(v);
                    }
                }
            },
            Term::Declaration { name: _, dtype } => {
                for mut v in dtype.find_all(target).drain(0..) {
                    v.push(1);
                    results.push(v);
                }
            },
            _ => {},
        }

        results
    }

    fn replace_at(self: &Arc<Term>, location: &[usize], target: &Arc<Term>) -> Arc<Term> {
        if location.len() == 0 {
            return target.clone();
        }

        let idx = location[location.len() - 1];
        let next_location = &location[0..location.len() - 1];

        match self.as_ref() {
            Term::Arrow { input_types, output_type } => {
                if idx == input_types.len() {
                    Term::Arrow { input_types: input_types.clone(),
                                  output_type: output_type.replace_at(next_location, target) }.rc()
                } else {
                    Term::Arrow { input_types: (input_types[0..idx].iter()
                                                .chain(once(
                                                    &input_types[idx].replace_at(next_location, target),
                                                ))
                                                .chain(input_types[(idx + 1)..].iter())
                                                .map(|x| x.clone()).collect()),
                                  output_type: output_type.clone() }.rc()
                }
            },
            Term::Lambda { parameters, body } => {
                if idx == parameters.len() {
                    Term::Lambda { parameters: parameters.clone(),
                                   body: body.replace_at(next_location, target) }.rc()
                } else {
                    Term::Lambda { parameters: (parameters[0..idx]
                                                .iter()
                                                .chain(once(
                                                    &parameters[idx].replace_at(next_location, target),
                                                ))
                                                .chain(parameters[(idx + 1)..].iter())
                                                .map(|x| x.clone()).collect()),
                                   body: body.clone() }.rc()
                }
            },
            Term::Application { function, arguments } => {
                if idx == 0 {
                    Term::Application { function: function.replace_at(next_location, target),
                                        arguments: arguments.clone() }.rc()
                } else {
                    Term::Application { function: function.clone(),
                                        arguments: (arguments[..idx - 1].iter()
                                                    .chain(once(
                                                        &arguments[idx - 1].replace_at(next_location, target),
                                                    ))
                                                    .chain(arguments[idx..].iter())
                                                    .map(|x| x.clone()).collect()) }.rc()
                }
            },
            Term::Declaration { name, dtype } => {
                Term::Declaration { name: name.clone(),
                                    dtype: dtype.replace_at(next_location, target) }.rc()
            },
            _ => { self.clone() },
        }
    }

    pub fn extract_equality(self: &Term) -> Option<(Arc<Term>, Arc<Term>)> {
        if let Term::Application { function, arguments } = &self {
            if let Term::Atom { name } = function.as_ref() {
                if name == "=" {
                    assert_eq!(arguments.len(), 2,
                               "Equality used as a non-binary relation.");
                    return Some((arguments[0].clone(), arguments[1].clone()));
                }
            }
        }
        None
    }

    pub fn make_equality_object(t1: Arc<Term>, t2: Arc<Term>) -> Arc<Term> {
        Arc::new(
            Term::Application {
                function: Arc::new(Term::Atom { name: "=".to_string() }),
                arguments: vec![t1.clone(), t2.clone()],
            })
    }

    pub fn fmt_in_context(self: &Arc<Term>, context: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.as_ref() {
            Term::Atom { name } => {
                if name.contains('@') {
                    if let Some(Definition { dtype: _, value: Some(value), location: None }) = context.lookup(&name) {
                        return value.fmt_in_context(context, f);
                    }
                }
                write!(f, "{}",
                       if name.starts_with(PARAMETER_PREFIX) { &name[0..] }
                       else { &name[0..] })
            },
            Term::Declaration { name, dtype } => {
                write!(f, "{} : ", if name.starts_with(PARAMETER_PREFIX) { &name[0..] }
                                   else { &name[..] })?;
                dtype.fmt_in_context(context, f)
            },
            Term::PatternDeclaration { pattern, dtype } => {
                pattern.fmt_in_context(context, f)?;
                write!(f, " : ")?;
                dtype.fmt_in_context(context, f)
            },
            Term::Arrow { input_types, output_type } => {
                write!(f, "[")?;
                for t in input_types.iter() {
                    match t.as_ref() {
                        Term::Declaration { name, dtype } => {
                            write!(f, "({} : ", &name[1..])?;
                            dtype.fmt_in_context(context, f)?;
                            write!(f, ") -> ")
                        },
                        _ => write!(f, "{} -> ", t),
                    }?;
                }
                output_type.fmt_in_context(context, f)?;
                write!(f, "]")
            },
            Term::Application { function, arguments } => {
                write!(f, "(")?;
                function.fmt_in_context(context, f)?;
                for a in arguments.iter() {
                    write!(f, " ")?;
                    a.fmt_in_context(context, f)?;
                }
                write!(f, ")")
            },
            Term::Lambda { parameters, body } => {
                write!(f, "lambda (")?;
                for (i, p) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    p.fmt_in_context(context, f)?;
                }
                write!(f, ") ")?;
                body.fmt_in_context(context, f)
            }
        }
    }

    // Expands a term in context by adding implicit arguments to applications.
    pub fn elaborate(self: &Arc<Term>, ctx: &Context) -> Arc<Term> {
        // Right now, the only implicit arguments are for the equality type, so that
        // is the only interesting case.
        match self.as_ref() {
            Term::Atom { name: _ } => self.clone(),
            Term::Declaration { name, dtype } => {
                Arc::new(Term::Declaration { name: name.clone(), dtype: dtype.elaborate(ctx) })
            },
            Term::PatternDeclaration { pattern, dtype } => {
                Arc::new(Term::PatternDeclaration { pattern: pattern.elaborate(ctx),
                                                   dtype: dtype.elaborate(ctx) })
            },
            Term::Arrow { input_types, output_type } => {
                // Iterates over the input types, and if any of them is a declaration,
                // adds to local context.
                let mut new_input_types = vec![];
                let mut new_context = ctx.clone();
                for t in input_types.iter() {
                    match t.as_ref() {
                        Term::Declaration { name, dtype } => {
                            new_input_types.push(
                                Arc::new(Term::Declaration { name: name.clone(),
                                                            dtype: dtype.elaborate(&new_context) }));
                            new_context.define(name.clone(), Definition::new_opaque(dtype.clone()));
                        },
                        _ => new_input_types.push(t.elaborate(ctx)),
                    }
                }
                Arc::new(Term::Arrow { input_types: new_input_types,
                                      output_type: output_type.elaborate(&new_context) })
            },
            Term::Application { function, arguments } => {
                // If function is equality, elaborate the first implicit argument.
                if let Term::Atom { name } = function.as_ref() {
                    if name == "=" {
                        return Arc::new(Term::Application {
                            function: function.clone(),
                            arguments: vec![arguments[0].get_type(ctx),
                                            arguments[0].clone(),
                                            arguments[1].clone()]});
                    }
                }
                // Otherwise, just elaborate the function and arguments.
                let elaborated_function = function.elaborate(ctx);
                let mut new_arguments = vec![];
                for a in arguments.iter() {
                    new_arguments.push(a.elaborate(ctx));
                }
                Arc::new(Term::Application { function: elaborated_function, arguments: new_arguments })
            },
            Term::Lambda { parameters, body } => {
                // Iterates over the parameters, and if any of them is a declaration,
                // adds to local context.
                let mut new_parameters = vec![];
                let mut new_context = ctx.clone();
                for p in parameters.iter() {
                    match p.as_ref() {
                        Term::Declaration { name, dtype } => {
                            new_parameters.push(
                                Arc::new(Term::Declaration { name: name.clone(),
                                                            dtype: dtype.elaborate(&new_context) }));
                            new_context.define(name.clone(), Definition::new_opaque(dtype.clone()));
                        },
                        _ => new_parameters.push(p.elaborate(ctx)),
                    }
                }
                Arc::new(Term::Lambda { parameters: new_parameters,
                                       body: body.elaborate(&new_context) })
            }
        }
    }

    // Removes implicit arguments from a term.
    pub fn contract(self: &Arc<Term>) -> Arc<Term> {
        // Right now, the only implicit arguments are for the equality type, so that
        // is the only interesting case.
        match self.as_ref() {
            Term::Atom { name: _ } => self.clone(),
            Term::Declaration { name, dtype } => {
                Arc::new(Term::Declaration { name: name.clone(), dtype: dtype.contract() })
            },
            Term::PatternDeclaration { pattern, dtype } => {
                Arc::new(Term::PatternDeclaration { pattern: pattern.contract(),
                                                   dtype: dtype.contract() })
            },
            Term::Arrow { input_types, output_type } => {
                Arc::new(Term::Arrow { input_types: input_types.iter().map(|t| t.contract()).collect(),
                                      output_type: output_type.contract() })
            },
            Term::Application { function, arguments } => {
                // If function is equality and the argument is explicit, remove the type argument.
                if let Term::Atom { name } = function.as_ref() {
                    if name == "=" && arguments.len() == 3 {
                        return Arc::new(Term::Application {
                            function: function.clone(),
                            arguments: vec![arguments[1].clone(),
                                            arguments[2].clone()]});
                    }
                }
                // Otherwise, just contract the function and arguments.
                Arc::new(Term::Application { function: function.contract(),
                                           arguments: arguments.iter().map(|a| a.contract()).collect() })
            },
            Term::Lambda { parameters, body } => {
                Arc::new(Term::Lambda { parameters: parameters.iter().map(|p| p.contract()).collect(),
                                       body: body.contract() })
            }
        }
    }
}

impl FromStr for Term {
    type Err = PestError<Rule>;

    fn from_str(s : &str) -> Result<Term, PestError<Rule>> {
        let root = TermParser::parse(Rule::term, s)?.next().unwrap();
        Ok(Arc::try_unwrap(parse_term(root, &mut HashMap::new())).unwrap())
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Atom { name } => write!(f, "{}", name),
            Term::Declaration { name, dtype } => write!(f, "{} : {}",
                                                        if name.starts_with(PARAMETER_PREFIX) { &name[0..] }
                                                        else { &name[..] },
                                                        dtype),
            Term::PatternDeclaration { pattern, dtype } => write!(f, "{} : {}", pattern, dtype),
            Term::Arrow { input_types, output_type } => {
                write!(f, "[")?;
                for t in input_types.iter() {
                    match t.as_ref() {
                        Term::Declaration { name, dtype } => write!(f, "({} : {}) -> ", &name[0..], dtype),
                        _ => write!(f, "{} -> ", t),
                    }?;
                }
                write!(f, "{}]", output_type)
            },
            Term::Application { function, arguments } => {
                write!(f, "({}", function)?;
                for a in arguments.iter() {
                    write!(f, " {}", a)?;
                }
                write!(f, ")")
            },
            Term::Lambda { parameters, body } => {
                write!(f, "(lambda (")?;
                for (i, p) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ") {})", body)
            }
        }
    }
}

pub struct TermInContext<'a> {
    term: &'a Arc<Term>,
    context: &'a Context,
}

impl<'a> fmt::Display for TermInContext<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.term.fmt_in_context(self.context, f)
    }
}

pub fn is_parameter_name(name: &str) -> bool {
    return name.starts_with(PARAMETER_PREFIX);
}

pub fn is_intrinsic_application(t: &Arc<Term>) -> bool {
    match t.as_ref() {
        Term::Application { function, arguments: _ } => {
            match function.as_ref() {
                Term::Atom { name } => {
                    name == "rewrite" || name == "eq_symm" || name == "eq_refl" || name == "eval"
                },
                _ => false
            }
        },
        _ => false
    }
}


pub mod tests {
    #![allow(unused_imports)]
    use std::sync::Arc;
    use crate::universe::term::{Context, Term, Definition, Unifier, alpha_equivalent};
    use crate::universe::{VarSet};

    #[test]
    fn build_context() {
        let mut c = Context::new();

        let atom = Arc::new(Term::Atom { name: "asdf".to_string() });
        let def = Definition::new_opaque(atom);

        c.define("x".to_string(), def.clone());
        assert_eq!(c.lookup(&"x".to_string()), Some(&def));
        assert_eq!(c.lookup(&"y".to_string()), None);
    }

    #[test]
    fn parse_and_format_terms() {
        let tests = [
            &"x",
            &"(s n)",
            &"(lambda ('n : nat, 'f : [nat -> nat -> nat]) ('f 'n ('f (s 'n) (s 'n))))",
            &"(lambda ('n : nat, 'f : [nat -> [nat -> prop] -> prop]) ('f 'n (lambda ('k : nat) (is_odd 'k))))",
        ];
        for &s in tests {
            let result: Result<Term, _> = s.parse();
            assert!(result.is_ok());
            let s2 = format!("{}", result.unwrap());
            assert_eq!(s, s2.as_str());
        }
    }

    #[test]
    fn parse_nat_theory() {
        let result : Result<Context, _> = include_str!("../../theories/nats.p").parse();
        println!("Result: {:#?}", result.as_ref().err());
        assert!(result.is_ok());
    }

    #[test]
    fn parse_simple_context() {
        let result: Result<Context, _> = concat!("nat : type. ",
                                                 "\n\n /* Some comment */ ",
                                                 "   leq : [nat -> nat -> /* hello */ prop]. ",
                                                 "leq_z : [nat -> prop] = (lambda (n : nat) (leq z n)).")
                                         .parse();
        assert!(result.is_ok());
        let context = result.unwrap();

        // 3 declared above, plus `type` and `prop`.
        assert_eq!(context.size(), 3 + 2);
        assert!(context.lookup(&"type".to_string()).is_some());

        assert!(context.lookup(&"nat".to_string()).is_some());
        assert!(context.lookup(&"nat".to_string()).unwrap().value.is_none());

        assert!(context.lookup(&"leq".to_string()).is_some());
        assert!(context.lookup(&"leq".to_string()).unwrap().value.is_none());

        assert!(context.lookup(&"leq".to_string()).is_some());
        assert!(context.lookup(&"leq_z".to_string()).unwrap().value.is_some());

        assert!(context.lookup(&"other".to_string()).is_none());
    }

    #[test]
    fn unify() {
        let t1 = "nat".parse::<Term>().unwrap().rc();
        let t2 = "real".parse::<Term>().unwrap().rc();

        assert!(!t1.unify_params(&t2, &mut Unifier::new()));
        assert!(t1.unify_params(&t1, &mut Unifier::new()));
        assert!(t2.unify_params(&t2, &mut Unifier::new()));

        let t1 = "'b".parse::<Term>().unwrap().rc();
        let t2 = "(leq 1 2)".parse::<Term>().unwrap().rc();
        let mut u = Unifier::new();
        assert!(t1.unify_params(&t2, &mut u));
        assert_eq!(u.len(), 1);
        assert_eq!(u.get(&String::from("'b")), Some(&t2));

        let t1 = "(leq 'x 'y)".parse::<Term>().unwrap().rc();
        let t2 = "(leq 1 2)".parse::<Term>().unwrap().rc();
        let mut u = Unifier::new();
        assert!(t1.unify_params(&t2, &mut u));
        assert_eq!(u.len(), 2);
        assert_eq!(u.get(&String::from("'x")).unwrap().to_string(), String::from("1"));
        assert_eq!(u.get(&String::from("'y")).unwrap().to_string(), String::from("2"));

        let t1 = "(leq (+ 'x 'x) 'y)".parse::<Term>().unwrap().rc();
        let t2 = "(leq (+ 1 1) 2)".parse::<Term>().unwrap().rc();
        let mut u = Unifier::new();
        assert!(t1.unify_params(&t2, &mut u));
        assert_eq!(u.len(), 2);
        assert_eq!(u.get(&String::from("'x")).unwrap().to_string(), String::from("1"));
        assert_eq!(u.get(&String::from("'y")).unwrap().to_string(), String::from("2"));

        let t1 = "(leq (+ 'x 'x) 'x)".parse::<Term>().unwrap().rc();
        let t2 = "(leq (+ 1 1) 2)".parse::<Term>().unwrap().rc();
        let mut u = Unifier::new();
        assert!(!t1.unify_params(&t2, &mut u));

        let t1 = "(leq (+ 'x 'x) 'x)".parse::<Term>().unwrap().rc();
        let t2 = "(leq (+ (* a b) (* a b)) (* a b))".parse::<Term>().unwrap().rc();
        let mut u = Unifier::new();
        assert!(t1.unify_params(&t2, &mut u));
        assert_eq!(u.get(&String::from("'x")).unwrap().to_string(), String::from("(* a b)"));
    }

    #[test]
    fn ndunify() {
        let context : Context = concat!("nat : type. z : nat.",
                                        "   leq : [nat -> nat -> prop]. ",
                                        "leq_z : [nat -> prop] = (lambda (n : nat) (leq z n)).")
            .parse().unwrap();

        let t1 = "nat".parse::<Term>().unwrap().rc();
        let t2 = "real".parse::<Term>().unwrap().rc();

        assert_eq!(t1.ndunify(&t2, &mut context.clone()).len(), 0);

        let t1 = "nat".parse::<Term>().unwrap().rc();
        let t2 = "nat".parse::<Term>().unwrap().rc();
        assert_eq!(t1.ndunify(&t2, &mut context.clone()).len(), 1);

        let t1 = "(leq z z)".parse::<Term>().unwrap().rc();
        let t2 = "(leq z z)".parse::<Term>().unwrap().rc();
        assert_eq!(t1.ndunify(&t2, &mut context.clone()).len(), 1);

        let t1 = "[('a : nat) -> (leq z 'a)]".parse::<Term>().unwrap().rc();
        let t2 = "[('b : nat) -> (leq z 'b)]".parse::<Term>().unwrap().rc();
        let us = t1.ndunify(&t2, &mut context.clone());
        println!("us: {:#?}", us);
        assert_eq!(us.len(), 1);

        let t1 = "[('a : nat) -> ('p 'a)]".parse::<Term>().unwrap().rc();
        let t2 = "[('n : nat) -> (leq z 'n)]".parse::<Term>().unwrap().rc();
        let us = t1.ndunify(&t2, &mut context.clone());
        assert_eq!(us.len(), 1);

        let t1 = "('p z)".parse::<Term>().unwrap().rc();
        let t2 = "(leq z z)".parse::<Term>().unwrap().rc();
        let us = t1.ndunify(&t2, &mut context.clone());
        println!("higher-order unifiers: {:#?}", us);
        assert_eq!(t1.ndunify(&t2, &mut context.clone()).len(), 1);
        // Answer would be 4 if we want to exhaustively enumerate subsets of substitutions
        // (implemented but disabled).
    }

    #[test]
    fn ndunify_unequal() {
        let context : Context = concat!("nat : type. z : nat.",
                                        "add : [nat -> nat -> nat].")
            .parse().unwrap();

        let t1 = "[('n : nat) -> ('p 'n)]".parse::<Term>().unwrap().rc();
        let t2 = "[('m : nat) -> (= (add n 'm) (add 'm n)) -> (= (add n (s 'm)) (add (s 'm) n))]".parse::<Term>().unwrap().rc();

        let us = t1.ndunify(&t2, &mut context.clone());

        println!("First unifier: {}", t1.apply_unifier(&us[0]));
        /*
         println!("2 unifier: {}", t1.apply_unifier(&us[1]));
         println!("3 unifier: {}", t1.apply_unifier(&us[2]));
         println!("4 unifier: {}", t1.apply_unifier(&us[3]));
         */

        assert_eq!(us.len(), 1);
    }

    #[test]
    fn alpha_equivalency() {
        fn test(s1: &str, s2: &str, equiv: bool) {
            let t1 = s1.parse::<Term>().unwrap().rc();
            let t2 = s2.parse::<Term>().unwrap().rc();
            assert_eq!(alpha_equivalent(&t1, &t2, &mut vec![]), equiv);
        }

        test("[('n : nat) -> (leq 'n 'n)]", "[('a : nat) -> (leq 'a 'a)]", true);
        test("[('n : nat) -> ('m : nat) -> (leq 'n 'n)]", "[('a : nat) -> (leq 'a 'a)]", false);
        test("[('n : nat) -> (leq 'n 'n)]", "[('a : nat) -> (leq 'a 'z)]", false);
        test("[('n : nat) -> (leq 'n 'n)]", "[('a : nat) -> (geq 'a 'a)]", false);

        test("(lambda ('x : nat, 'y : nat) (leq 'x 'y))",
             "(lambda ('x : nat, 'y : nat) (leq 'x 'x))", false);

        test("(lambda ('x : nat, 'y : nat) (leq 'x 'y))",
             "(lambda ('y : nat, 'x : nat) (leq 'y 'x))", true);

        test("(lambda ('t : type, 'f : ['t -> 't], 'p : ['t -> prop], 'x : 't) ('p ('f 'x)))",
             "(lambda ('t : type, 'f : ['t -> 't], 'p : ['t -> prop], 'x : 't) ('p ('f 'x)))",
             true);

        test("(lambda ('t : type, 'f : ['t -> 't], 'p : ['t -> prop], 'x : 't) ('p ('f 'x)))",
             "(lambda ('f : type, 't : ['f -> 'f], 'p : ['f -> prop], 'x : 'f) ('p ('t 'x)))",
             true);

        test("(lambda ('t : type, 'f : ['t -> 't], 'p : ['t -> prop], 'x : 't) ('p ('f 'x)))",
             "(lambda ('t : type, 'f : ['t -> 't], 'p : ['t -> prop], 'x : 't) ('f ('p 'x)))",
             false);

        test("(lambda ('t : type, 'f : ['t -> 't], 'p : ['t -> prop], 'x : 't) ('p ('f 'x)))",
             "(lambda ('t : type, 'f : ['t -> 't], 'p : ['t -> prop], 'x : 't) (p (f 'x)))",
             false);
    }

    #[test]
    fn unify_arrow_with_type_of_lambda() {
        let context : Context = concat!(
            "nat : type.",
            "+ : [nat -> nat -> nat].",
            "exists : [('t : type) -> ('p : ['t -> prop]) -> prop].",
            "ex_elim : [('t : type) -> ('p : ['t -> prop]) -> ('e : (exists 't 'p)) -> ('p (ex_wit 't 'p 'e))].",
            "x : nat. x0 : nat.")
            .parse().unwrap();

        let t : Arc<Term> = "(lambda ('c : nat) (= (+ x 'c) x0))".parse::<Term>().unwrap().rc();
        let t2 : Arc<Term> = "['t -> prop]".parse::<Term>().unwrap().rc();

        let mut u = Unifier::new();
        assert!(t2.unify_params(&t.get_type(&context), &mut u));
        assert!(u.get("'t").unwrap() == &Term::Atom { name: "nat".to_string() }.rc());

    }

    #[test]
    fn test_elaborate() {
        let context : Context = concat!(
            "nat : type.\n",
            "int : type.\n",
            "n2i : [nat -> int].\n",
            "+ : [nat -> nat -> nat].\n",
            "= : [('t : type) -> 't -> 't -> prop].\n",
            "z : nat.\n",
            "s : [nat -> nat].\n")
            .parse().unwrap();

        let t : Arc<Term> = "[('a : nat) -> (= 'a 'a)]".parse::<Term>().unwrap().rc();
        assert_eq!(t.elaborate(&context).to_string(), "[('a : nat) -> (= nat 'a 'a)]");
        assert_eq!(t.elaborate(&context).contract().to_string(), t.to_string());

        let t : Arc<Term> = "(= (+ z z) z)".parse::<Term>().unwrap().rc();
        assert_eq!(t.elaborate(&context).to_string(), "(= nat (+ z z) z)");
        assert_eq!(t.elaborate(&context).contract().to_string(), t.to_string());

        let t : Arc<Term> = "(lambda ('x : nat) [('a : nat) -> (= (n2i 'a) (n2i 'x))])".parse::<Term>().unwrap().rc();
        assert_eq!(t.elaborate(&context).to_string(), "(lambda ('x : nat) [('a : nat) -> (= int (n2i 'a) (n2i 'x))])");
        assert_eq!(t.elaborate(&context).contract().to_string(), t.to_string());
    }
}
